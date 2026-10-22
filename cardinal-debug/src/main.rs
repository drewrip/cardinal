//! `cardinal-debug`: dump what cardinal tells Z3 about a query, and view it.

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use cardinal::Options;
use cardinal_debug::{Dump, Source, ascii, context, dump, foreign_key, html};
use clap::{Args, Parser, Subcommand};

#[derive(Parser)]
#[command(version, about = "Dump cardinal's Z3 constraints for a query and show why its bounds hold")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Analyze a query and write the dump as JSON.
    Dump {
        #[command(flatten)]
        input: Input,
        /// The JSON dump to write.
        #[arg(short, long)]
        output: PathBuf,
        /// Also write the constraints as an annotated SMT-LIB script.
        #[arg(long)]
        smt2: Option<PathBuf>,
    },
    /// Show a dump written by `dump`.
    View {
        /// The JSON dump.
        dump: PathBuf,
        #[command(flatten)]
        output: Output,
    },
    /// Analyze a query and show it, without writing a dump.
    Analyze {
        #[command(flatten)]
        input: Input,
        #[command(flatten)]
        output: Output,
        /// Also write the constraints as an annotated SMT-LIB script.
        #[arg(long)]
        smt2: Option<PathBuf>,
    },
}

#[derive(Args)]
struct Input {
    /// `CREATE TABLE` statements, separated by `;`, declaring the tables (and
    /// their primary keys).
    #[arg(long)]
    schema: PathBuf,
    /// A file with the SQL query (or, with --duckdb or --postgres, the SQL the
    /// plan is for).
    #[arg(long)]
    sql: Option<PathBuf>,
    /// The SQL query, inline.
    #[arg(long, conflicts_with = "sql")]
    query: Option<String>,
    /// Read DuckDB's `EXPLAIN (FORMAT JSON)` plan from this file.
    #[arg(long, conflicts_with = "postgres")]
    duckdb: Option<PathBuf>,
    /// Read PostgreSQL's `EXPLAIN (VERBOSE, FORMAT JSON)` plan from this file.
    #[arg(long)]
    postgres: Option<PathBuf>,
    /// A foreign key, as `orders(cust)->customers(id)`; repeatable.
    #[arg(long = "fk", value_parser = foreign_key)]
    foreign_keys: Vec<cardinal::ForeignKey>,
    /// Most distinct-count factors multiplied in one constraint.
    #[arg(long)]
    max_product: Option<usize>,
    /// Skip proving bounds: only the verdict is explained.
    #[arg(long)]
    no_bounds: bool,
}

#[derive(Args)]
struct Output {
    /// Write an HTML page here instead of printing text.
    #[arg(long)]
    html: Option<PathBuf>,
    /// Only the constraints of this proof (e.g. `verdict`, `sum`, `table:orders`).
    #[arg(long)]
    proof: Option<String>,
    /// Only this node's constraints, in full.
    #[arg(long, conflicts_with = "html")]
    node: Option<usize>,
    /// Hide constraints in the tree.
    #[arg(long, conflicts_with = "html")]
    brief: bool,
}

fn read(path: &PathBuf) -> Result<String, String> {
    fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn write(path: &PathBuf, text: &str) -> Result<(), String> {
    fs::write(path, text).map_err(|e| format!("{}: {e}", path.display()))
}

async fn analyze(input: &Input) -> Result<Dump, String> {
    let ctx = context(&read(&input.schema)?).await?;
    let sql = match (&input.sql, &input.query) {
        (Some(path), _) => Some(read(path)?),
        (_, Some(q)) => Some(q.clone()),
        _ => None,
    };
    let source = match (&input.duckdb, &input.postgres, sql) {
        (Some(p), _, sql) => Source::DuckDb { json: read(p)?, sql },
        (_, Some(p), sql) => Source::Postgres { json: read(p)?, sql },
        (None, None, Some(sql)) => Source::Sql(sql),
        (None, None, None) => return Err("give a query: --sql, --query, --duckdb or --postgres".into()),
    };
    let mut options = Options { foreign_keys: input.foreign_keys.clone(), ..Default::default() };
    if let Some(n) = input.max_product {
        options.max_product = n;
    }
    dump(&ctx, &source, options, !input.no_bounds).await
}

fn show(d: &Dump, output: &Output) -> Result<(), String> {
    match &output.html {
        Some(path) => {
            if let Some(p) = &output.proof
                && !d.proofs.iter().any(|x| x.name == *p)
            {
                return Err(format!("no proof {p:?}"));
            }
            write(path, &html::render(d, output.proof.as_deref()))?;
            eprintln!("wrote {}", path.display());
        }
        None => {
            let view = ascii::View { proof: output.proof.clone(), node: output.node, brief: output.brief };
            print!("{}", ascii::render(d, &view)?);
        }
    }
    Ok(())
}

async fn run(cli: Cli) -> Result<(), String> {
    match cli.command {
        Command::Dump { input, output, smt2 } => {
            let d = analyze(&input).await?;
            let json = serde_json::to_string_pretty(&d).map_err(|e| e.to_string())?;
            write(&output, &json)?;
            if let Some(path) = smt2 {
                write(&path, &d.trace.to_smt2())?;
            }
            eprintln!("{}: {} constraints over {} nodes", d.verdict, d.trace.constraints.len(), d.trace.nodes.len());
        }
        Command::View { dump, output } => {
            let d: Dump = serde_json::from_str(&read(&dump)?).map_err(|e| format!("{}: {e}", dump.display()))?;
            show(&d, &output)?;
        }
        Command::Analyze { input, output, smt2 } => {
            let d = analyze(&input).await?;
            if let Some(path) = smt2 {
                write(&path, &d.trace.to_smt2())?;
            }
            show(&d, &output)?;
        }
    }
    Ok(())
}

#[tokio::main]
async fn main() -> ExitCode {
    match run(Cli::parse()).await {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}
