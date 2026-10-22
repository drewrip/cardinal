//! `cardinal-debug`: dump what cardinal tells Z3 about a query, and view it.

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use cardinal::{FactMode, Options};
use cardinal_debug::{Dump, FactInput, Profile, Source, ascii, context, dump, foreign_key, html, read_facts};
use clap::{Args, Parser, Subcommand, ValueEnum};

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
    #[command(flatten)]
    facts: Facts,
}

/// Facts to inform the analysis with. Any of them adds a facts section.
#[derive(Args)]
struct Facts {
    /// A fact set, as JSON.
    #[arg(long)]
    facts: Option<PathBuf>,
    /// Read facts off DuckDB's `EXPLAIN (ANALYZE, FORMAT JSON)` profile in
    /// this file; repeatable.
    #[arg(long)]
    profile_duckdb: Vec<PathBuf>,
    /// Read facts off PostgreSQL's `EXPLAIN (ANALYZE, VERBOSE, FORMAT JSON)`
    /// profile in this file; repeatable.
    #[arg(long)]
    profile_postgres: Vec<PathBuf>,
    /// Read facts off every `*.json` profile in this directory.
    #[arg(long)]
    profiles_dir: Option<PathBuf>,
    /// The engine whose profiles --profiles-dir holds.
    #[arg(long, value_enum, default_value_t = Engine::Duckdb, requires = "profiles_dir")]
    profiles_format: Engine,
    /// Skip the profile `NAME.json` of --profiles-dir: inform a query from the
    /// others' profiles only.
    #[arg(long, value_name = "NAME", requires = "profiles_dir")]
    except: Option<String>,
    /// What facts may stand for: only selectivities, or row counts too.
    #[arg(long, value_enum, default_value_t = Mode::Ratios)]
    mode: Mode,
    /// Skip proving the bounds with facts again (and without them).
    #[arg(long)]
    no_explain: bool,
}

#[derive(Clone, Copy, ValueEnum)]
enum Engine {
    Duckdb,
    Postgres,
}

#[derive(Clone, Copy, ValueEnum)]
enum Mode {
    Ratios,
    Pinned,
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
    /// Show the analysis without its facts, as if none were given.
    #[arg(long)]
    without_facts: bool,
}

fn read(path: &PathBuf) -> Result<String, String> {
    fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn write(path: &PathBuf, text: &str) -> Result<(), String> {
    fs::write(path, text).map_err(|e| format!("{}: {e}", path.display()))
}

/// Each profile `facts` names, by its file's stem.
fn profiles(facts: &Facts) -> Result<Vec<Profile>, String> {
    let stem = |p: &PathBuf| p.file_stem().map_or_else(|| p.display().to_string(), |s| s.to_string_lossy().into_owned());
    let mut out = vec![];
    for (paths, postgres) in [(&facts.profile_duckdb, false), (&facts.profile_postgres, true)] {
        for p in paths {
            out.push(Profile { name: stem(p), json: read(p)?, postgres });
        }
    }
    if let Some(dir) = &facts.profiles_dir {
        let mut paths: Vec<PathBuf> = fs::read_dir(dir)
            .map_err(|e| format!("{}: {e}", dir.display()))?
            .filter_map(|e| Some(e.ok()?.path()))
            .filter(|p| p.extension().is_some_and(|e| e == "json"))
            .filter(|p| facts.except.as_deref().is_none_or(|x| stem(p) != x))
            .collect();
        paths.sort();
        let postgres = matches!(facts.profiles_format, Engine::Postgres);
        for p in paths {
            out.push(Profile { name: stem(&p), json: read(&p)?, postgres });
        }
    }
    Ok(out)
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
    let profiles = profiles(&input.facts)?;
    let facts = match &input.facts.facts {
        Some(p) => Some(serde_json::from_str(&read(p)?).map_err(|e| format!("{}: {e}", p.display()))?),
        None => None,
    };
    let facts = if facts.is_some() || !profiles.is_empty() {
        Some(FactInput {
            facts: read_facts(&ctx, facts, &profiles).await?,
            mode: match input.facts.mode {
                Mode::Ratios => FactMode::Ratios,
                Mode::Pinned => FactMode::Pinned,
            },
            explain: !input.facts.no_explain,
        })
    } else {
        None
    };
    dump(&ctx, &source, options, !input.no_bounds, facts.as_ref()).await
}

fn show(d: &Dump, output: &Output) -> Result<(), String> {
    match &output.html {
        Some(path) => {
            if let Some(p) = &output.proof
                && !d.proofs.iter().chain(d.facts.iter().flat_map(|f| &f.proofs)).any(|x| x.name == *p)
            {
                return Err(format!("no proof {p:?}"));
            }
            write(path, &html::render(d, output.proof.as_deref(), output.without_facts))?;
            eprintln!("wrote {}", path.display());
        }
        None => {
            let view = ascii::View {
                proof: output.proof.clone(),
                node: output.node,
                brief: output.brief,
                without_facts: output.without_facts,
            };
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
