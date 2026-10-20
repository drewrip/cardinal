//! Derives the selectivity equation for a TPC-H join with a filter:
//!
//! ```sql
//! SELECT * FROM lineitem JOIN orders ON l_orderkey = o_orderkey
//! WHERE l_discount < 0.01
//! ```
//!
//! No data is needed: the tables are registered empty, with their keys.
//! Run with `cargo run --example selectivity`.

use std::collections::HashMap;
use std::sync::Arc;

use cardinal::{ForeignKey, Options, analyze_sql_with};
use datafusion::arrow::datatypes::{DataType, Field, Schema};
use datafusion::common::{Constraint, Constraints};
use datafusion::datasource::MemTable;
use datafusion::prelude::SessionContext;

const SQL: &str = "SELECT * FROM lineitem JOIN orders ON l_orderkey = o_orderkey \
                   WHERE l_discount < 0.01";

/// Registers `name` as an empty table with `columns` and primary key `key`.
fn register(ctx: &SessionContext, name: &str, columns: &[(&str, DataType)], key: &[&str]) {
    let fields: Vec<Field> = columns.iter().map(|(c, t)| Field::new(*c, t.clone(), false)).collect();
    let schema = Arc::new(Schema::new(fields));
    let key = key.iter().map(|c| schema.index_of(c).unwrap()).collect();
    let table = MemTable::try_new(schema, vec![vec![]])
        .unwrap()
        .with_constraints(Constraints::new_unverified(vec![Constraint::PrimaryKey(key)]));
    ctx.register_table(name, Arc::new(table)).unwrap();
}

#[tokio::main]
async fn main() -> cardinal::Result<()> {
    let ctx = SessionContext::new();
    register(
        &ctx,
        "lineitem",
        &[
            ("l_orderkey", DataType::Int64),
            ("l_linenumber", DataType::Int64),
            ("l_discount", DataType::Decimal128(15, 2)),
        ],
        &["l_orderkey", "l_linenumber"],
    );
    register(
        &ctx,
        "orders",
        &[("o_orderkey", DataType::Int64), ("o_totalprice", DataType::Decimal128(15, 2))],
        &["o_orderkey"],
    );

    // Primary keys alone: the join is an unknown share of |lineitem|·|orders|.
    let options = Options { selectivity: true, ..Default::default() };
    let a = analyze_sql_with(&ctx, SQL, options.clone()).await?;
    let report = a.selectivity.unwrap();
    println!("{SQL}\n\nWith primary keys:\n{report}");

    // With lineitem.l_orderkey → orders.o_orderkey declared, each filtered
    // lineitem row finds exactly one order, so only the filter is unknown.
    let options = Options {
        foreign_keys: vec![ForeignKey::new("lineitem", &["l_orderkey"], "orders", &["o_orderkey"])],
        ..options
    };
    let a = analyze_sql_with(&ctx, SQL, options).await?;
    let report = a.selectivity.unwrap();
    println!("\nWith the foreign key:\n{report}");
    for s in &report.resolved {
        println!("  resolved: {s}");
    }

    // Plug in sizes (TPC-H SF1) and a value for each remaining selectivity.
    let tables = HashMap::from([("lineitem".to_string(), 6_001_215), ("orders".to_string(), 1_500_000)]);
    let values: HashMap<String, f64> = report.required.iter().map(|s| (s.name.clone(), 1.0 / 11.0)).collect();
    println!("\nAt SF1 with each selectivity = 1/11: X = {}", report.evaluate(&tables, &values)?);
    Ok(())
}
