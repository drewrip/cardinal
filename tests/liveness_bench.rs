//! Plan bounds with and without leaving out dead columns
//! ([`cardinal::postprocess`]): whether they agree, and how long each takes,
//! on the DuckDB fixtures, with and without facts of the other queries.
//!
//! ```sh
//! cargo test --release --test liveness_bench -- --ignored --nocapture
//! ```

mod fixtures;

use std::time::{Duration, Instant};

use cardinal::facts::FactSet;
use cardinal::{Analysis, Facts, Options, Postprocess};
use fixtures::{catalog, context, foreign_keys, plans, query};

fn options(dead_columns: bool) -> Options {
    Options {
        foreign_keys: foreign_keys(),
        postprocess: Postprocess { dead_columns },
        ..Default::default()
    }
}

fn timed(a: &Analysis) -> (String, Duration) {
    let t = Instant::now();
    let b = a.plan_bounds().unwrap();
    let s = b
        .nodes
        .iter()
        .map(|n| n.bounds.to_string())
        .chain([b.total.to_string()])
        .collect::<Vec<_>>()
        .join("|");
    (s, t.elapsed())
}

#[tokio::test]
#[ignore]
async fn liveness_bench() {
    let ctx = context();
    let catalog = catalog().await;
    let mut cases = vec![];
    for dir in ["extra", "tpch"] {
        for plan in plans(dir).await {
            let sql = query(dir, &plan.name);
            let mut observed = FactSet::default();
            observed.observe(&plan);
            cases.push((dir, plan, sql, observed));
        }
    }
    let (mut off, mut on, mut same, mut differ) = (Duration::ZERO, Duration::ZERO, 0, 0);
    for (dir, plan, sql, _) in &cases {
        let mut set = FactSet::default();
        for (_, p, _, o) in &cases {
            if p.name != plan.name {
                for f in o.iter() {
                    set.insert(f.clone());
                }
                for b in o.bounds() {
                    set.insert_bound(b.clone());
                }
                for f in o.floors() {
                    set.insert_floor(f.clone());
                }
            }
        }
        let facts = Facts::new(set);
        let mut pairs = vec![];
        if let (Ok(a), Ok(b)) = (
            cardinal::analyze_sql(&ctx, sql, options(false)).await,
            cardinal::analyze_sql(&ctx, sql, options(true)).await,
        ) {
            pairs.push(("df", a, b));
        }
        pairs.push((
            "duck",
            cardinal::analyze_observed(&catalog, plan, options(false)).unwrap(),
            cardinal::analyze_observed(&catalog, plan, options(true)).unwrap(),
        ));
        for (planner, a, b) in pairs {
            for with_facts in [false, true] {
                let (a, b) = if with_facts {
                    (a.with_facts(&facts).unwrap(), b.with_facts(&facts).unwrap())
                } else {
                    (a.clone(), b.clone())
                };
                let ((x, tx), (y, ty)) = (timed(&a), timed(&b));
                off += tx;
                on += ty;
                if x == y {
                    same += 1;
                } else {
                    differ += 1;
                    println!(
                        "DIFFER {dir}/{} {planner} facts={with_facts}\n  off {x}\n  on  {y}",
                        plan.name
                    );
                }
                println!(
                    "{dir}/{} {planner} facts={with_facts}: off {:.2}s on {:.2}s",
                    plan.name,
                    tx.as_secs_f64(),
                    ty.as_secs_f64()
                );
            }
        }
    }
    println!(
        "TOTAL plan_bounds: off {:.1}s on {:.1}s; analyses same {same}, differ {differ}",
        off.as_secs_f64(),
        on.as_secs_f64()
    );
}
