//! Plan bounds with and without leaving out dead columns
//! ([`cardinal::postprocess`]): whether they agree, and how long each takes,
//! on the DuckDB fixtures, with and without the other queries' plans.
//! With the plans, dead columns are left out before `solve-eqs`
//! ([`cardinal::joint`]); compare the bounds themselves.
//!
//! ```sh
//! cargo test --release --test liveness_bench -- --ignored --nocapture
//! ```

mod fixtures;

use std::time::{Duration, Instant};

use cardinal::{Analysis, Options, Postprocess};
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
            cases.push((dir, plan, sql));
        }
    }
    let (mut off, mut on, mut same, mut differ) = (Duration::ZERO, Duration::ZERO, 0, 0);
    for (dir, plan, sql) in &cases {
        let others: Vec<_> = cases.iter().map(|(_, p, _)| p).filter(|p| p.name != plan.name).collect();
        let mut queries = vec![];
        if let Ok(q) = Analysis::sql(&ctx, sql).await {
            queries.push(("df", q));
        }
        queries.push(("duck", Analysis::plan(&catalog, plan)));
        for (planner, q) in queries {
            for with_plans in [false, true] {
                let plans = if with_plans { others.clone() } else { vec![] };
                let a = q.clone().options(options(false)).with_plans(plans.iter().copied()).build().unwrap();
                let b = q.clone().options(options(true)).with_plans(plans.iter().copied()).build().unwrap();
                let ((x, tx), (y, ty)) = (timed(&a), timed(&b));
                off += tx;
                on += ty;
                if x == y {
                    same += 1;
                } else {
                    differ += 1;
                    println!(
                        "DIFFER {dir}/{} {planner} plans={with_plans}\n  off {x}\n  on  {y}",
                        plan.name
                    );
                }
                println!(
                    "{dir}/{} {planner} plans={with_plans}: off {:.2}s on {:.2}s",
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
