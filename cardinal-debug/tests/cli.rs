//! The `cardinal-debug` binary end to end, on TPC-H's schema.

use std::path::PathBuf;
use std::process::Command;

use cardinal_debug::Dump;

const SCHEMA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/tpch.sql");
const QUERY: &str = "SELECT o_orderkey, c_name FROM orders JOIN customer ON o_custkey = c_custkey WHERE o_totalprice > 100";

fn run(args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_cardinal-debug")).args(args).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap()
}

fn temp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("cardinal-debug-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(name)
}

#[test]
fn dump_then_view_as_text_and_html() {
    let (json, smt2, html) = (temp("q.json"), temp("q.smt2"), temp("q.html"));
    let fk = "orders(o_custkey)->customer(c_custkey)";
    run(&["dump", "--schema", SCHEMA, "--query", QUERY, "--fk", fk, "-o", json.to_str().unwrap(), "--smt2", smt2.to_str().unwrap()]);

    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    assert_eq!(dump.verdict, "Reduces");
    assert_eq!(dump.bounds.as_deref(), Some("X <= |orders|"));
    let table = dump.proofs.iter().find(|p| p.name == "table:orders").unwrap();
    assert_eq!(table.status, cardinal::ProofStatus::Proven);
    let join = dump.trace.nodes.iter().position(|n| n.label.starts_with("Inner Join")).unwrap();
    assert!(table.core.iter().any(|&c| dump.trace.constraints[c].node == Some(join)));
    assert!(std::fs::read_to_string(&smt2).unwrap().contains("(assert "));

    let text = run(&["view", json.to_str().unwrap()]);
    assert!(text.contains("Inner Join: orders.o_custkey = customer.c_custkey"), "{text}");
    assert!(text.contains("table:orders"), "{text}");
    let proof = run(&["view", json.to_str().unwrap(), "--proof", "table:orders"]);
    assert!(proof.contains("● [") && proof.contains("Proof table:orders"), "{proof}");
    let node = run(&["view", json.to_str().unwrap(), "--node", "0"]);
    assert!(node.contains("rule: fresh at src/analyzer.rs:"), "{node}");

    run(&["view", json.to_str().unwrap(), "--html", html.to_str().unwrap()]);
    let page = std::fs::read_to_string(&html).unwrap();
    assert!(page.contains("X <= |orders|") && page.contains("Inner Join"));
    assert!(!page.contains("__DATA__"));
}

#[test]
fn reads_duckdb_plans() {
    let plan = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/duckdb/explain/q03.json");
    let sql = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/tpch/q03.sql");
    let text = run(&["analyze", "--schema", SCHEMA, "--duckdb", plan, "--sql", sql, "--brief", "--no-bounds"]);
    assert!(text.contains("Verdict:") && text.contains("verdict"), "{text}");
}

#[test]
fn unknown_proof_is_an_error() {
    let out = Command::new(env!("CARGO_BIN_EXE_cardinal-debug"))
        .args(["analyze", "--schema", SCHEMA, "--query", "SELECT * FROM nation", "--proof", "nope"])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("no proof \"nope\""));
}
