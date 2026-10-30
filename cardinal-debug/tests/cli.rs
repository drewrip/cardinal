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
    assert!(node.contains("rule: non_negative at src/axioms.rs:"), "{node}");

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

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/duckdb/tpch");
const Q05: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/tpch/q05.sql");
const Q05_FKS: [&str; 6] = [
    "lineitem(l_orderkey)->orders(o_orderkey)",
    "lineitem(l_suppkey)->supplier(s_suppkey)",
    "orders(o_custkey)->customer(c_custkey)",
    "customer(c_nationkey)->nation(n_nationkey)",
    "supplier(s_nationkey)->nation(n_nationkey)",
    "nation(n_regionkey)->region(r_regionkey)",
];

/// `dump` of TPC-H Q5 informed by the other queries' profiles, with `extra`
/// arguments.
fn dump_q05(name: &str, extra: &[&str]) -> (PathBuf, Dump) {
    let json = temp(name);
    let mut args = vec!["dump", "--schema", SCHEMA, "--sql", Q05, "--profiles-dir", PROFILES, "--except", "q05"];
    for fk in &Q05_FKS {
        args.extend(["--fk", fk]);
    }
    args.extend(extra);
    args.extend(["-o", json.to_str().unwrap()]);
    run(&args);
    let dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    (json, dump)
}

#[test]
fn facts_from_profiles() {
    let (json, dump) = dump_q05("q05.json", &["--mode", "pinned"]);
    let facts = dump.facts.as_ref().expect("a facts section");
    assert_eq!(facts.mode, "pinned");
    assert!(facts.explained && !facts.proofs.is_empty());
    assert_eq!(facts.proofs.len(), facts.base_proofs.len());
    let base = dump.trace.constraints.len();
    assert_eq!(facts.trace.constraints[..base], dump.trace.constraints[..]);
    assert!(facts.trace.constraints[base..].iter().all(|c| c.fact.is_some()));
    assert!(!facts.report.pinned.is_empty(), "{:?}", facts.report);
    // Some bound holds only with the facts, and its proof names them.
    let tighter = facts.proofs.iter().zip(&facts.base_proofs).find(|(w, wo)| {
        w.status == cardinal::ProofStatus::Proven && wo.status != cardinal::ProofStatus::Proven
    });
    let (with, _) = tighter.expect("a bound only the facts prove");
    assert!(with.core.iter().any(|&c| facts.trace.constraints[c].fact.is_some()));

    let path = json.to_str().unwrap();
    let text = run(&["view", path]);
    for want in ["With facts: ", "Facts:   pinned", "◆ [", "fact: pinned rows", "Proofs (without facts / with facts)", "Facts used:", "Facts not used:"] {
        assert!(text.contains(want), "no {want:?} in {text}");
    }
    let proof = run(&["view", path, "--proof", &with.name]);
    assert!(proof.contains(&format!("Proof {}", with.name)) && proof.contains("fact: "), "{proof}");
    let without = run(&["view", path, "--without-facts"]);
    assert!(!without.contains("With facts") && !without.contains("◆"), "{without}");

    let html = temp("q05.html");
    run(&["view", path, "--html", html.to_str().unwrap()]);
    let page = std::fs::read_to_string(&html).unwrap();
    assert!(page.contains("Hide fact constraints") && page.contains("\"source\":\"pinned rows\""));
}

#[test]
fn facts_without_explaining() {
    let (_, dump) = dump_q05("q05-quick.json", &["--no-explain"]);
    let facts = dump.facts.expect("a facts section");
    assert_eq!(facts.mode, "ratios");
    assert!(!facts.explained && facts.proofs.is_empty() && facts.base_proofs.is_empty());
    assert!(facts.bounds.is_some());
}

#[test]
fn dumps_without_facts_still_load() {
    let json = temp("old.json");
    run(&["dump", "--schema", SCHEMA, "--query", QUERY, "-o", json.to_str().unwrap()]);
    // A dump from before facts: no `facts`, and no `fact` on its constraints.
    let mut v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    v.as_object_mut().unwrap().remove("facts");
    for c in v["trace"]["constraints"].as_array_mut().unwrap() {
        c.as_object_mut().unwrap().remove("fact");
    }
    std::fs::write(&json, v.to_string()).unwrap();
    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    assert!(dump.facts.is_none() && dump.trace.constraints.iter().all(|c| c.fact.is_none()));
    let text = run(&["view", json.to_str().unwrap()]);
    assert!(!text.contains("With facts"), "{text}");
}
