//! The `cardinal-cli` binary end to end, on TPC-H's schema.

use std::path::PathBuf;
use std::process::Command;

use cardinal_cli::Dump;

const SCHEMA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/tpch.sql");
/// At most three orders, each with at most one customer.
const QUERY: &str = "SELECT o_orderkey, c_name FROM orders JOIN customer ON o_custkey = c_custkey WHERE o_orderkey IN (1, 2, 3)";

fn run(args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_cardinal-cli")).args(args).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap()
}

fn temp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("cardinal-cli-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(name)
}

#[test]
fn dump_then_view_as_text_and_html() {
    let (json, smt2, html) = (temp("q.json"), temp("q.smt2"), temp("q.html"));
    let fk = "orders(o_custkey)->customer(c_custkey)";
    let args = ["dump", "--schema", SCHEMA, "--query", QUERY, "--fk", fk, "--no-plan-bounds"];
    run(&[&args[..], &["-o", json.to_str().unwrap(), "--smt2", smt2.to_str().unwrap()]].concat());

    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    assert_eq!(dump.bounds.as_deref(), Some("0 <= X <= 3"));
    let upper = dump.proofs.iter().find(|p| p.name == "upper").unwrap();
    assert_eq!(upper.status, cardinal::ProofStatus::Proven);
    // Which minimal core Z3 finds depends on the constraints' order; any
    // names the operators it is from.
    assert!(!upper.core.is_empty() && upper.core.iter().all(|&c| dump.trace.constraints[c].node.is_some()));
    assert!(std::fs::read_to_string(&smt2).unwrap().contains("(assert "));
    assert!(dump.plan_bounds.is_none());

    let text = run(&["view", json.to_str().unwrap()]);
    assert!(text.contains("Inner Join: orders.o_custkey = customer.c_custkey"), "{text}");
    assert!(text.contains("upper"), "{text}");
    let proof = run(&["view", json.to_str().unwrap(), "--proof", "upper"]);
    assert!(proof.contains("● [") && proof.contains("Proof upper"), "{proof}");
    let node = run(&["view", json.to_str().unwrap(), "--node", "0"]);
    assert!(node.contains("rule: non_negative at src/rules/op_output.rs:"), "{node}");

    run(&["view", json.to_str().unwrap(), "--html", html.to_str().unwrap()]);
    let page = std::fs::read_to_string(&html).unwrap();
    assert!(page.contains("0 <= X <= 3") && page.contains("Inner Join"));
    assert!(!page.contains("__DATA__"));
}

#[test]
fn reads_duckdb_plans() {
    let plan = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/duckdb/explain/q03.json");
    let sql = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/tpch/q03.sql");
    let text = run(&["analyze", "--schema", SCHEMA, "--duckdb", plan, "--sql", sql, "--brief", "--no-bounds"]);
    assert!(text.contains("Root:") && text.contains("Plan and constraints:"), "{text}");
}

#[test]
fn unknown_proof_is_an_error() {
    let out = Command::new(env!("CARGO_BIN_EXE_cardinal-cli"))
        .args(["analyze", "--schema", SCHEMA, "--query", "SELECT * FROM nation", "--no-plan-bounds", "--proof", "nope"])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("no proof \"nope\""));
}

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/duckdb/tpch");
const Q04: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/tpch/q04.sql");
const Q04_FKS: [&str; 2] = ["lineitem(l_orderkey)->orders(o_orderkey)", "orders(o_custkey)->customer(c_custkey)"];

/// `dump` of TPC-H Q4 with its own profile as a reference plan, with
/// `extra` arguments.
fn dump_q04(name: &str, extra: &[&str]) -> (PathBuf, Dump) {
    let json = temp(name);
    let profile = format!("{PROFILES}/q04.json");
    let mut args = vec!["dump", "--schema", SCHEMA, "--sql", Q04, "--profile-duckdb", &profile, "--no-plan-bounds"];
    for fk in &Q04_FKS {
        args.extend(["--fk", fk]);
    }
    args.extend(extra);
    args.extend(["-o", json.to_str().unwrap()]);
    run(&args);
    let dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    (json, dump)
}

#[test]
fn reference_plans_from_profiles() {
    let (json, dump) = dump_q04("q04.json", &[]);
    let informed = dump.informed.as_ref().expect("an informed section");
    assert_eq!(informed.plans, ["q04"]);
    assert!(informed.explained && !informed.proofs.is_empty());
    assert_eq!(informed.proofs.len(), informed.base_proofs.len());
    let t = &informed.trace;
    // The query's nodes, then the plan's.
    assert_eq!(t.nodes.iter().filter(|n| n.plan.is_none()).count(), dump.trace.nodes.len());
    assert!(t.nodes.iter().any(|n| n.plan.as_deref() == Some("q04")));
    assert!(t.constraints.iter().any(|c| c.fact.as_ref().is_some_and(|f| f.source == "observed rows")));
    // Some bound holds only with the plan, and its proof names a pin.
    let tighter = informed.proofs.iter().zip(&informed.base_proofs).find(|(w, wo)| {
        w.status == cardinal::ProofStatus::Proven && wo.status != cardinal::ProofStatus::Proven
    });
    let (with, _) = tighter.expect("a bound only the plan proves");
    assert!(with.core.iter().any(|&c| t.constraints[c].fact.is_some()));

    let path = json.to_str().unwrap();
    let text = run(&["view", path]);
    for want in ["Informed: ", "Plans:   1 reference plans", "Reference plan q04:", "◆ [", "fact: observed rows", "Proofs (plain / informed)", "Pins and row counts used"] {
        assert!(text.contains(want), "no {want:?} in {text}");
    }
    let proof = run(&["view", path, "--proof", &with.name]);
    assert!(proof.contains(&format!("Proof {}", with.name)) && proof.contains("fact: "), "{proof}");
    let plain = run(&["view", path, "--plain"]);
    assert!(!plain.contains("Informed") && !plain.contains("◆") && !plain.contains("Reference plan"), "{plain}");

    let html = temp("q04.html");
    run(&["view", path, "--html", html.to_str().unwrap()]);
    let page = std::fs::read_to_string(&html).unwrap();
    assert!(page.contains("Plain") && page.contains("\"source\":\"observed rows\""));
}

#[test]
fn cardinalities_by_hand() {
    let sizes = temp("sizes.json");
    std::fs::write(&sizes, r#"{"nation": 25}"#).unwrap();
    let json = temp("hand.json");
    let sizes = sizes.to_str().unwrap();
    run(&["dump", "--schema", SCHEMA, "--query", "SELECT * FROM nation", "--cardinalities", sizes, "--no-plan-bounds", "-o", json.to_str().unwrap()]);
    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    let informed = dump.informed.expect("an informed section");
    assert!(informed.plans.is_empty());
    assert_eq!(informed.bounds.as_deref(), Some("X = 25"));
    assert!(informed.trace.constraints.iter().any(|c| c.fact.as_ref().is_some_and(|f| f.source == "given rows")));
}

#[test]
fn reference_plans_without_explaining() {
    let (_, dump) = dump_q04("q04-quick.json", &["--no-explain"]);
    let informed = dump.informed.expect("an informed section");
    assert!(!informed.explained && informed.proofs.is_empty() && informed.base_proofs.is_empty());
    assert!(informed.bounds.is_some());
}

#[test]
fn dumps_without_facts_still_load() {
    let json = temp("old.json");
    run(&["dump", "--schema", SCHEMA, "--query", QUERY, "--no-plan-bounds", "-o", json.to_str().unwrap()]);
    // A dump from before facts: no `informed`, and no `fact` on its
    // constraints or `plan` on its nodes.
    let mut v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    v.as_object_mut().unwrap().remove("informed");
    for c in v["trace"]["constraints"].as_array_mut().unwrap() {
        c.as_object_mut().unwrap().remove("fact");
    }
    for n in v["trace"]["nodes"].as_array_mut().unwrap() {
        n.as_object_mut().unwrap().remove("plan");
    }
    std::fs::write(&json, v.to_string()).unwrap();
    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    assert!(dump.informed.is_none() && dump.trace.constraints.iter().all(|c| c.fact.is_none()));
    let text = run(&["view", json.to_str().unwrap()]);
    assert!(!text.contains("Informed"), "{text}");
}

#[test]
fn every_operator_bound_has_a_proof_and_a_derivation() {
    let (json, html) = (temp("nodes.json"), temp("nodes.html"));
    run(&["dump", "--schema", SCHEMA, "--query", QUERY, "-o", json.to_str().unwrap()]);
    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    let plan = dump.plan_bounds.as_ref().expect("plan bounds");
    assert_eq!(plan.proofs.len(), plan.nodes.len());
    let root = dump.trace.nodes.len() - 1;
    let upper = plan.proof(&format!("n{root}.upper")).expect("the root node's upper proof");
    assert_eq!(upper.status, cardinal::ProofStatus::Proven);
    assert!(upper.minimal && upper.claim.starts_with(&format!("|#{root}| <= ")));

    // The derivation starts at the claim's variable and holds each of the
    // core's constraints once.
    let steps = cardinal_cli::derivation(&dump.trace, upper);
    let mut ids: Vec<usize> = steps.iter().map(|s| s.constraint).collect();
    ids.sort();
    assert_eq!(ids, upper.core);
    let first = &dump.trace.constraints[steps[0].constraint];
    assert!(steps[0].depth == 0 && first.vars.contains(&dump.trace.root), "{first:?}");

    let text = run(&["view", json.to_str().unwrap(), "--proof", &upper.name]);
    assert!(text.contains(&format!("Proof {}", upper.name)) && text.contains("<- c"), "{text}");
    run(&["view", json.to_str().unwrap(), "--html", html.to_str().unwrap(), "--proof", &upper.name]);
    let page = std::fs::read_to_string(&html).unwrap();
    assert!(page.contains(&format!("\"name\":\"{}\"", upper.name)) && page.contains("\"steps\":"));
}

#[test]
fn operator_proofs_with_reference_plans_name_pins() {
    let json = temp("q04-nodes.json");
    let profile = format!("{PROFILES}/q04.json");
    let mut args = vec!["dump", "--schema", SCHEMA, "--sql", Q04, "--profile-duckdb", &profile];
    for fk in &Q04_FKS {
        args.extend(["--fk", fk]);
    }
    args.extend(["-o", json.to_str().unwrap()]);
    run(&args);
    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    let informed = dump.informed.expect("an informed section");
    let t = &informed.trace;
    let plan = informed.plan_bounds.expect("informed plan bounds");
    let pinned = plan.proofs.iter().flatten().any(|p| p.core.iter().any(|&c| t.constraints[c].fact.is_some()));
    assert!(pinned, "no operator's proof uses a pin");
}

#[test]
fn dumps_without_node_proofs_still_load() {
    let json = temp("old-nodes.json");
    run(&["dump", "--schema", SCHEMA, "--query", QUERY, "-o", json.to_str().unwrap()]);
    // A dump from before node proofs: no `proofs` on its plan bounds, and no
    // `minimal` on its proofs.
    let mut v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    v["plan_bounds"].as_object_mut().unwrap().remove("proofs");
    for p in v["proofs"].as_array_mut().unwrap() {
        p.as_object_mut().unwrap().remove("minimal");
    }
    std::fs::write(&json, v.to_string()).unwrap();
    let dump: Dump = serde_json::from_str(&std::fs::read_to_string(&json).unwrap()).unwrap();
    assert!(dump.plan_bounds.unwrap().proofs.is_empty() && dump.proofs.iter().all(|p| p.minimal));
}
