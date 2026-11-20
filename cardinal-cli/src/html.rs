//! A dump as one self-contained HTML page. It opens on the proof of the
//! result's upper bound: a "why" chain from the claim down to the table sizes,
//! pins and row counts it rests on ([`crate::derivation`]), beside the plan
//! tree with every operator's bounds. Clicking an operator's bound shows its
//! proof instead. Constraints are listed by node, routine ones folded, and
//! linked both ways with the tree. With reference plans or row counts, the
//! page can switch to the analysis without them.

use std::collections::HashMap;

use cardinal::{Proof, ProofStatus, Trace};
use serde_json::{Value, json};

use crate::{Dump, column_names, derivation};

/// The page for `dump`, opened on proof `proof` if given, and without its
/// reference plans and facts if `plain`.
pub fn render(dump: &Dump, proof: Option<&str>, plain: bool) -> String {
    let mut names = column_names(&dump.trace);
    if let Some(f) = &dump.informed {
        names.extend(column_names(&f.trace));
    }
    let plain_view = view(
        dump,
        &dump.trace,
        false,
        dump.bounds.as_deref(),
        dump.plan_bounds.as_ref().map(|p| (&p.nodes, &p.total)),
    );
    let informed_view = dump.informed.as_ref().map(|f| {
        view(dump, &f.trace, true, f.bounds.as_deref(), f.plan_bounds.as_ref().map(|p| (&p.nodes, &p.total)))
    });
    let data = json!({
        "query": dump.query,
        "plan": dump.plan,
        "plans": dump.informed.as_ref().map(|f| f.plans.clone()),
        "explained": dump.informed.as_ref().is_some_and(|f| f.explained),
        "views": { "plain": plain_view, "informed": informed_view },
        "names": names,
        "proof": proof,
        "plain": plain,
    });
    // Keep `</script>` in the data from closing the tag it sits in.
    let data = data.to_string().replace("</", "<\\/");
    TEMPLATE.replace("__DATA__", &data)
}

/// One side of the page: a trace, compactly, with the proofs over it, each
/// with its derivation, and the bounds proven.
fn view(dump: &Dump, t: &Trace, informed: bool, bounds: Option<&str>, plan: Option<(&Vec<String>, &String)>) -> Value {
    let proofs: Vec<Value> = dump.proofs_of(informed).into_iter().map(|p| proof(t, p)).collect();
    json!({
        "trace": compact(t),
        "proofs": proofs,
        "bounds": bounds,
        "nodes": plan.map(|p| p.0),
        "total": plan.map(|p| p.1),
    })
}

fn proof(t: &Trace, p: &Proof) -> Value {
    let (status, reason) = match &p.status {
        ProofStatus::Proven => ("Proven", None),
        ProofStatus::Refuted => ("Refuted", None),
        ProofStatus::Unknown(r) => ("Unknown", Some(r.clone())),
    };
    let steps: Vec<Value> = derivation(t, p).into_iter().map(|s| json!([s.constraint, s.depth, s.via])).collect();
    json!({
        "name": p.name, "claim": p.claim, "status": status, "reason": reason,
        "core": p.core, "minimal": p.minimal, "steps": steps,
    })
}

/// `t` with each constraint as `[smt, infix, node, rule, vars, fact]`, `rule`
/// indexing a table of distinct `[source, function, code]`: the same rules
/// make most constraints, and names repeated 25,000 times add up.
fn compact(t: &Trace) -> Value {
    let mut rules: Vec<[&str; 3]> = vec![];
    let mut index: HashMap<[&str; 3], usize> = HashMap::new();
    let cs: Vec<Value> = t
        .constraints
        .iter()
        .map(|c| {
            let key = [c.source.as_str(), c.function.as_str(), c.code.as_str()];
            let rule = *index.entry(key).or_insert_with(|| {
                rules.push(key);
                rules.len() - 1
            });
            json!([c.smt, c.infix, c.node, rule, c.vars, c.fact])
        })
        .collect();
    json!({
        "nodes": t.nodes,
        "root": t.root,
        "tables": t.tables,
        "declarations": t.declarations,
        "rules": rules,
        "cs": cs,
    })
}

const TEMPLATE: &str = r##"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Cardinal Trace</title>
<style>
:root {
  --bg: #ffffff; --sub: #f6f6f5; --ink: #18181b; --muted: #62626a; --faint: #a0a0a6;
  --rule: #dcdcdf; --rule-soft: #efeff1;
  --accent: #1d4ed8; --accent-bg: #eaf0fd; --hl: #fff4bf;
  --good: #166534; --bad: #b91c1c; --open: #b45309; --open-bg: #fdf3e4;
  --pin: #7c3aed; --pin-bg: #f1eafe;
  color-scheme: light;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #131315; --sub: #1c1c1f; --ink: #ececee; --muted: #a2a2a8; --faint: #66666c;
    --rule: #34343a; --rule-soft: #24242a;
    --accent: #7aa2ff; --accent-bg: #1b2540; --hl: #46401a;
    --good: #6ee7a0; --bad: #ff8a8a; --open: #f2b866; --open-bg: #3a2c16;
    --pin: #c4a5ff; --pin-bg: #2a2140;
    color-scheme: dark;
  }
}
* { box-sizing: border-box; }
html, body { margin: 0; background: var(--bg); color: var(--ink); }
body { font: 13px/1.5 -apple-system, system-ui, "Segoe UI", sans-serif; }
code, pre, .m { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 12px; }
pre { margin: 0; white-space: pre-wrap; overflow-wrap: anywhere; }
h2 { font-size: 11px; font-weight: 600; text-transform: uppercase; letter-spacing: .06em; color: var(--muted); margin: 0 0 8px; }
table { border-collapse: collapse; width: 100%; }
th { text-align: left; font-weight: 600; color: var(--muted); }
button { font: inherit; font-size: 12px; padding: 2px 8px; border: 1px solid var(--rule); border-radius: 3px;
  background: none; color: var(--muted); cursor: pointer; }
button:hover { color: var(--ink); border-color: var(--muted); }
details > summary { cursor: pointer; color: var(--muted); width: max-content; }
details > summary:hover { color: var(--ink); }
details[open] > summary { margin-bottom: 6px; }
details pre { padding: 8px; background: var(--sub); border: 1px solid var(--rule-soft); max-height: 24em; overflow: auto; }
.note { color: var(--muted); }
.good { color: var(--good); } .bad { color: var(--bad); } .warn { color: var(--open); }
[hidden] { display: none !important; }

/* Bounds: a closed range in bold, one with no upper end in amber. */
.bd { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-weight: 600; white-space: nowrap; }
.bd.open { color: var(--open); font-weight: 500; }
.bd.none { color: var(--faint); font-weight: 400; background: none !important; }
.pn .bd, tr.gh .bd { font-size: 12px; padding: 0 6px; border-radius: 3px; background: var(--sub); }
.pn .bd.open, tr.gh .bd.open { background: var(--open-bg); }
.bd.link { cursor: pointer; text-decoration: underline dotted var(--faint); text-underline-offset: 3px; }
.bd.link:hover { box-shadow: 0 0 0 1px var(--accent); }
.bd.sel { background: var(--accent) !important; color: var(--bg) !important; text-decoration: none; }
.pin { color: var(--pin); font-size: 11px; white-space: nowrap; }

/* Header */
header { padding: 12px 16px 10px; border-bottom: 1px solid var(--rule); }
.top { display: flex; flex-wrap: wrap; align-items: baseline; gap: 4px 12px; margin-bottom: 10px; }
.top .grow { flex: 1; }
h1 { font-size: 15px; margin: 0; }
.hrow { display: flex; flex-wrap: wrap; gap: 10px 24px; align-items: stretch; margin-bottom: 10px; }
.cards { display: flex; gap: 10px; }
.card { border: 1px solid var(--rule); border-radius: 4px; padding: 6px 14px; min-width: 11em; }
.card .k { font-size: 11px; color: var(--muted); }
.card .bd { display: block; font-size: 20px; line-height: 1.3; }
.card .was { color: var(--muted); font-size: 12px; min-height: 1em; }
.claims { display: flex; flex-direction: column; gap: 4px; justify-content: center; }
.claim { display: flex; gap: 10px; align-items: baseline; padding: 3px 10px; border: 1px solid var(--rule); border-radius: 4px;
  cursor: pointer; background: none; color: var(--ink); text-align: left; font-size: 13px; }
.claim:hover { border-color: var(--muted); }
.claim.on { border-color: var(--accent); background: var(--accent-bg); }
.claim .c { font-weight: 600; min-width: 7em; }
#query { color: var(--muted); max-height: 4.6em; overflow: hidden; cursor: pointer; position: relative; margin-bottom: 6px; }
#query.full { max-height: none; }
#query:not(.full)::after { content: "… click to show all"; position: absolute; right: 0; bottom: 0; padding-left: 2em;
  background: linear-gradient(to right, transparent, var(--bg) 1.5em); color: var(--faint); }
.more { display: flex; flex-wrap: wrap; gap: 4px 20px; }
dl.notation { display: grid; grid-template-columns: max-content 1fr; gap: 2px 14px; margin: 0 0 4px; color: var(--muted); max-width: 60em; }
dl.notation dt { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 12px; color: var(--ink); }
dl.notation dd { margin: 0; }
table.facts th, table.facts td { padding: 3px 12px 3px 0; border-bottom: 1px solid var(--rule-soft); vertical-align: top; overflow-wrap: anywhere; }
table.facts thead th { border-bottom: 1px solid var(--rule); font-size: 12px; font-weight: 500; }

/* Toolbar */
.toolbar { display: flex; flex-wrap: wrap; gap: 8px 16px; align-items: center; padding: 7px 16px;
  border-bottom: 1px solid var(--rule); background: var(--bg); position: sticky; top: 0; z-index: 3; }
.toolbar input[type=search] { font: inherit; padding: 3px 8px; width: 18em; max-width: 100%;
  border: 1px solid var(--rule); border-radius: 3px; background: var(--bg); color: var(--ink); }
.toolbar label { color: var(--muted); white-space: nowrap; }
.toolbar .count { margin-left: auto; color: var(--muted); }
.toolbar .sel { color: var(--accent); font-weight: 600; }

/* Body */
main { display: grid; grid-template-columns: minmax(340px, 40%) 1fr; }
@media (max-width: 900px) {
  main { grid-template-columns: 1fr; }
  .plan { position: static !important; max-height: none !important; border-right: 0 !important; border-bottom: 1px solid var(--rule); }
  table.cs col.rule, table.cs td.rule, table.cs th.rule { display: none; }
}
.plan { padding: 12px 12px 14px 16px; border-right: 1px solid var(--rule); position: sticky; top: 41px;
  max-height: calc(100vh - 41px); overflow: auto; }
.thead, .pn { display: grid; grid-template-columns: 2.6em 1fr auto 3.2em; gap: 0 8px; align-items: baseline; }
.thead { color: var(--faint); font-size: 11px; padding: 0 6px 4px; border-bottom: 1px solid var(--rule-soft); margin-bottom: 4px; }
.thead span:last-child, .pn .n { text-align: right; }
.plan ul { list-style: none; margin: 0; padding: 0 0 0 14px; border-left: 1px solid var(--rule); }
.plan #tree > ul { padding-left: 0; border-left: 0; }
.pn { padding: 3px 6px; margin: 1px 0; cursor: pointer; border-left: 3px solid transparent; border-radius: 0 3px 3px 0; }
.pn:hover, .pn.hl { background: var(--hl); }
.pn .id { color: var(--faint); }
.pn .op { overflow-wrap: anywhere; min-width: 0; }
.pn .op b { font-weight: 600; }
.pn .d { color: var(--muted); display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; }
.pn .bds { display: flex; gap: 4px; align-items: baseline; justify-content: flex-end; }
.pn .n { color: var(--faint); white-space: nowrap; font-size: 11px; }
.pn.alias .op, .pn.alias .op b { color: var(--faint); font-weight: 400; }
.pn.core { border-left-color: var(--accent); background: var(--accent-bg); }
.pn.core .n { color: var(--accent); font-weight: 600; }
.pn.out { opacity: .45; }
.sub { color: var(--muted); font-style: italic; padding: 8px 0 2px; }
.refh { color: var(--muted); padding: 6px 0 2px; cursor: pointer; user-select: none; }
.refh:hover { color: var(--ink); }
.refh .tw { display: inline-block; width: 1em; color: var(--faint); }
.refh.core { color: var(--accent); }

.right { min-width: 0; }
#why { padding: 12px 16px 14px; border-bottom: 1px solid var(--rule); }
.why-head { display: flex; align-items: baseline; gap: 12px; }
.why-head h2 { margin: 0; }
.why-head .grow { flex: 1; }
#explain { margin: 6px 0 10px; color: var(--muted); }
.tag { font-size: 11px; padding: 0 6px; border-radius: 3px; background: var(--open-bg); color: var(--open); }
ol.chain { list-style: none; margin: 0; padding: 0; }
ol.chain li.claim-row { font-weight: 600; padding: 2px 0 4px; }
ol.chain li.step { display: grid; grid-template-columns: 5.2em 4.5em 1fr auto 3.4em; gap: 0 8px; align-items: baseline;
  padding: 2px 4px; border-radius: 3px; cursor: pointer; }
ol.chain li.step:hover, ol.chain li.step.hl { background: var(--hl); }
ol.chain .conn { color: var(--faint); text-align: right; font-size: 12px; }
ol.chain .conn.why { color: var(--muted); }
ol.chain .cid { color: var(--accent); }
ol.chain .rl { color: var(--muted); font-size: 12px; white-space: nowrap; }
ol.chain .nd { color: var(--faint); text-align: right; }
ol.chain .nd:hover { color: var(--accent); }
ol.chain .read { grid-column: 3 / 6; color: var(--pin); font-size: 12px; }
ol.chain li.fact .f { color: var(--pin); }

.list { padding: 12px 16px; }
table.cs { table-layout: fixed; }
table.cs col.id { width: 5em; } table.cs col.rule { width: 13em; }
table.cs thead th { position: sticky; top: 41px; background: var(--bg); border-bottom: 1px solid var(--rule); padding: 4px 8px 4px 0;
  font-size: 12px; font-weight: 500; z-index: 1; }
table.cs td { padding: 2px 8px 2px 0; border-bottom: 1px solid var(--rule-soft); vertical-align: top; overflow-wrap: anywhere; }
table.cs td.id { padding-left: 6px; color: var(--faint); }
table.cs td.rule { color: var(--muted); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
tr.gh td { padding: 12px 6px 4px; border-bottom: 1px solid var(--rule); background: var(--bg); cursor: pointer; }
tr.gh .row { display: flex; gap: 8px; align-items: baseline; }
tr.gh .lab { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
tr.gh b { font-weight: 600; }
tr.gh .d { color: var(--muted); }
tr.gh.hl td { background: var(--hl); }
tr.c { cursor: pointer; }
tr.c:hover td { background: var(--sub); }
tr.c.hl td, tr.c.flash td { background: var(--hl); }
tr.c.core td.id { box-shadow: inset 3px 0 0 var(--accent); color: var(--accent); font-weight: 600; }
tr.c.core td.f { font-weight: 600; }
tr.c.fact td.id, tr.c.fact td.rule { color: var(--pin); }
tr.fold td { padding: 2px 6px 4px; color: var(--faint); font-size: 12px; cursor: pointer; border-bottom: 1px solid var(--rule-soft); }
tr.fold td:hover { color: var(--ink); }
tr.x td { padding: 4px 8px 8px 6px; background: var(--sub); border-bottom: 1px solid var(--rule); }
tr.x th { color: var(--muted); font-weight: 400; width: 5em; padding: 2px 8px 2px 0; vertical-align: top; }
tr.x table td { background: none; border: 0; padding: 2px 0; }
.var { border-bottom: 1px dotted var(--faint); }
.var.hl { background: var(--hl); }
</style>
</head>
<body>
<header>
  <div class="top">
    <h1>cardinal</h1><span class="note" id="stats"></span><span class="grow"></span>
    <label id="hide-label" class="note" hidden title="Show the analysis as if no reference plans or row counts were given"><input type="checkbox" id="hide"> Plain</label>
  </div>
  <div class="hrow">
    <div class="cards">
      <div class="card"><div class="k">Rows out</div><span class="bd" id="out"></span><div class="was" id="out-was"></div></div>
      <div class="card" id="total-card" hidden><div class="k">Rows over every operator</div><span class="bd" id="total"></span><div class="was" id="total-was"></div></div>
    </div>
    <div class="claims" id="claims"></div>
  </div>
  <pre id="query" title="Click to show all"></pre>
  <div class="more">
    <details><summary>Optimized plan</summary><pre id="plan"></pre></details>
    <details id="facts" hidden><summary>Pins and row counts: <span id="facts-n"></span></summary>
      <table class="facts"><thead><tr><th>Kind</th><th>Claim</th><th>From facts</th><th>Read off</th></tr></thead><tbody id="facts-used"></tbody></table>
    </details>
    <details><summary>Notation</summary>
      <dl class="notation">
        <dt>X</dt><dd>Rows output by the result (the root operator).</dd>
        <dt>|#n|</dt><dd>Rows output by plan node n.</dd>
        <dt>#n[col]</dt><dd>Distinct values of column col in node n's output (NULL counts as one).</dd>
        <dt>|#n unfiltered|</dt><dd>Rows of scan n before its pushed-down filters.</dd>
        <dt>|t|</dt><dd>Rows in base table t.</dd>
        <dt>part{n}</dt><dd>Rows of a table shared by op outputs whose rows are disjoint.</dd>
        <dt>◆</dt><dd>A pin (a count read off a reference plan) or a given row count, or a node with one.</dd>
        <dt>≥ n</dt><dd>No upper bound was proven.</dd>
        <dt>plain / informed</dt><dd>The analysis without / with the reference plans and row counts given.</dd>
        <dt>because</dt><dd>A proof's constraints, from the claim down: each row explains a variable of the rows above it; "and" rows are needed together.</dd>
      </dl>
      <p class="note">Hover a variable for its full name. Click a bound in the plan to see why it holds.</p>
    </details>
  </div>
</header>

<div class="toolbar">
  <input type="search" id="search" placeholder="Filter constraints…" aria-label="Filter constraints">
  <label title="Show only the constraints the selected proof needs"><input type="checkbox" id="only"> Only needed</label>
  <span class="count" id="count"></span>
  <button id="copy">Copy SMT-LIB</button>
  <button id="save">Save .smt2</button>
</div>

<main>
  <nav class="plan" aria-label="Plan">
    <h2>Plan and bounds</h2>
    <div class="thead"><span>#</span><span>operator</span><span>bound</span><span title="Constraints of the node; under a proof, needed / all">cons.</span></div>
    <div id="tree"></div>
  </nav>
  <div class="right">
    <section id="why" hidden>
      <div class="why-head"><h2 id="why-title">Why</h2><span id="why-tag"></span><span class="grow"></span><button id="clear">Show every constraint</button></div>
      <p id="explain"></p>
      <ol class="chain" id="chain"></ol>
    </section>
    <div class="list">
      <h2>Constraints</h2>
      <table class="cs" id="cs">
        <colgroup><col class="id"><col><col class="rule"></colgroup>
        <thead><tr><th style="padding-left:6px">#</th><th>Constraint</th><th class="rule">Rule</th></tr></thead>
      </table>
    </div>
  </div>
</main>

<script type="application/json" id="data">__DATA__</script>
<script>
(() => {
  const D = JSON.parse(document.getElementById('data').textContent);
  // The page as written, to mount again on switching views.
  const ORIGINAL = document.body.innerHTML;
  // Rules folded under a group's summary row unless a proof needs them.
  const ROUTINE = new Set(['non_negative', 'nonempty_ndv', 'ndv_within_rows', 'range_within_domain']);
  let ac = null;

  // A view's trace with its constraints unpacked into objects.
  function unpack(v) {
    const t = v.trace;
    if (!t.constraints) t.constraints = t.cs.map(([smt, infix, node, rule, vars, fact], id) => {
      const [source, fn, code] = t.rules[rule];
      return { id, smt, infix, node, source, function: fn, code, vars, fact };
    });
    return t;
  }

  // Mounts the page: plain (without reference plans and facts) or informed;
  // `keep` carries the proof selected and the filters over.
  function mount(plain, keep) {
    if (ac) { ac.abort(); document.body.innerHTML = ORIGINAL; }
    ac = new AbortController();
    const on = (e, ev, f) => e.addEventListener(ev, f, { signal: ac.signal });
    const hasInformed = !!D.views.informed;
    const informed = hasInformed && !plain;
    const V = informed ? D.views.informed : D.views.plain, O = informed ? D.views.plain : D.views.informed;
    const t = unpack(V), names = D.names;
    const otherName = informed ? 'plain' : 'informed';
    const $ = id => document.getElementById(id);
    const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; };
    const isFact = c => !!c.fact;
    const isPin = c => !!c.fact && c.fact.source.startsWith('observed');
    const nodeProof = /^n(\d+)\.(lower|upper)$/;

    // Proofs: the result's, then each node's, by name.
    const proofs = {}, rootProofs = [], nodeProofs = {};
    for (const p of V.proofs) {
      proofs[p.name] = p;
      const m = p.name.match(nodeProof);
      if (m) (nodeProofs[+m[1]] ??= []).push(p); else rootProofs.push(p);
    }
    const otherProof = {};
    if (O && D.explained) for (const p of O.proofs) if (!nodeProof.test(p.name)) otherProof[p.name] = p;

    // A bound, compactly: "= 60,175", "≤ 25", "3 – 25", or "≥ 100" when no
    // upper end was proven.
    const num = n => Number(n).toLocaleString('en-US');
    function boundText(s) {
      if (!s) return { text: '—', open: true };
      let m;
      if ((m = s.match(/^X = (\d+)$/))) return { text: '= ' + num(m[1]), open: false };
      if ((m = s.match(/^(\d+) <= X <= (\d+)$/))) return { text: m[1] === '0' ? '≤ ' + num(m[2]) : `${num(m[1])} – ${num(m[2])}`, open: false };
      if ((m = s.match(/^X <= (\d+)$/))) return { text: '≤ ' + num(m[1]), open: false };
      if ((m = s.match(/^X >= (\d+)$/))) return { text: '≥ ' + num(m[1]), open: m[1] !== '0', none: m[1] === '0' };
      return { text: s, open: !/<=|=/.test(s) };
    }
    function setBound(e, s, other) {
      const b = boundText(s);
      e.textContent = b.text;
      e.classList.toggle('open', b.open);
      e.classList.toggle('none', !!b.none);
      e.title = (s ?? 'not computed') + (other !== undefined && other !== s ? `\n${otherName}: ${other ?? 'not computed'}` : '');
    }
    const claimText = s => s.replace(/<=/g, '≤').replace(/>=/g, '≥').replace(/\d{4,}/g, num);

    // Variables: the node each describes, and a short name for each.
    const owner = {}, short = {};
    for (const n of t.nodes) {
      owner[n.var] = n.id;
      short[n.var] = `|#${n.id}|`;
      if (n.raw_var) { owner[n.raw_var] = n.id; short[n.raw_var] = `|#${n.id} unfiltered|`; }
      n.columns.forEach(([, nv], j) => {
        owner[nv] = n.id;
        const full = names[nv] ?? '', i = full.lastIndexOf('[');
        short[nv] = `#${n.id}[${i >= 0 ? full.slice(i + 1, -1) : 'c' + j}]`;
      });
    }
    for (const [name, sym] of t.tables) short[sym] = `|${name}|`;
    const isVar = s => short[s] !== undefined || /^part\d+$/.test(s);
    const shortName = v => short[v] ?? names[v] ?? v;

    // Header.
    const q = $('query');
    q.textContent = D.query.trim();
    on(q, 'click', () => q.classList.toggle('full'));
    $('plan').textContent = D.plan;
    if (hasInformed) { $('hide-label').hidden = false; $('hide').checked = !informed; }
    const byNode = {};
    for (const c of t.constraints) (byNode[c.node ?? 'p'] ??= []).push(c);
    const partitions = (byNode.p ?? []).length;
    const referenced = t.nodes.filter(n => n.plan).length;
    const pins = t.constraints.filter(isPin).length, facts = t.constraints.filter(isFact).length - pins;
    $('stats').textContent = `${t.nodes.length} plan nodes` + (referenced ? ` (${referenced} in ${D.plans.length} reference plans)` : '') +
      ` · ${num(t.constraints.length)} constraints` + (partitions ? ` (${num(partitions)} over table partitions)` : '') +
      (informed ? ` · ${pins} pins · ${facts} row counts` : '') + (hasInformed && !informed ? ' · plain' : '');
    $('total-card').hidden = !V.nodes;
    setBound($('out'), V.bounds, O ? O.bounds : undefined);
    if (V.total) setBound($('total'), V.total, O ? O.total : undefined);
    const was = (e, a, b) => { e.textContent = O && a !== b ? `${otherName} ${boundText(b).text}` : ''; };
    if (O) { was($('out-was'), V.bounds, O.bounds); if (V.total) was($('total-was'), V.total, O.total); }

    // What a proof's status says, against the other view's.
    function statusOf(p) {
      const o = otherProof[p.name];
      if (p.status === 'Proven') {
        const needs = o && o.status !== 'Proven' ? (informed ? 'needs reference plans' : '') : '';
        return { label: 'proven', cls: 'good', note: needs };
      }
      const also = o && o.status === 'Proven' ? 'proven with reference plans' : '';
      return p.status === 'Refuted' ? { label: 'refuted', cls: 'bad', note: also } : { label: 'unknown', cls: 'warn', note: p.reason ?? '' };
    }

    // The result's claims.
    const claimButtons = {};
    if (!rootProofs.length) {
      $('claims').append(el('span', 'note', informed && !D.explained ? 'Proofs skipped (--no-explain).' : 'Nothing to prove: no bound beyond X ≥ 0.'));
    }
    for (const p of rootProofs) {
      const b = el('button', 'claim');
      const s = statusOf(p);
      b.append(el('span', 'c m', claimText(p.claim)), el('span', s.cls, s.label));
      if (s.note) b.append(el('span', 'note', s.note));
      if (p.status === 'Proven') b.append(el('span', 'note', p.core.length === 1 ? '1 constraint' : `${p.core.length} constraints`));
      on(b, 'click', () => select(p.name));
      claimButtons[p.name] = b;
      $('claims').append(b);
    }

    // An operator's label: its kind in bold, the rest muted.
    function opLabel(n, cls, inline) {
      const line = n.label.split('\n')[0];
      const i = line.indexOf(':');
      const box = el('span', cls);
      box.append(el('b', null, i < 0 ? line : line.slice(0, i)));
      if (i >= 0) box.append(inline ? ' ' : '', el(inline ? 'span' : 'div', 'd m', line.slice(i + 1).trim()));
      return box;
    }
    // What pins and row counts hold a node's rows to.
    function pinned(n) {
      const mine = [n.var, n.raw_var].filter(x => x);
      return (byNode[n.id] ?? []).filter(c => c.fact && c.vars.length === 1 && mine.includes(c.vars[0]))
        .map(c => `${c.vars[0] === n.var ? 'rows' : 'unfiltered rows'} ${c.fact.value}`);
    }
    // A node's bound badge, linked to its proof if it has one.
    const badges = [];
    function badge(id) {
      const b = el('span', 'bd');
      const ps = nodeProofs[id] ?? [];
      const p = ps.find(x => x.name.endsWith('.upper') && x.status === 'Proven') ?? ps.find(x => x.status === 'Proven');
      if (p) { b.classList.add('link'); b.dataset.proof = p.name; }
      badges.push([b, id]);
      return b;
    }

    // Plan tree, root first; nodes no other node takes as input are roots:
    // the query's, then each reference plan's parts, folded.
    const used = new Set(t.nodes.flatMap(n => n.inputs));
    const rootsOf = {};
    for (const n of t.nodes) if (!used.has(n.id)) (rootsOf[n.plan ?? ''] ??= []).push(n.id);
    const treeNodes = {}, order = [], refs = {};
    function build(id) {
      const n = t.nodes[id];
      order.push(id);
      const li = el('li');
      const row = el('div', n.label.startsWith('SubqueryAlias') ? 'pn alias' : 'pn');
      row.dataset.node = id;
      const pin = pinned(n);
      row.title = [n.label, n.var, ...pin.map(p => '◆ ' + p)].join('\n');
      const bds = el('span', 'bds');
      bds.append(badge(id));
      if (pin.length) { const s = el('span', 'pin', '◆ pinned'); s.title = pin.join('\n'); bds.append(s); }
      const count = el('span', 'n m');
      row.append(el('span', 'id m', String(id)), opLabel(n, 'op'), bds, count);
      treeNodes[id] = { row, count };
      li.append(row);
      if (n.inputs.length) {
        const ul = el('ul');
        for (const i of n.inputs) ul.append(build(i));
        li.append(ul);
      }
      return li;
    }
    const top = el('ul');
    (rootsOf[''] ?? []).slice().reverse().forEach((r, i) => {
      if (i > 0) top.append(el('li', 'sub', 'Subquery inside an expression'));
      top.append(build(r));
    });
    const refOf = {};
    for (const [name, rs] of Object.entries(rootsOf)) {
      if (!name) continue;
      const li = el('li'), head = el('div', 'refh'), ul = el('ul');
      const start = order.length;
      for (const r of rs.slice().reverse()) ul.append(build(r));
      const ids = order.slice(start);
      for (const id of ids) refOf[id] = name;
      head.append(el('span', 'tw', '▸'), `Reference plan ${name} · ${ids.length} nodes`);
      refs[name] = { head, ul, open: false };
      on(head, 'click', () => { setRef(name, !refs[name].open); filter(); });
      li.append(head, ul);
      top.append(li);
    }
    function setRef(name, open) {
      const r = refs[name];
      r.open = open;
      r.ul.hidden = !open;
      r.head.firstChild.textContent = open ? '▾' : '▸';
    }
    for (const name of Object.keys(refs)) setRef(name, false);
    $('tree').append(top);

    // A formula, each variable shortened and linked to its node.
    function formula(text, cls = 'f m', tag = 'td') {
      const f = el(tag, cls);
      for (const part of text.split(/([A-Za-z0-9_]+)/)) {
        if (!part) continue;
        if (isVar(part)) {
          const s = el('span', 'var', shortName(part));
          s.dataset.var = part;
          s.title = `${names[part] ?? part}\n${part}`;
          f.append(s);
        } else {
          f.append(document.createTextNode(part));
        }
      }
      return f;
    }
    const ruleOf = c => isPin(c) ? `pin: ${c.fact.source}` : isFact(c) ? `row count: ${c.fact.source}` : c.function;

    // Constraint table: a body per node, built when first shown.
    const groups = {}, rows = {};
    const groupKeys = [...order, 'p'].filter(k => (byNode[k] ?? []).length);
    for (const key of groupKeys) {
      const body = el('tbody');
      const gh = el('tr', 'gh');
      const td = el('td');
      td.colSpan = 3;
      const line = el('div', 'row');
      if (key === 'p') {
        const lab = el('span', 'lab');
        lab.append(el('b', null, 'Table partitions'), el('span', 'd', ' — op outputs of one table with disjoint rows share its rows'));
        line.append(lab);
      } else {
        const n = t.nodes[key];
        const lab = el('span', 'lab');
        lab.append(el('span', 'm note', `#${key}${n.plan ? ' · ' + n.plan : ''}  `), opLabel(n, null, true));
        lab.title = `${n.label}\n${n.var}`;
        line.append(lab, badge(key));
        gh.dataset.node = key;
      }
      td.append(line);
      gh.append(td);
      const fold = el('tr', 'fold');
      const ftd = el('td');
      ftd.colSpan = 3;
      fold.append(ftd);
      body.append(gh);
      body.hidden = true;
      $('cs').append(body);
      groups[key] = { body, gh, fold, ftd, built: false, unfold: false };
      on(fold, 'click', () => { groups[key].unfold = true; filter(); });
    }
    function buildGroup(key) {
      const g = groups[key];
      if (g.built) return;
      g.built = true;
      for (const c of byNode[key]) {
        const r = el('tr', isFact(c) ? 'c fact' : 'c');
        r.dataset.c = c.id;
        const rule = el('td', 'rule m', ruleOf(c));
        rule.title = `${c.function}\n${c.source}`;
        r.append(el('td', 'id m', 'c' + c.id + (isFact(c) ? ' ◆' : '')), formula(c.infix), rule);
        const x = el('tr', 'x');
        x.hidden = true;
        on(r, 'click', () => {
          if (!x.firstChild) x.append(detail(c));
          x.hidden = !x.hidden;
        });
        rows[c.id] = { r, x };
        g.body.append(r, x);
      }
      g.body.append(g.fold);
    }
    function detail(c) {
      const xd = el('td');
      xd.colSpan = 3;
      const kv = el('table');
      const items = [['SMT-LIB', c.smt], ['Names', c.vars.map(v => `${shortName(v)} = ${names[v] ?? v}`).join('\n')], ['Made by', `${c.function} at ${c.source}`], ['Code', c.code]];
      if (isFact(c)) {
        items.push(['Asserts', `${shortName(c.vars[0] ?? '')} ${c.fact.value}`]);
        for (const f of c.fact.facts) items.push([isPin(c) ? 'Count' : 'Fact', f.text + (f.origins.length ? `\nread off ${f.origins.join(', ')}` : '')]);
      }
      for (const [k, v] of items) {
        if (!v) continue;
        const tr = el('tr'), val = el('td');
        val.append(el('pre', null, v));
        tr.append(el('th', null, k), val);
        kv.append(tr);
      }
      xd.append(kv);
      return xd;
    }

    // Every operator's bounds, the query's only.
    for (const [e, id] of badges) {
      const b = V.nodes?.[id];
      e.hidden = b === undefined;
      if (b !== undefined) setBound(e, b, O?.nodes?.[id]);
      if (e.dataset.proof) e.title += '\nClick: why it holds';
    }

    // Hover: a node lights its constraints' header and its tree entry; a
    // variable lights every use of it and the node it describes.
    const lit = [];
    const light = e => { if (e) { e.classList.add('hl'); lit.push(e); } };
    const clear = () => { while (lit.length) lit.pop().classList.remove('hl'); };
    on(document, 'mouseover', e => {
      const target = e.target;
      const v = target.closest('.var');
      const n = target.closest('[data-node]');
      const r = target.closest('tr.c, li.step');
      clear();
      if (v) {
        document.querySelectorAll('.var').forEach(x => { if (x.dataset.var === v.dataset.var) light(x); });
        const o = owner[v.dataset.var];
        if (o !== undefined) light(treeNodes[o].row);
      } else if (n) {
        light(treeNodes[+n.dataset.node]?.row);
        light(groups[+n.dataset.node]?.gh);
      } else if (r) {
        const o = t.constraints[+r.dataset.c].node;
        if (o !== null) { light(treeNodes[o].row); light(groups[o]?.gh); }
      }
    });
    // Clicks: a bound with a proof selects it; a node scrolls to its
    // constraints, and a group header to its node.
    on(document, 'click', e => {
      const b = e.target.closest('.bd.link');
      if (b) { e.stopPropagation(); select(b.dataset.proof); return; }
      const nd = e.target.closest('.nd[data-node]');
      if (nd) { treeNodes[+nd.dataset.node].row.scrollIntoView({ behavior: 'smooth', block: 'center' }); return; }
      const n = e.target.closest('.pn[data-node]');
      if (n) {
        const g = groups[+n.dataset.node];
        if (g && !g.body.hidden) g.gh.scrollIntoView({ behavior: 'smooth', block: 'start' });
        return;
      }
      const h = e.target.closest('tr.gh[data-node]');
      if (h) treeNodes[+h.dataset.node].row.scrollIntoView({ behavior: 'smooth', block: 'center' });
    }, true);

    // Pins and row counts used.
    const factRows = [];
    if (informed && pins + facts) {
      $('facts').hidden = false;
      $('facts-n').textContent = `${pins} pins, ${facts} row counts`;
      for (const c of t.constraints.filter(isFact)) {
        const f = c.fact, read = f.facts.flatMap(x => x.origins);
        const r = el('tr');
        for (const [text, cls] of [[f.source, 'note'], [`${c.vars.map(shortName).join(', ')} ${f.value}`, 'm'], [f.facts.map(x => x.text).join(', '), 'm'], [read.length ? read.join(', ') : '—', 'm note']]) r.append(el('td', cls, text));
        $('facts-used').append(r);
        factRows.push(r);
      }
    }

    // The selected proof, and its "why" chain.
    let current = null;
    function select(name) {
      current = (name && proofs[name]) || null;
      for (const [k, b] of Object.entries(claimButtons)) b.classList.toggle('on', k === name);
      for (const [b] of badges) b.classList.toggle('sel', !!current && b.dataset.proof === current.name);
      const core = new Set(current ? current.core : []);
      const perNode = {};
      for (const c of core) { const n = t.constraints[c].node; perNode[n] = (perNode[n] ?? 0) + 1; }
      for (const [id, { row, count }] of Object.entries(treeNodes)) {
        const total = (byNode[id] ?? []).length, k = perNode[id] ?? 0;
        row.classList.toggle('core', k > 0);
        row.classList.toggle('out', !!current && k === 0);
        count.textContent = current ? `${k}/${total}` : String(total);
        count.title = current ? `${k} of this node's ${total} constraints are needed` : `${total} constraints`;
      }
      // Open the reference plans the proof reads from.
      const touched = new Set(Object.keys(perNode).map(n => refOf[n]).filter(x => x));
      for (const [name, r] of Object.entries(refs)) {
        r.head.classList.toggle('core', touched.has(name));
        if (touched.has(name)) setRef(name, true);
      }
      $('only').disabled = !current;
      $('only').parentElement.title = current ? 'Show only the constraints the selected proof needs' : 'Select a proof first';
      why();
      filter();
    }

    function why() {
      const w = $('why');
      w.hidden = !current;
      if (!current) return;
      const p = current, m = p.name.match(nodeProof);
      const what = m ? `node #${m[1]}'s ${m[2]} bound` : `the result's ${p.name} bound`;
      $('why-title').textContent = `Why ${claimText(p.claim)}`;
      const tag = $('why-tag');
      tag.textContent = '';
      if (p.status === 'Proven' && !p.minimal) { const s = el('span', 'tag', 'not minimized'); s.title = 'Z3 could not shrink this set fully: some of these constraints may not be needed.'; tag.append(s); }
      const ex = $('explain'), chain = $('chain');
      chain.textContent = '';
      if (p.status !== 'Proven') {
        ex.textContent = p.status === 'Refuted'
          ? `${claimText(p.claim)} (${what}) does not follow: some assignment satisfies every constraint and breaks it.`
          : `${claimText(p.claim)} (${what}): Z3 could not decide (${p.reason}).`;
        return;
      }
      const n = p.core.length;
      ex.textContent = `${what[0].toUpperCase() + what.slice(1)} follows from ${n === 1 ? 'one constraint' : `these ${n} constraints together; dropping any one leaves it unproven`}. Read from the claim down: each row explains a variable of the rows above it.`;
      const head = el('li', 'claim-row m', claimText(p.claim));
      chain.append(head);
      let prev = -1;
      for (const [cid, depth, via] of p.steps) {
        const c = t.constraints[cid];
        const li = el('li', isFact(c) ? 'step fact' : 'step');
        li.dataset.c = cid;
        const conn = el('span', depth === prev ? 'conn' : 'conn why', depth === prev ? 'and' : 'because');
        conn.title = via.length ? `explains ${via.map(shortName).join(', ')}` : 'shares no variable with the chain';
        const nd = el('span', 'nd m', c.node === null ? 'part' : `#${c.node}`);
        if (c.node !== null) nd.dataset.node = c.node;
        li.append(conn, el('span', 'cid m', 'c' + cid + (isFact(c) ? ' ◆' : '')), formula(c.infix, 'f m', 'span'), el('span', 'rl', ruleOf(c)), nd);
        if (isFact(c)) {
          // A pin's text already names the operator it is read off.
          const read = c.fact.facts.map(f => f.text + (f.origins.some(o => !f.text.includes(o)) ? ` (read off ${f.origins.join(', ')})` : '')).join('; ');
          li.append(el('span', 'read m', read));
        }
        on(li, 'click', e => { if (!e.target.closest('[data-node]')) reveal(cid); });
        chain.append(li);
        prev = depth;
      }
    }

    // Shows constraint `id` in the list, and flashes it.
    function reveal(id) {
      const c = t.constraints[id];
      const key = c.node ?? 'p';
      if (refOf[key] && !refs[refOf[key]].open) setRef(refOf[key], true);
      buildGroup(key);
      groups[key].unfold = true;
      filter();
      const r = rows[id].r;
      r.scrollIntoView({ behavior: 'smooth', block: 'center' });
      r.classList.add('flash');
      setTimeout(() => r.classList.remove('flash'), 1200);
    }

    // Which constraints the list shows: those matching the search; under a
    // proof with "Only needed", its core; else every one, routine rules
    // folded and folded reference plans' left out.
    let texts = null;
    const textOf = c => (texts ??= t.constraints.map(c => [c.infix, c.smt, c.function, c.source, c.code,
      ...(c.fact ? c.fact.facts.flatMap(f => [f.text, ...f.origins]) : []), ...c.vars.map(v => `${names[v] ?? v} ${shortName(v)}`)].join(' ').toLowerCase()))[c.id];
    function filter() {
      const q = $('search').value.trim().toLowerCase();
      const only = $('only').checked && current;
      const core = new Set(current ? current.core : []);
      let shown = 0;
      for (const key of groupKeys) {
        const g = groups[key];
        const refFolded = refOf[key] && !refs[refOf[key]].open;
        const show = [], folded = [];
        for (const c of byNode[key]) {
          const inCore = core.has(c.id);
          if (q && !textOf(c).includes(q)) continue;
          if (only && !inCore) continue;
          if (!q && !only && refFolded) continue;
          if (!q && !inCore && !g.unfold && ROUTINE.has(c.function)) { folded.push(c); continue; }
          show.push(c);
        }
        g.body.hidden = !show.length && !folded.length;
        if (g.body.hidden) continue;
        buildGroup(key);
        const vis = new Set(show.map(c => c.id));
        for (const c of byNode[key]) {
          const { r, x } = rows[c.id];
          r.hidden = !vis.has(c.id);
          if (r.hidden) x.hidden = true;
          r.classList.toggle('core', core.has(c.id));
        }
        shown += show.length;
        g.fold.hidden = !folded.length;
        if (folded.length) {
          const kinds = [...new Set(folded.map(c => c.function))].join(', ');
          g.ftd.textContent = `+ ${folded.length} routine bound${folded.length === 1 ? '' : 's'} (${kinds}): show`;
        }
      }
      const count = $('count');
      count.textContent = '';
      if (current) count.append(el('span', 'sel', claimText(current.claim)), current.status === 'Proven' ? `: ${current.core.length} needed · ` : ` · `);
      count.append(`${num(shown)} of ${num(t.constraints.length)} shown`);
      for (const r of factRows) r.hidden = !!q && !r.textContent.toLowerCase().includes(q);
    }

    // The constraints as an SMT-LIB script, as `Trace::to_smt2` writes it.
    function smt2() {
      let s = '; cardinal constraints\n' + t.declarations;
      for (const c of t.constraints) {
        const owner = c.node === null ? 'partition' : `node ${c.node} ${t.nodes[c.node].label.replace(/\n/g, ' ')}`;
        s += `; [c${c.id}] ${owner} (${c.source} ${c.function})\n(assert ${c.smt})\n`;
      }
      return s;
    }

    on($('search'), 'input', filter);
    on($('only'), 'change', filter);
    on($('clear'), 'click', () => { $('only').checked = false; select(null); });
    on($('hide'), 'change', () => mount($('hide').checked, { proof: current?.name, search: $('search').value, only: $('only').checked }));
    on($('copy'), 'click', async () => {
      try { await navigator.clipboard.writeText(smt2()); $('copy').textContent = 'Copied'; }
      catch { $('copy').textContent = 'Copy failed'; }
      setTimeout(() => { $('copy').textContent = 'Copy SMT-LIB'; }, 1500);
    });
    on($('save'), 'click', () => {
      const a = el('a');
      a.href = URL.createObjectURL(new Blob([smt2()], { type: 'text/plain' }));
      a.download = 'cardinal.smt2';
      a.click();
    });

    $('search').value = keep.search ?? '';
    $('only').checked = !!keep.only;
    const first = rootProofs.find(p => p.name === 'upper' && p.status === 'Proven') ?? rootProofs.find(p => p.status === 'Proven');
    select(keep.proof === null ? null : proofs[keep.proof] ? keep.proof : first?.name);
  }

  mount(!!D.plain, { proof: D.proof ?? undefined, only: true });
})();
</script>
</body>
</html>
"##;
