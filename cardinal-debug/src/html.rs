//! A dump as one self-contained HTML page: the plan tree beside its
//! constraints, linked both ways, with a selector that picks out the
//! constraints each proof needs, and with facts, which were used and which
//! not.

use serde_json::json;

use crate::{Dump, column_names};

/// The page for `dump`, opened on proof `proof` if given, and with its fact
/// constraints hidden if `without_facts`.
pub fn render(dump: &Dump, proof: Option<&str>, without_facts: bool) -> String {
    let trace = dump.facts.as_ref().map_or(&dump.trace, |f| &f.trace);
    let data = json!({
        "dump": dump,
        "names": column_names(trace),
        "smt2": trace.to_smt2(),
        "proof": proof,
        "withoutFacts": without_facts,
    });
    // Keep `</script>` in the data from closing the tag it sits in.
    let data = data.to_string().replace("</", "<\\/");
    TEMPLATE.replace("__DATA__", &data)
}

const TEMPLATE: &str = r##"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Cardinal Z3 Trace</title>
<style>
:root {
  --bg: #ffffff; --sub: #f5f5f4; --ink: #111111; --muted: #666666; --faint: #a3a3a3;
  --rule: #d4d4d4; --rule-soft: #ececec;
  --accent: #1d4ed8; --accent-bg: #e8eefc; --hl: #fff4b8;
  --good: #166534; --bad: #b91c1c; --warn: #92400e;
  color-scheme: light;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #121212; --sub: #1b1b1b; --ink: #ececec; --muted: #a0a0a0; --faint: #6b6b6b;
    --rule: #3a3a3a; --rule-soft: #262626;
    --accent: #7aa2ff; --accent-bg: #1c2740; --hl: #4a4115;
    --good: #6ee7a0; --bad: #ff8a8a; --warn: #f5c26b;
    color-scheme: dark;
  }
}
:root[data-theme="dark"] {
  --bg: #121212; --sub: #1b1b1b; --ink: #ececec; --muted: #a0a0a0; --faint: #6b6b6b;
  --rule: #3a3a3a; --rule-soft: #262626;
  --accent: #7aa2ff; --accent-bg: #1c2740; --hl: #4a4115;
  --good: #6ee7a0; --bad: #ff8a8a; --warn: #f5c26b;
  color-scheme: dark;
}
* { box-sizing: border-box; }
html, body { margin: 0; background: var(--bg); color: var(--ink); }
body { font: 13px/1.45 -apple-system, system-ui, "Segoe UI", sans-serif; }
code, pre, .m { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 12px; }
pre { margin: 0; white-space: pre-wrap; overflow-wrap: anywhere; }
h1 { font-size: 15px; margin: 0 0 10px; }
h2 { font-size: 11px; font-weight: 600; text-transform: uppercase; letter-spacing: .06em; color: var(--muted); margin: 0 0 6px; }
.help { color: var(--muted); margin: 0 0 8px; max-width: 80ch; }
section, header { padding: 14px 16px; border-bottom: 1px solid var(--rule); }
table { border-collapse: collapse; width: 100%; }
th { text-align: left; font-weight: 600; color: var(--muted); }
details > summary { cursor: pointer; color: var(--muted); margin-top: 8px; }
details pre { margin-top: 6px; padding: 8px; background: var(--sub); border: 1px solid var(--rule-soft); max-height: 24em; overflow: auto; }

/* Summary */
table.kv th { width: 7.5em; padding: 3px 12px 3px 0; vertical-align: top; }
table.kv td { padding: 3px 0; vertical-align: top; }
table.kv pre { max-height: 10em; overflow: auto; }
.status { font-weight: 700; }
.good { color: var(--good); } .bad { color: var(--bad); } .warn { color: var(--warn); }
.note { color: var(--muted); }

/* Proofs */
table.proofs th, table.proofs td { padding: 4px 10px 4px 0; border-bottom: 1px solid var(--rule-soft); vertical-align: top; }
table.proofs thead th { border-bottom: 1px solid var(--rule); font-size: 12px; }
table.proofs tbody tr { cursor: pointer; }
table.proofs tbody tr:hover { background: var(--sub); }
table.proofs tbody tr.on { background: var(--accent-bg); box-shadow: inset 3px 0 0 var(--accent); }
table.proofs td:first-child { padding-left: 8px; width: 6.5em; }
table.proofs .num { text-align: right; width: 6em; }
#explain { margin: 8px 0 0; padding: 6px 8px; border-left: 3px solid var(--accent); background: var(--sub); }

/* Toolbar */
.toolbar { display: flex; flex-wrap: wrap; gap: 8px 16px; align-items: center; padding: 8px 16px;
  border-bottom: 1px solid var(--rule); background: var(--bg); position: sticky; top: 0; z-index: 3; }
.toolbar input[type=search] { font: inherit; padding: 3px 6px; width: 18em; max-width: 100%;
  border: 1px solid var(--rule); background: var(--bg); color: var(--ink); }
.toolbar button { font: inherit; padding: 3px 10px; border: 1px solid var(--rule); background: var(--sub); color: var(--ink); cursor: pointer; }
.toolbar button:hover { border-color: var(--muted); }
.toolbar .count { margin-left: auto; color: var(--muted); }
.toolbar .sel { color: var(--accent); font-weight: 600; }

/* Body */
main { display: grid; grid-template-columns: minmax(280px, 34%) 1fr; }
@media (max-width: 860px) {
  main { grid-template-columns: 1fr; }
  .plan { position: static !important; max-height: none !important; border-right: 0 !important; border-bottom: 1px solid var(--rule); }
  table.cs col.rule, table.cs td.rule, table.cs th.rule { display: none; }
}
.plan { padding: 14px 12px 14px 16px; border-right: 1px solid var(--rule); position: sticky; top: 41px;
  max-height: calc(100vh - 41px); overflow: auto; }
.plan ul { list-style: none; margin: 0; padding: 0 0 0 14px; border-left: 1px solid var(--rule); }
.plan > ul { padding-left: 0; border-left: 0; }
.plan li { margin: 0; }
.pn { display: grid; grid-template-columns: auto 1fr auto; gap: 0 6px; padding: 3px 6px; margin: 1px 0; cursor: pointer; border-left: 3px solid transparent; }
.pn:hover, .pn.hl { background: var(--hl); }
.pn .id { color: var(--muted); }
.pn .op { overflow-wrap: anywhere; }
.pn .op b { font-weight: 600; }
.pn .op .d { color: var(--muted); display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; }
.pn .op .v { color: var(--muted); }
.pn .n { color: var(--muted); text-align: right; white-space: nowrap; }
.pn.core { border-left-color: var(--accent); background: var(--accent-bg); }
.pn.core .n { color: var(--accent); font-weight: 600; }
.pn.out { color: var(--faint); }
.pn.out .d, .pn.out .id, .pn.out .v { color: var(--faint); }
.sub { color: var(--muted); font-style: italic; padding: 6px 0 2px; }

.list { padding: 14px 16px; min-width: 0; }
table.cs { table-layout: fixed; }
table.cs col.id { width: 4.5em; } table.cs col.rule { width: 15em; } table.cs col.src { width: 8.5em; }
table.cs thead th { position: sticky; top: 41px; background: var(--bg); border-bottom: 1px solid var(--rule); padding: 4px 8px 4px 0; font-size: 12px; z-index: 1; }
table.cs td { padding: 2px 8px 2px 0; border-bottom: 1px solid var(--rule-soft); vertical-align: top; overflow-wrap: anywhere; }
table.cs td.id { padding-left: 6px; color: var(--muted); }
table.cs td.rule, table.cs td.src { color: var(--muted); }
table.cs td.src { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
tr.gh td { padding: 10px 6px 4px; border-bottom: 1px solid var(--rule); background: var(--bg); cursor: pointer; }
tr.gh td b { font-weight: 600; }
tr.gh .d, tr.gh .v { color: var(--muted); }
tr.gh.hl td { background: var(--hl); }
tr.c { cursor: pointer; }
tr.c:hover td { background: var(--sub); }
tr.c.hl td { background: var(--hl); }
tr.c.core td.id { box-shadow: inset 3px 0 0 var(--accent); color: var(--accent); font-weight: 600; }
tr.c.core td.f { font-weight: 600; }
tr.c.out td { color: var(--faint); }
tr.c.out td.f .var { color: var(--faint); }
tr.x td { padding: 4px 8px 8px 6px; background: var(--sub); border-bottom: 1px solid var(--rule); }
tr.x th { color: var(--muted); font-weight: 400; width: 5em; padding: 2px 8px 2px 0; vertical-align: top; }
tr.x table td { background: none; border: 0; padding: 2px 0; }
.var { border-bottom: 1px dotted var(--faint); }
.var.hl { background: var(--hl); }
[hidden] { display: none !important; }

/* Facts */
.fm { color: var(--accent); }
tr.c.fact td.id { color: var(--accent); }
tr.c.fact td.rule { font-style: italic; }
table.proofs .grp { border-left: 1px solid var(--rule); padding-left: 10px; }
table.facts { margin: 4px 0 12px; }
table.facts th, table.facts td { padding: 3px 10px 3px 0; border-bottom: 1px solid var(--rule-soft); vertical-align: top; overflow-wrap: anywhere; }
table.facts thead th { border-bottom: 1px solid var(--rule); font-size: 12px; }
h3 { font-size: 12px; font-weight: 600; margin: 10px 0 2px; }

footer { padding: 14px 16px 24px; color: var(--muted); border-top: 1px solid var(--rule); }
footer dl { display: grid; grid-template-columns: max-content 1fr; gap: 2px 14px; margin: 0; }
footer dt { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 12px; color: var(--ink); }
footer dd { margin: 0; }
</style>
</head>
<body>
<header>
  <h1>cardinal — Z3 constraint trace</h1>
  <table class="kv">
    <tr><th>Verdict</th><td><span id="verdict" class="status"></span> <span id="verdict-note" class="note"></span></td></tr>
    <tr><th id="bounds-label">Bounds</th><td><code id="bounds"></code></td></tr>
    <tr id="fbounds-row" hidden><th id="fbounds-label">With facts</th><td><code id="fbounds"></code></td></tr>
    <tr id="facts-row" hidden><th>Facts</th><td id="facts-stats"></td></tr>
    <tr><th>Size</th><td id="stats"></td></tr>
    <tr><th>Query</th><td><pre id="query"></pre></td></tr>
  </table>
  <details><summary>Optimized plan (DataFusion)</summary><pre id="plan"></pre></details>
  <details id="cxbox" hidden open><summary>Counterexample: values satisfying every constraint with X &gt; Σ</summary>
    <pre id="cx"></pre></details>
</header>

<section>
  <h2>Proofs</h2>
  <p class="help">Each claim is re-proven from the constraints. Select one to mark the smallest set of constraints that proves it: removing any one of them makes the claim unprovable.</p>
  <table class="proofs">
    <thead id="proofs-head"></thead>
    <tbody id="proofs"></tbody>
  </table>
  <p id="explain" hidden></p>
</section>

<section id="facts" hidden>
  <h2>Facts</h2>
  <p class="help">What the facts gave: each fact constraint (◆) holds a variable to a value read off a plan that ran. Facts not used were rejected (they contradict the constraints), not decided in time, or not found.</p>
  <h3>Used</h3>
  <table class="facts"><thead><tr><th>Selectivity</th><th>Value</th><th>From facts</th><th>Read off</th></tr></thead><tbody id="facts-used"></tbody></table>
  <h3>Not used</h3>
  <table class="facts"><thead><tr><th>Why</th><th>What</th><th>Reason</th></tr></thead><tbody id="facts-unused"></tbody></table>
  <div id="conflicts-box" hidden>
    <h3>Conflicts (left out)</h3>
    <table class="facts"><tbody id="conflicts"></tbody></table>
  </div>
</section>

<div class="toolbar">
  <label><input type="checkbox" id="only"> Only constraints the selected proof needs</label>
  <label id="hide-label" hidden><input type="checkbox" id="hide"> Hide fact constraints</label>
  <input type="search" id="search" placeholder="Filter: text, variable, rule…" aria-label="Filter constraints">
  <button id="copy">Copy SMT-LIB</button>
  <button id="save">Save .smt2</button>
  <span class="count" id="count"></span>
</div>

<main>
  <nav class="plan" aria-label="Plan">
    <h2>Plan <span class="note" style="text-transform:none;letter-spacing:0;font-weight:400">· root first · count = constraints</span></h2>
    <div id="tree"></div>
  </nav>
  <div class="list">
    <h2>Constraints, by plan node</h2>
    <table class="cs">
      <colgroup><col class="id"><col><col class="rule"><col class="src"></colgroup>
      <thead><tr><th style="padding-left:6px">#</th><th>Constraint</th><th class="rule">Rule (analyzer function)</th><th class="src">Source</th></tr></thead>
      <tbody id="list"></tbody>
    </table>
  </div>
</main>

<footer>
  <h2>Notation</h2>
  <dl>
    <dt>X</dt><dd>Rows output by the root operator.</dd>
    <dt>Σ</dt><dd>Sum of the rows read by every base-table scan.</dd>
    <dt>|t|, T{n}_{t}</dt><dd>Rows in base table t.</dd>
    <dt>op{n}_{Kind}</dt><dd>Rows output by plan node n.</dd>
    <dt>op{n}_{Kind}[col]</dt><dd>Distinct values of column col in node n's output (NULL counts as one).</dd>
    <dt>part{n}</dt><dd>Rows of a table shared by relations whose rows are disjoint.</dd>
    <dt>◆</dt><dd>A constraint a fact gave, or a node with one.</dd>
    <dt>a·b, min, max, =&gt;, ∧, ∨, ¬</dt><dd>Product, minimum, maximum, implication, and, or, not.</dd>
  </dl>
</footer>

<script type="application/json" id="data">__DATA__</script>
<script>
(() => {
  const D = JSON.parse(document.getElementById('data').textContent);
  const dump = D.dump, F = dump.facts, t = F ? F.trace : dump.trace, names = D.names;
  // The proofs to select: with facts if they were proven, else the base
  // ones, whose constraints come first in the trace with facts too.
  const proofs = F && F.explained ? F.proofs : dump.proofs;
  const baseOf = {};
  if (F && F.explained) F.proofs.forEach((p, i) => { if (F.base_proofs[i]) baseOf[p.name] = F.base_proofs[i]; });
  const isFact = c => !!c.fact;
  const $ = id => document.getElementById(id);
  const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; };
  const statusOf = p => typeof p.status === 'string' ? p.status : 'Unknown';

  // Summary.
  $('query').textContent = dump.query.trim();
  $('plan').textContent = dump.plan;
  const verdictNote = {
    Reduces: 'proven: the output never has more rows than the scans read (X <= Σ)',
    MightGrow: 'not provable: an assignment satisfies every constraint with X > Σ (see counterexample)',
  };
  $('verdict').textContent = dump.verdict.split(':')[0];
  $('verdict').classList.add(dump.verdict === 'Reduces' ? 'good' : dump.verdict === 'MightGrow' ? 'bad' : 'warn');
  $('verdict-note').textContent = verdictNote[dump.verdict] ?? dump.verdict;
  $('bounds').textContent = dump.bounds ?? 'not computed';
  if (F) {
    $('bounds-label').textContent = 'Without facts';
    $('fbounds-row').hidden = false;
    $('fbounds-label').textContent = `With facts (${F.mode})`;
    $('fbounds').textContent = F.bounds ?? 'not computed';
    $('facts-row').hidden = false;
    const k = t.constraints.filter(isFact).length;
    $('facts-stats').textContent = `${k} fact constraints, ${F.report.matched.length} selectivities matched, ` +
      `${F.report.rejected.length} rejected · X = ${F.report.output}`;
    $('hide-label').hidden = false;
  }
  const partitions = t.constraints.filter(c => c.node === null).length;
  $('stats').textContent = `${t.nodes.length} plan nodes, ${t.constraints.length} constraints` +
    (partitions ? ` (${partitions} over table partitions)` : '') + `, root variable ${t.root}`;
  if (dump.counterexample) {
    $('cxbox').hidden = false;
    const rows = Object.entries(dump.counterexample).map(([k, v]) => [names[k] ?? k, v]);
    const w = Math.max(...rows.map(([k]) => k.length));
    $('cx').textContent = rows.map(([k, v]) => k.padEnd(w + 2) + v).join('\n');
  }

  // The node each variable describes.
  const owner = {};
  for (const n of t.nodes) {
    owner[n.var] = n.id;
    if (n.raw_var) owner[n.raw_var] = n.id;
    for (const [, nv] of n.columns) owner[nv] = n.id;
  }
  const isVar = s => owner[s] !== undefined || t.tables.some(([, sym]) => sym === s) || /^part\d+$/.test(s);
  const byNode = {};
  for (const c of t.constraints) (byNode[c.node ?? 'p'] ??= []).push(c);

  // An operator's label: its kind in bold, the rest muted.
  function opLabel(n, cls) {
    const line = n.label.split('\n')[0];
    const i = line.indexOf(':');
    const box = el('span', cls);
    box.append(el('b', null, i < 0 ? line : line.slice(0, i)));
    if (i >= 0) box.append(el('span', 'd m', line.slice(i + 1).trim()));
    return box;
  }

  // Plan tree, root first; nodes no other node takes as input are roots.
  const used = new Set(t.nodes.flatMap(n => n.inputs));
  const roots = t.nodes.filter(n => !used.has(n.id)).map(n => n.id).reverse();
  const treeNodes = {}, order = [];
  function build(id) {
    const n = t.nodes[id];
    order.push(id);
    const li = el('li');
    const row = el('div', 'pn');
    row.dataset.node = id;
    row.title = n.label;
    const op = opLabel(n, 'op');
    let v = n.var;
    if (F) {
      const mine = [n.var, n.raw_var].filter(x => x);
      for (const [list, o] of [[F.report.pinned, '='], [F.report.capped, '<=']])
        for (const [x, k] of list) if (mine.includes(x)) v += `  ${x === n.var ? '' : (names[x] ?? x) + ' '}${o} ${k}`;
    }
    op.append(el('div', 'v m', v));
    const count = el('span', 'n m');
    const idBox = el('span', 'id m', `[${id}]`);
    if ((byNode[id] ?? []).some(isFact)) idBox.append(el('span', 'fm', ' ◆'));
    row.append(idBox, op, count);
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
  roots.forEach((r, i) => {
    if (i > 0) top.append(el('li', 'sub', 'Subquery inside an expression:'));
    top.append(build(r));
  });
  $('tree').append(top);

  // A formula, each variable named by its column and linked to its node.
  function formula(text) {
    const f = el('td', 'f m');
    for (const part of text.split(/([A-Za-z0-9_]+)/)) {
      if (!part) continue;
      if (isVar(part)) {
        const s = el('span', 'var', names[part] ?? part);
        s.dataset.var = part;
        s.title = part;
        f.append(s);
      } else {
        f.append(document.createTextNode(part));
      }
    }
    return f;
  }

  // Constraint table: one header row per node, then its constraints.
  const heads = {}, rows = {};
  function group(key) {
    const cs = byNode[key] ?? [];
    if (!cs.length) return;
    const gh = el('tr', 'gh');
    const td = el('td');
    td.colSpan = 4;
    if (key === 'p') {
      td.append(el('b', null, 'Table partitions'), el('span', 'd', ' — relations of one table with disjoint rows share its rows'));
    } else {
      const n = t.nodes[key];
      td.append(el('span', 'm', `[${key}] `), opLabel(n), el('span', 'v m', '  ' + n.var));
      gh.dataset.node = key;
    }
    gh.append(td);
    heads[key] = gh;
    $('list').append(gh);
    for (const c of cs) {
      const r = el('tr', isFact(c) ? 'c fact' : 'c');
      r.dataset.c = c.id;
      const file = c.source.split('/').pop();
      const src = el('td', 'src m', isFact(c) ? 'fact' : file);
      src.title = c.source;
      r.append(el('td', 'id m', 'c' + c.id + (isFact(c) ? ' ◆' : '')), formula(c.infix), el('td', 'rule m', c.function), src);
      const x = el('tr', 'x');
      x.hidden = true;
      const xd = el('td');
      xd.colSpan = 4;
      const kv = el('table');
      const details = [['SMT-LIB', c.smt], ['Made by', `${c.function} at ${c.source}`], ['Code', c.code]];
      if (isFact(c)) {
        details.push(['Asserts', `${names[c.vars[0]] ?? c.vars[0] ?? ''} ${c.fact.value}`]);
        for (const f of c.fact.facts) details.push(['Fact', f.text + (f.origins.length ? `\nread off ${f.origins.join(', ')}` : '')]);
      }
      for (const [k, v] of details) {
        const tr = el('tr');
        const val = el('td');
        val.append(el('pre', null, v));
        tr.append(el('th', null, k), val);
        kv.append(tr);
      }
      xd.append(kv);
      x.append(xd);
      r.addEventListener('click', () => { x.hidden = !x.hidden; });
      rows[c.id] = { r, x };
      $('list').append(r, x);
    }
  }
  for (const id of order) group(id);
  group('p');

  // Hover: a node lights its constraints' header and its tree entry; a
  // variable lights every use of it and the node it describes.
  const lit = [];
  const light = e => { if (e) { e.classList.add('hl'); lit.push(e); } };
  const clear = () => { while (lit.length) lit.pop().classList.remove('hl'); };
  document.addEventListener('mouseover', e => {
    const target = e.target;
    const v = target.closest('.var');
    const n = target.closest('[data-node]');
    const r = target.closest('tr.c');
    clear();
    if (v) {
      document.querySelectorAll('.var').forEach(x => { if (x.dataset.var === v.dataset.var) light(x); });
      const o = owner[v.dataset.var];
      if (o !== undefined) light(treeNodes[o].row);
    } else if (n) {
      light(treeNodes[+n.dataset.node]?.row);
      light(heads[+n.dataset.node]);
    } else if (r) {
      const o = t.constraints[+r.dataset.c].node;
      if (o !== null) { light(treeNodes[o].row); light(heads[o]); }
    }
  });
  $('tree').addEventListener('click', e => {
    const n = e.target.closest('[data-node]');
    const h = n && heads[+n.dataset.node];
    if (h && !h.hidden) h.scrollIntoView({ behavior: 'smooth', block: 'start' });
  });
  $('list').addEventListener('click', e => {
    const h = e.target.closest('tr.gh');
    if (h && h.dataset.node !== undefined) treeNodes[+h.dataset.node].row.scrollIntoView({ behavior: 'smooth', block: 'center' });
  });

  // Facts: used, not used, conflicts.
  const factRows = [];
  if (F) {
    $('facts').hidden = false;
    const row = (body, cells) => {
      const r = el('tr');
      for (const [text, cls] of cells) r.append(el('td', cls, text));
      $(body).append(r);
      factRows.push(r);
    };
    for (const m of F.report.matched) {
      const read = m.facts.flatMap(f => f.origins);
      row('facts-used', [[m.name, 'm'], [m.value, 'm'], [m.facts.map(f => f.text).join(', '), 'm'], [read.length ? read.join(', ') : '—', 'm note']]);
    }
    const counts = [['pinned', F.report.pinned], ['capped', F.report.capped], ['ndv', F.report.pinned_ndv], ['ranges', F.report.ranges || []], ['floors', F.report.floors]];
    for (const [k, list] of counts)
      for (const [v, n] of list) row('facts-used', [[k, 'note'], [`${names[v] ?? v} ${k === 'capped' ? '<=' : k === 'floors' ? '>=' : '='} ${n}`, 'm'], ['row count from a fact (◆ in the constraints)', 'note'], ['', '']]);
    for (const [s, why] of F.report.rejected) row('facts-unused', [['rejected', 'bad'], [s, 'm'], [why, '']]);
    for (const s of F.report.unchecked) row('facts-unused', [['unchecked', 'warn'], [s, 'm'], ['not decided in time', '']]);
    for (const [s, why] of F.report.unmatched) row('facts-unused', [['unmatched', 'note'], [s, 'm'], [why, '']]);
    if (!$('facts-unused').children.length) row('facts-unused', [['—', 'note'], ['every fact found was used', 'note'], ['', '']]);
    if (F.conflicts.length) {
      $('conflicts-box').hidden = false;
      for (const c of F.conflicts) row('conflicts', [[c, 'm']]);
    }
  }

  // Proofs.
  let current = null;
  const proofRows = {};
  const statusLabel = { Proven: ['proven', 'good'], Refuted: ['refuted', 'bad'], Unknown: ['unknown', 'warn'] };
  const all = el('tr');
  const compare = !!(F && F.explained);
  {
    const h = el('tr');
    for (const [text, cls] of compare
      ? [['Status', ''], ['Name', ''], ['Claim', ''], ['Without facts', 'grp'], ['Needs', 'num'], ['With facts', 'grp'], ['Needs', 'num'], ['Facts', 'num'], ['From nodes', '']]
      : [['Status', ''], ['Name', ''], ['Claim', ''], ['Needs', 'num'], ['From nodes', '']]) h.append(el('th', cls, text));
    $('proofs-head').append(h);
  }
  const needs = p => statusOf(p) === 'Proven' ? String(p.core.length) : '—';
  const cell = (p, grp) => {
    const [label, cls] = statusLabel[statusOf(p)];
    return el('td', `status ${cls}${grp ? ' grp' : ''}`, label);
  };
  {
    const blank = compare ? 6 : 2;
    all.append(el('td', 'note', '—'), el('td', null, 'none'), el('td', 'note', 'Show every constraint'));
    for (let i = 0; i < blank; i++) all.append(el('td', 'note', ''));
  }
  all.addEventListener('click', () => select(null));
  $('proofs').append(all);
  for (const p of proofs) {
    const nodes = [...new Set(p.core.map(c => t.constraints[c].node).filter(n => n !== null))].sort((a, b) => a - b);
    const r = el('tr');
    r.append(cell(p), el('td', 'm', p.name), el('td', 'm', p.claim));
    if (compare) {
      const b = baseOf[p.name];
      const k = statusOf(p) === 'Proven' ? p.core.filter(c => isFact(t.constraints[c])).length : null;
      r.append(
        b ? cell(b, true) : el('td', 'note grp', '—'),
        el('td', 'num m', b ? needs(b) : '—'),
        cell(p, true),
        el('td', 'num m', needs(p)),
        el('td', 'num m', k === null ? '—' : String(k)),
      );
    } else {
      r.append(el('td', 'num m', needs(p)));
    }
    r.append(el('td', 'm note', nodes.length ? nodes.map(n => `[${n}]`).join(' ') : '—'));
    if (statusOf(p) === 'Unknown') r.title = p.status.Unknown;
    r.addEventListener('click', () => select(p.name));
    proofRows[p.name] = r;
    $('proofs').append(r);
  }

  // With fact constraints hidden, a proof's core is the one without them.
  const hiding = () => !!F && $('hide').checked;
  function select(name) {
    current = (hiding() && compare ? baseOf[name] : null) ?? proofs.find(p => p.name === name) ?? null;
    all.classList.toggle('on', !current);
    for (const [k, r] of Object.entries(proofRows)) r.classList.toggle('on', k === name);
    const core = new Set(current ? current.core : []);
    const perNode = {};
    for (const c of core) { const n = t.constraints[c].node; perNode[n] = (perNode[n] ?? 0) + 1; }
    for (const [id, { r }] of Object.entries(rows)) {
      r.classList.toggle('core', core.has(+id));
      r.classList.toggle('out', !!current && !core.has(+id));
    }
    for (const [id, { row, count }] of Object.entries(treeNodes)) {
      const total = (byNode[id] ?? []).filter(c => !(hiding() && isFact(c))).length;
      const k = perNode[id] ?? 0;
      row.classList.toggle('core', k > 0);
      row.classList.toggle('out', !!current && k === 0);
      count.textContent = current ? `${k}/${total}` : String(total);
      count.title = current ? `${k} of this node's ${total} constraints are needed` : `${total} constraints`;
    }
    const ex = $('explain');
    ex.hidden = !current;
    if (current) {
      const s = statusOf(current);
      ex.textContent = s === 'Proven'
        ? (current.core.length === 1
            ? `${current.claim} follows from one constraint, marked below.`
            : `${current.claim} follows from the ${current.core.length} constraints marked below, taken together; dropping any one of them leaves it unproven.`)
        : s === 'Refuted'
          ? `${current.claim} does not follow: some assignment satisfies every constraint and breaks it.`
          : `${current.claim}: Z3 could not decide (${current.status.Unknown}).`;
    }
    filter();
  }

  function filter() {
    const q = $('search').value.trim().toLowerCase();
    const only = $('only').checked && current;
    const core = new Set(current ? current.core : []);
    let shown = 0;
    for (const [id, { r, x }] of Object.entries(rows)) {
      const c = t.constraints[+id];
      const origins = c.fact ? c.fact.facts.flatMap(f => [f.text, ...f.origins]) : [];
      const text = [c.infix, c.smt, c.function, c.source, c.code, ...origins, ...c.vars.map(v => names[v] ?? v)].join(' ').toLowerCase();
      const hide = (q && !text.includes(q)) || (only && !core.has(+id)) || (hiding() && isFact(c));
      r.hidden = hide;
      if (hide) x.hidden = true;
      if (!hide) shown++;
    }
    for (const [key, h] of Object.entries(heads)) h.hidden = !(byNode[key] ?? []).some(c => !rows[c.id].r.hidden);
    const count = $('count');
    count.textContent = '';
    if (current) {
      const s = statusOf(current);
      count.append(el('span', 'sel', current.name), s === 'Proven' ? `: ${current.core.length} needed · ` : `: ${s.toLowerCase()} · `);
    }
    count.append(`${shown} of ${t.constraints.length} constraints shown`);
    for (const r of factRows) r.hidden = !!q && !r.textContent.toLowerCase().includes(q);
  }
  $('search').addEventListener('input', filter);
  $('only').addEventListener('change', filter);
  $('hide').addEventListener('change', () => select(current ? current.name : null));

  $('copy').addEventListener('click', async () => {
    try { await navigator.clipboard.writeText(D.smt2); $('copy').textContent = 'Copied'; }
    catch { $('copy').textContent = 'Copy failed'; }
    setTimeout(() => { $('copy').textContent = 'Copy SMT-LIB'; }, 1500);
  });
  $('save').addEventListener('click', () => {
    const a = el('a');
    a.href = URL.createObjectURL(new Blob([D.smt2], { type: 'text/plain' }));
    a.download = 'cardinal.smt2';
    a.click();
  });

  if (D.proof) $('only').checked = true;
  if (D.withoutFacts) $('hide').checked = true;
  select(D.proof ?? null);
})();
</script>
</body>
</html>
"##;
