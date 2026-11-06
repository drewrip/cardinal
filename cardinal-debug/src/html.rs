//! A dump as one self-contained HTML page: the result's bounds, the plan tree
//! with every operator's bounds beside its constraints, linked both ways, and
//! a selector that picks out the constraints each proof needs. With facts,
//! the page can switch to the analysis without them.

use serde_json::json;

use crate::{Dump, column_names};

/// The page for `dump`, opened on proof `proof` if given, and without its
/// facts if `without_facts`.
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
<title>Cardinal Trace</title>
<style>
:root {
  --bg: #ffffff; --sub: #f6f6f5; --ink: #18181b; --muted: #6b6b70; --faint: #a8a8ad;
  --rule: #dcdcdf; --rule-soft: #efeff1;
  --accent: #1d4ed8; --accent-bg: #eaf0fd; --hl: #fff4bf;
  --good: #166534; --bad: #b91c1c; --open: #b45309; --open-bg: #fdf3e4;
  color-scheme: light;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #131315; --sub: #1c1c1f; --ink: #ececee; --muted: #9d9da3; --faint: #646469;
    --rule: #34343a; --rule-soft: #24242a;
    --accent: #7aa2ff; --accent-bg: #1b2540; --hl: #46401a;
    --good: #6ee7a0; --bad: #ff8a8a; --open: #f2b866; --open-bg: #3a2c16;
    color-scheme: dark;
  }
}
:root[data-theme="dark"] {
  --bg: #131315; --sub: #1c1c1f; --ink: #ececee; --muted: #9d9da3; --faint: #646469;
  --rule: #34343a; --rule-soft: #24242a;
  --accent: #7aa2ff; --accent-bg: #1b2540; --hl: #46401a;
  --good: #6ee7a0; --bad: #ff8a8a; --open: #f2b866; --open-bg: #3a2c16;
  color-scheme: dark;
}
* { box-sizing: border-box; }
html, body { margin: 0; background: var(--bg); color: var(--ink); }
body { font: 13px/1.45 -apple-system, system-ui, "Segoe UI", sans-serif; }
code, pre, .m { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 12px; }
pre { margin: 0; white-space: pre-wrap; overflow-wrap: anywhere; }
h2 { font-size: 11px; font-weight: 600; text-transform: uppercase; letter-spacing: .06em; color: var(--muted); margin: 0 0 8px; }
section, header { padding: 14px 16px; border-bottom: 1px solid var(--rule); }
table { border-collapse: collapse; width: 100%; }
th { text-align: left; font-weight: 600; color: var(--muted); }
details > summary { cursor: pointer; color: var(--muted); width: max-content; }
details > summary:hover { color: var(--ink); }
details[open] > summary { margin-bottom: 6px; }
details pre { padding: 8px; background: var(--sub); border: 1px solid var(--rule-soft); max-height: 24em; overflow: auto; }
.note { color: var(--muted); }
.good { color: var(--good); } .bad { color: var(--bad); } .warn { color: var(--open); }
[hidden] { display: none !important; }
body.nofacts .fm { display: none; }

/* Bounds: a closed range in bold, one with no upper end in amber. */
.bd { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-weight: 600; white-space: nowrap; }
.bd.open { color: var(--open); font-weight: 500; }
.pn .bd, tr.gh .bd { font-size: 12px; padding: 0 6px; border-radius: 3px; background: var(--sub); }
.pn .bd.open, tr.gh .bd.open { background: var(--open-bg); }

/* Header */
.top { display: flex; flex-wrap: wrap; align-items: baseline; gap: 4px 12px; margin-bottom: 12px; }
h1 { font-size: 15px; margin: 0; }
.cards { display: flex; flex-wrap: wrap; gap: 10px; margin-bottom: 12px; }
.card { border: 1px solid var(--rule); border-radius: 4px; padding: 8px 14px; min-width: 12em; }
.card .k { font-size: 11px; color: var(--muted); }
.card .bd { display: block; font-size: 20px; line-height: 1.3; }
.card .was { color: var(--muted); font-size: 12px; min-height: 1em; }
#query { max-height: 9em; overflow: auto; color: var(--muted); margin-bottom: 8px; }
.more { display: flex; flex-wrap: wrap; gap: 4px 20px; }

/* Proofs */
table.proofs th, table.proofs td { padding: 4px 12px 4px 0; border-bottom: 1px solid var(--rule-soft); vertical-align: top; }
table.proofs thead th { border-bottom: 1px solid var(--rule); font-size: 12px; font-weight: 500; }
table.proofs tbody tr { cursor: pointer; }
table.proofs tbody tr:hover { background: var(--sub); }
table.proofs tbody tr.on { background: var(--accent-bg); box-shadow: inset 3px 0 0 var(--accent); }
table.proofs td:first-child, table.proofs th:first-child { padding-left: 8px; }
table.proofs .status { font-weight: 600; }
#explain { margin: 8px 0 0; padding: 6px 8px; border-left: 3px solid var(--accent); background: var(--sub); }

/* Facts */
.fm { color: var(--accent); }
table.facts { margin-top: 2px; }
table.facts th, table.facts td { padding: 3px 12px 3px 0; border-bottom: 1px solid var(--rule-soft); vertical-align: top; overflow-wrap: anywhere; }
table.facts thead th { border-bottom: 1px solid var(--rule); font-size: 12px; font-weight: 500; }
#conflicts-box { margin-top: 8px; color: var(--open); }

/* Toolbar */
.toolbar { display: flex; flex-wrap: wrap; gap: 8px 16px; align-items: center; padding: 8px 16px;
  border-bottom: 1px solid var(--rule); background: var(--bg); position: sticky; top: 0; z-index: 3; }
.toolbar input[type=search] { font: inherit; padding: 3px 8px; width: 18em; max-width: 100%;
  border: 1px solid var(--rule); border-radius: 3px; background: var(--bg); color: var(--ink); }
.toolbar label { color: var(--muted); white-space: nowrap; }
.toolbar .count { margin-left: auto; color: var(--muted); }
.toolbar .sel { color: var(--accent); font-weight: 600; }
.toolbar button { font: inherit; font-size: 12px; padding: 2px 8px; border: 1px solid var(--rule); border-radius: 3px;
  background: none; color: var(--muted); cursor: pointer; }
.toolbar button:hover { color: var(--ink); border-color: var(--muted); }

/* Body */
main { display: grid; grid-template-columns: minmax(320px, 42%) 1fr; }
@media (max-width: 860px) {
  main { grid-template-columns: 1fr; }
  .plan { position: static !important; max-height: none !important; border-right: 0 !important; border-bottom: 1px solid var(--rule); }
  table.cs col.rule, table.cs td.rule, table.cs th.rule { display: none; }
}
.plan { padding: 14px 12px 14px 16px; border-right: 1px solid var(--rule); position: sticky; top: 41px;
  max-height: calc(100vh - 41px); overflow: auto; }
.plan ul { list-style: none; margin: 0; padding: 0 0 0 14px; border-left: 1px solid var(--rule); }
.plan > div > ul { padding-left: 0; border-left: 0; }
.pn { display: grid; grid-template-columns: auto 1fr auto 2.8em; gap: 0 8px; align-items: baseline; padding: 3px 6px; margin: 1px 0;
  cursor: pointer; border-left: 3px solid transparent; border-radius: 0 3px 3px 0; }
.pn:hover, .pn.hl { background: var(--hl); }
.pn .id { color: var(--faint); }
.pn .op { overflow-wrap: anywhere; min-width: 0; }
.pn .op b { font-weight: 600; }
.pn .d { color: var(--muted); display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; }
.pn .n { color: var(--faint); text-align: right; white-space: nowrap; font-size: 11px; }
.pn.alias .op, .pn.alias .op b { color: var(--faint); font-weight: 400; }
.pn.alias .bd { background: none; opacity: .6; font-weight: 400; }
.pn.core { border-left-color: var(--accent); background: var(--accent-bg); }
.pn.core .n { color: var(--accent); font-weight: 600; }
.pn.out { opacity: .45; }
.sub { color: var(--muted); font-style: italic; padding: 8px 0 2px; }

.list { padding: 14px 16px; min-width: 0; }
table.cs { table-layout: fixed; }
table.cs col.id { width: 4.5em; } table.cs col.rule { width: 14em; }
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
tr.c.hl td { background: var(--hl); }
tr.c.core td.id { box-shadow: inset 3px 0 0 var(--accent); color: var(--accent); font-weight: 600; }
tr.c.core td.f { font-weight: 600; }
tr.c.out td { color: var(--faint); }
tr.c.out td.f .var { color: var(--faint); }
tr.c.fact td.id { color: var(--accent); }
tr.x td { padding: 4px 8px 8px 6px; background: var(--sub); border-bottom: 1px solid var(--rule); }
tr.x th { color: var(--muted); font-weight: 400; width: 5em; padding: 2px 8px 2px 0; vertical-align: top; }
tr.x table td { background: none; border: 0; padding: 2px 0; }
.var { border-bottom: 1px dotted var(--faint); }
.var.hl { background: var(--hl); }

dl.notation { display: grid; grid-template-columns: max-content 1fr; gap: 2px 14px; margin: 0 0 4px; color: var(--muted); }
dl.notation dt { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 12px; color: var(--ink); }
dl.notation dd { margin: 0; }
</style>
</head>
<body>
<header>
  <div class="top"><h1>cardinal</h1><span class="note" id="stats"></span></div>
  <div class="cards">
    <div class="card"><div class="k">Rows out</div><span class="bd" id="out"></span><div class="was" id="out-was"></div></div>
    <div class="card" id="total-card" hidden><div class="k">Rows over every operator</div><span class="bd" id="total"></span><div class="was" id="total-was"></div></div>
  </div>
  <pre id="query"></pre>
  <div class="more">
    <details><summary>Optimized plan</summary><pre id="plan"></pre></details>
    <details><summary>Notation</summary>
      <dl class="notation">
        <dt>X</dt><dd>Rows output by the root operator.</dd>
        <dt>|t|, T{n}_{t}</dt><dd>Rows in base table t.</dd>
        <dt>op{n}_{Kind}</dt><dd>Rows output by plan node n.</dd>
        <dt>op{n}_{Kind}[col]</dt><dd>Distinct values of column col in node n's output (NULL counts as one).</dd>
        <dt>part{n}</dt><dd>Rows of a table shared by relations whose rows are disjoint.</dd>
        <dt>◆</dt><dd>A constraint a fact gave, or a node with one.</dd>
        <dt>≥ n</dt><dd>No upper bound was proven.</dd>
      </dl>
    </details>
  </div>
</header>

<section>
  <h2>Proofs</h2>
  <table class="proofs">
    <thead><tr><th>Claim</th><th>Result</th><th>Needs</th><th>From nodes</th></tr></thead>
    <tbody id="proofs"></tbody>
  </table>
  <p id="explain" hidden></p>
</section>

<section id="facts" hidden>
  <details><summary>Facts used: <span id="facts-n"></span></summary>
    <table class="facts"><thead><tr><th>Kind</th><th>Claim</th><th>From facts</th><th>Read off</th></tr></thead><tbody id="facts-used"></tbody></table>
  </details>
  <details id="conflicts-box" hidden open><summary class="warn">Facts left out for contradicting the constraints: <span id="conflicts-n"></span></summary>
    <table class="facts"><tbody id="conflicts"></tbody></table>
  </details>
</section>

<div class="toolbar">
  <input type="search" id="search" placeholder="Filter constraints…" aria-label="Filter constraints">
  <label title="Show only the constraints the selected proof needs"><input type="checkbox" id="only"> Only needed</label>
  <label id="hide-label" hidden title="Show the analysis as if no facts were given"><input type="checkbox" id="hide"> Without facts</label>
  <span class="count" id="count"></span>
  <button id="copy">Copy SMT-LIB</button>
  <button id="save">Save .smt2</button>
</div>

<main>
  <nav class="plan" aria-label="Plan">
    <h2>Plan and bounds</h2>
    <div id="tree"></div>
  </nav>
  <div class="list">
    <h2>Constraints</h2>
    <table class="cs">
      <colgroup><col class="id"><col><col class="rule"></colgroup>
      <thead><tr><th style="padding-left:6px">#</th><th>Constraint</th><th class="rule">Rule</th></tr></thead>
      <tbody id="list"></tbody>
    </table>
  </div>
</main>

<script type="application/json" id="data">__DATA__</script>
<script>
(() => {
  const D = JSON.parse(document.getElementById('data').textContent);
  const dump = D.dump, F = dump.facts, t = F ? F.trace : dump.trace, names = D.names;
  // The proofs to select: with facts if they were proven, else the base
  // ones, whose constraints come first in the trace with facts too.
  const compare = !!(F && F.explained);
  const proofs = compare ? F.proofs : dump.proofs;
  const baseOf = {};
  if (compare) F.proofs.forEach((p, i) => { if (F.base_proofs[i]) baseOf[p.name] = F.base_proofs[i]; });
  const isFact = c => !!c.fact;
  const $ = id => document.getElementById(id);
  const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; };
  const statusOf = p => typeof p.status === 'string' ? p.status : 'Unknown';
  const hiding = () => !!F && $('hide').checked;

  // A bound, compactly: "= 60,175", "≤ 25", "3 – 25", or "≥ 100" when no
  // upper end was proven.
  const num = n => Number(n).toLocaleString('en-US');
  function boundText(s) {
    if (!s) return { text: '—', open: true };
    let m;
    if ((m = s.match(/^X = (\d+)$/))) return { text: '= ' + num(m[1]), open: false };
    if ((m = s.match(/^(\d+) <= X <= (\d+)$/))) return { text: m[1] === '0' ? '≤ ' + num(m[2]) : `${num(m[1])} – ${num(m[2])}`, open: false };
    if ((m = s.match(/^X <= (\d+)$/))) return { text: '≤ ' + num(m[1]), open: false };
    if ((m = s.match(/^X >= (\d+)$/))) return { text: '≥ ' + num(m[1]), open: true };
    return { text: s, open: !/<=|=/.test(s) };
  }
  function setBound(e, s, other) {
    const b = boundText(s);
    e.textContent = b.text;
    e.classList.toggle('open', b.open);
    e.title = (s ?? 'not computed') + (other && other !== s ? `\n${hiding() ? 'with' : 'without'} facts: ${other}` : '');
  }
  const bd = () => el('span', 'bd');

  // Header.
  $('query').textContent = dump.query.trim();
  $('plan').textContent = dump.plan;
  if (F) $('hide-label').hidden = false;
  const partitions = t.constraints.filter(c => c.node === null).length;
  const facts = t.constraints.filter(isFact).length;
  $('stats').textContent = `${t.nodes.length} plan nodes · ${t.constraints.length} constraints` +
    (partitions ? ` (${partitions} over table partitions)` : '') + (F ? ` · ${facts} from facts` : '');
  const basePlan = dump.plan_bounds, factPlan = F ? F.plan_bounds : null;
  $('total-card').hidden = !(basePlan || factPlan);
  function header() {
    const facts = F && !hiding();
    const [out, outOther] = facts ? [F.bounds, dump.bounds] : [dump.bounds, F?.bounds];
    setBound($('out'), out, outOther);
    const [plan, planOther] = facts ? [factPlan, basePlan] : [basePlan, factPlan];
    if (plan) setBound($('total'), plan.total, planOther?.total);
    const was = (e, a, b) => { e.textContent = F && a !== b ? `${facts ? 'without' : 'with'} facts ${boundText(b).text}` : ''; };
    was($('out-was'), out, outOther);
    if (plan) was($('total-was'), plan.total, planOther?.total);
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
  function opLabel(n, cls, inline) {
    const line = n.label.split('\n')[0];
    const i = line.indexOf(':');
    const box = el('span', cls);
    box.append(el('b', null, i < 0 ? line : line.slice(0, i)));
    if (i >= 0) box.append(inline ? ' ' : '', el(inline ? 'span' : 'div', 'd m', line.slice(i + 1).trim()));
    return box;
  }
  // What a node's fact pins, for its tooltip.
  function pinned(n) {
    const mine = [n.var, n.raw_var].filter(x => x);
    return (byNode[n.id] ?? []).filter(c => c.fact && c.vars.length === 1 && mine.includes(c.vars[0]))
      .map(c => `◆ ${c.vars[0] === n.var ? 'rows' : names[c.vars[0]] ?? c.vars[0]} ${c.fact.value}`);
  }

  // Plan tree, root first; nodes no other node takes as input are roots.
  const used = new Set(t.nodes.flatMap(n => n.inputs));
  const roots = t.nodes.filter(n => !used.has(n.id)).map(n => n.id).reverse();
  const treeNodes = {}, order = [], bounds = [];
  function build(id) {
    const n = t.nodes[id];
    order.push(id);
    const li = el('li');
    const alias = n.label.startsWith('SubqueryAlias');
    const row = el('div', alias ? 'pn alias' : 'pn');
    row.dataset.node = id;
    row.title = [n.label, n.var, ...pinned(n)].join('\n');
    const idBox = el('span', 'id m', String(id));
    if ((byNode[id] ?? []).some(isFact)) idBox.append(el('span', 'fm', '◆'));
    const b = bd();
    bounds.push([b, id]);
    const count = el('span', 'n m');
    row.append(idBox, opLabel(n, 'op'), b, count);
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
    if (i > 0) top.append(el('li', 'sub', 'Subquery inside an expression'));
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
    td.colSpan = 3;
    const line = el('div', 'row');
    if (key === 'p') {
      line.append(el('span', 'lab', null));
      line.firstChild.append(el('b', null, 'Table partitions'), el('span', 'd', ' — relations of one table with disjoint rows share its rows'));
    } else {
      const n = t.nodes[key];
      const lab = el('span', 'lab');
      lab.append(el('span', 'm note', `${key}  `), opLabel(n, null, true));
      lab.title = `${n.label}\n${n.var}`;
      const b = bd();
      bounds.push([b, key]);
      line.append(lab, b);
      gh.dataset.node = key;
    }
    td.append(line);
    gh.append(td);
    heads[key] = gh;
    $('list').append(gh);
    for (const c of cs) {
      const r = el('tr', isFact(c) ? 'c fact' : 'c');
      r.dataset.c = c.id;
      const rule = el('td', 'rule m', isFact(c) ? `fact: ${c.fact.source}` : c.function);
      rule.title = c.source;
      r.append(el('td', 'id m', 'c' + c.id + (isFact(c) ? ' ◆' : '')), formula(c.infix), rule);
      const x = el('tr', 'x');
      x.hidden = true;
      const xd = el('td');
      xd.colSpan = 3;
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

  // Every operator's bounds, with facts unless they are hidden.
  function nodeBounds() {
    const [plan, other] = F && !hiding() ? [factPlan, basePlan] : [basePlan, factPlan];
    for (const [e, id] of bounds) {
      e.hidden = !plan;
      if (plan) setBound(e, plan.nodes[id], other?.nodes[id]);
    }
  }

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

  // Facts: used, and conflicts.
  const factRows = [];
  if (F) {
    $('facts').hidden = false;
    const row = (body, cells) => {
      const r = el('tr');
      for (const [text, cls] of cells) r.append(el('td', cls, text));
      $(body).append(r);
      factRows.push(r);
    };
    const used = t.constraints.filter(isFact);
    $('facts-n').textContent = String(used.length);
    for (const c of used) {
      const f = c.fact, read = f.facts.flatMap(x => x.origins);
      const claim = `${c.vars.map(v => names[v] ?? v).join(', ')} ${f.value}`;
      row('facts-used', [[f.source, 'note'], [claim, 'm'], [f.facts.map(x => x.text).join(', '), 'm'], [read.length ? read.join(', ') : '—', 'm note']]);
    }
    if (F.conflicts.length) {
      $('conflicts-box').hidden = false;
      $('conflicts-n').textContent = String(F.conflicts.length);
      for (const c of F.conflicts) row('conflicts', [[c, 'm']]);
    }
  }

  // Proofs: the one shown is the base proof while facts are hidden.
  let current = null;
  const proofRows = {};
  const statusLabel = { Proven: ['proven', 'good'], Refuted: ['refuted', 'bad'], Unknown: ['unknown', 'warn'] };
  const shown = p => (hiding() && compare ? baseOf[p.name] : null) ?? p;
  const all = el('tr');
  all.append(el('td', 'note', 'none'), el('td', 'note', 'every constraint'), el('td'), el('td'));
  all.addEventListener('click', () => select(null));
  $('proofs').append(all);
  for (const p of proofs) {
    const r = el('tr');
    const cells = [el('td', 'm'), el('td'), el('td', 'm'), el('td', 'm note')];
    r.append(...cells);
    r.addEventListener('click', () => select(p.name));
    proofRows[p.name] = { r, cells, p };
    $('proofs').append(r);
  }
  function proofTable() {
    for (const { r, cells: [claim, result, needs, from], p } of Object.values(proofRows)) {
      const q = shown(p), s = statusOf(q), proven = s === 'Proven';
      claim.textContent = q.claim;
      claim.title = q.name;
      const [label, cls] = statusLabel[s];
      result.textContent = '';
      result.append(el('span', 'status ' + cls, label));
      const base = compare && !hiding() ? baseOf[p.name] : null;
      if (base && statusOf(base) !== s) result.append(el('span', 'note', ` · ${statusLabel[statusOf(base)][0]} without facts`));
      const k = proven ? q.core.filter(c => isFact(t.constraints[c])).length : 0;
      needs.textContent = proven ? String(q.core.length) + (k ? ` (${k} ◆)` : '') : '—';
      const nodes = [...new Set(q.core.map(c => t.constraints[c].node).filter(n => n !== null))].sort((a, b) => a - b);
      from.textContent = proven && nodes.length ? nodes.join(' ') : '—';
      r.title = s === 'Unknown' ? q.status.Unknown : '';
    }
  }

  function select(name) {
    const p = proofs.find(p => p.name === name);
    current = p ? shown(p) : null;
    all.classList.toggle('on', !current);
    for (const [k, { r }] of Object.entries(proofRows)) r.classList.toggle('on', k === name);
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
    let n = 0;
    for (const [id, { r, x }] of Object.entries(rows)) {
      const c = t.constraints[+id];
      const origins = c.fact ? c.fact.facts.flatMap(f => [f.text, ...f.origins]) : [];
      const text = [c.infix, c.smt, c.function, c.source, c.code, ...origins, ...c.vars.map(v => names[v] ?? v)].join(' ').toLowerCase();
      const hide = (q && !text.includes(q)) || (only && !core.has(+id)) || (hiding() && isFact(c));
      r.hidden = hide;
      if (hide) x.hidden = true;
      if (!hide) n++;
    }
    for (const [key, h] of Object.entries(heads)) h.hidden = !(byNode[key] ?? []).some(c => !rows[c.id].r.hidden);
    const count = $('count');
    count.textContent = '';
    if (current) {
      const s = statusOf(current);
      count.append(el('span', 'sel', current.claim), s === 'Proven' ? `: ${current.core.length} needed · ` : `: ${s.toLowerCase()} · `);
    }
    count.append(`${n} of ${t.constraints.length} shown`);
    for (const r of factRows) r.hidden = !!q && !r.textContent.toLowerCase().includes(q);
  }

  function refresh() {
    document.body.classList.toggle('nofacts', hiding());
    header();
    nodeBounds();
    proofTable();
    select(current ? current.name : null);
  }
  $('search').addEventListener('input', filter);
  $('only').addEventListener('change', filter);
  $('hide').addEventListener('change', refresh);

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
  current = D.proof ? { name: D.proof } : null;
  refresh();
})();
</script>
</body>
</html>
"##;
