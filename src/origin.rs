//! Row subsets of one stored table, and which of them are disjoint.
//!
//! A filter's selectivity is unknown, but two filters whose predicates cannot
//! both hold pass disjoint sets of rows: their selectivities sum to at most 1.
//! A relation built from one scan by operators that never duplicate a row
//! (filter, projection, sort, limit, distinct, semi / anti join, ...) has an
//! *origin*: the table, and the domains of the table's columns over its rows.
//! Those domains outlive the columns: a filter on `age` still says something
//! about the rows after `age` is projected away. Relations over the same table
//! whose domains are disjoint on some column share no row of it.

use datafusion::common::{Column, DFSchema};
use datafusion::logical_expr::Expr;

use crate::domain::{Dom, Facts};

#[derive(Debug, Clone)]
pub(crate) struct Origin {
    /// The table, as `ScanKind::Base::key`.
    pub(crate) table: String,
    /// The table column each output column holds unchanged, if any.
    cols: Vec<Option<String>>,
    /// Domains of table columns over this relation's rows, by column name.
    doms: Vec<(String, Dom)>,
}

impl Origin {
    /// A scan of `table` with output `schema`, whose columns are the table's.
    pub(crate) fn scan(table: &str, schema: &DFSchema) -> Origin {
        Origin {
            table: table.to_string(),
            cols: schema.fields().iter().map(|f| Some(f.name().clone())).collect(),
            doms: vec![],
        }
    }

    /// Records what `facts` say about the table columns among the output
    /// columns of `schema`.
    pub(crate) fn narrow(mut self, facts: &Facts, schema: &DFSchema) -> Origin {
        for (j, name) in self.cols.iter().enumerate() {
            let Some(name) = name else { continue };
            if j >= schema.fields().len() {
                break;
            }
            let d = facts.dom(&Expr::Column(Column::from(schema.qualified_field(j))), schema);
            match self.doms.iter_mut().find(|(n, _)| n == name) {
                Some((_, old)) => *old = old.intersect(&d),
                None => self.doms.push((name.clone(), d)),
            }
        }
        self
    }

    /// The same rows, with output column `j` holding input column `from[j]`.
    pub(crate) fn project(&self, from: impl IntoIterator<Item = Option<usize>>) -> Origin {
        Origin {
            table: self.table.clone(),
            cols: from
                .into_iter()
                .map(|i| i.and_then(|i| self.cols.get(i).cloned().flatten()))
                .collect(),
            doms: self.doms.clone(),
        }
    }

    /// The same rows, with the first `n` columns unchanged.
    pub(crate) fn with_width(&self, n: usize) -> Origin {
        self.project((0..n).map(Some))
    }

    /// True if anything is known about the rows; otherwise they cannot be
    /// disjoint from anything.
    pub(crate) fn informative(&self) -> bool {
        self.doms.iter().any(|(_, d)| *d != Dom::top())
    }

    /// True if no row of the table can be in both relations.
    fn disjoint(&self, o: &Origin) -> bool {
        self.table == o.table
            && self.doms.iter().any(|(n, a)| {
                o.doms
                    .iter()
                    .any(|(m, b)| n == m && a.intersect(b).is_empty())
            })
    }

    fn same_rows_as(&self, o: &Origin) -> bool {
        self.table == o.table
            && self.doms.len() == o.doms.len()
            && self.doms.iter().all(|x| o.doms.contains(x))
    }
}

/// Groups `origins` into classes with the same table and domains, and returns
/// each class's members, and the maximal sets of pairwise-disjoint classes (of
/// two or more classes, at most `cap` of them).
pub(crate) fn disjoint_classes(
    origins: &[Origin],
    cap: usize,
) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let mut classes: Vec<Vec<usize>> = vec![];
    for (i, o) in origins.iter().enumerate() {
        match classes.iter_mut().find(|c| origins[c[0]].same_rows_as(o)) {
            Some(c) => c.push(i),
            None => classes.push(vec![i]),
        }
    }
    let n = classes.len();
    let adj: Vec<Vec<bool>> = (0..n)
        .map(|a| {
            (0..n)
                .map(|b| origins[classes[a][0]].disjoint(&origins[classes[b][0]]))
                .collect()
        })
        .collect();
    let mut cliques = vec![];
    bron_kerbosch(&adj, vec![], (0..n).collect(), vec![], &mut cliques, cap);
    cliques.retain(|c| c.len() >= 2);
    (classes, cliques)
}

fn bron_kerbosch(
    adj: &[Vec<bool>],
    r: Vec<usize>,
    mut p: Vec<usize>,
    mut x: Vec<usize>,
    out: &mut Vec<Vec<usize>>,
    cap: usize,
) {
    if out.len() >= cap {
        return;
    }
    if p.is_empty() && x.is_empty() {
        out.push(r);
        return;
    }
    while let Some(v) = p.pop() {
        let mut r2 = r.clone();
        r2.push(v);
        let p2 = p.iter().copied().filter(|&u| adj[v][u]).collect();
        let x2 = x.iter().copied().filter(|&u| adj[v][u]).collect();
        bron_kerbosch(adj, r2, p2, x2, out, cap);
        x.push(v);
    }
}
