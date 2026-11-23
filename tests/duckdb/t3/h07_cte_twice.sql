with t as (select l_orderkey, sum(l_quantity) as q from lineitem group by l_orderkey) select a.l_orderkey from t a join t b on a.l_orderkey = b.l_orderkey where a.q > 150
