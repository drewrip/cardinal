select count(*) from lineitem l1, lineitem l2
where l1.l_orderkey = l2.l_orderkey and l1.l_suppkey <> l2.l_suppkey and l1.l_quantity < 5
