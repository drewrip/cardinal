select l_orderkey, sum(l_quantity) from lineitem group by l_orderkey having sum(l_quantity) > 200
