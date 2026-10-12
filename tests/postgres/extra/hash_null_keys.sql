select count(*) from (select nullif(o_custkey % 2, 0) as k, o_orderkey from orders where o_orderkey < 100) s join lineitem on l_suppkey = s.k
