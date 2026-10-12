with big as materialized (select o_orderkey, o_custkey from orders where o_totalprice > 250000) select count(*) from big join customer on c_custkey = o_custkey where c_mktsegment = 'MACHINERY'
