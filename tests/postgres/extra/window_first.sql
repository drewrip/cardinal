select o_custkey, o_orderkey from (select o_custkey, o_orderkey, row_number() over (partition by o_custkey order by o_orderdate desc, o_orderkey) as rn from orders) s where rn = 1
