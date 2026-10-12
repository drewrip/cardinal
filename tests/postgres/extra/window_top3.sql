select o_custkey, o_orderkey, rn from (select o_custkey, o_orderkey, row_number() over (partition by o_custkey order by o_totalprice desc) as rn from orders where o_orderstatus = 'F') s where rn <= 3
