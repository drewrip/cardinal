select o_orderkey, r from (select o_orderkey, rank() over (order by o_totalprice desc) as r from orders) s where r <= 10
