select c_custkey, t.o_orderkey from customer c, lateral (select o_orderkey from orders o where o.o_custkey = c.c_custkey order by o_totalprice desc limit 2) t where c_acctbal > 9500
