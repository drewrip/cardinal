select count(*) from orders o where o_totalprice > (select avg(o2.o_totalprice) from orders o2 where o2.o_custkey = o.o_custkey)
