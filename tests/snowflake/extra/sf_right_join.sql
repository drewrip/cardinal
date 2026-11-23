select count(*) from orders o right join customer c on o.o_custkey = c.c_custkey
