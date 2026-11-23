select count(*) from orders o full outer join customer c on o.o_custkey = c.c_custkey and c.c_acctbal > 0
