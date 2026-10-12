select count(*) from customer where not exists (select * from orders where o_custkey = c_custkey)
