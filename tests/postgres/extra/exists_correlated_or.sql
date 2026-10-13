select count(*) from customer where c_acctbal > 9000 or exists (select 1 from orders where o_custkey = c_custkey and o_totalprice > 400000)
