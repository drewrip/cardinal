select count(*) from customer full join supplier on c_nationkey = s_nationkey and c_acctbal > 9000 where s_acctbal > 9000 or s_suppkey is null
