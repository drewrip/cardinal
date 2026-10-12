select c_custkey, o_orderkey from customer left join orders on c_custkey = o_custkey and o_totalprice > 300000 where c_acctbal > 5000
