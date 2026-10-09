select c_custkey, o_orderkey from customer left join orders on c_custkey = o_custkey where o_totalprice > 300000
