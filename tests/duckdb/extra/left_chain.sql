select c_custkey, o_orderkey from nation join customer on n_nationkey = c_nationkey left join orders on c_custkey = o_custkey and o_totalprice > 300000 where n_regionkey = 1
