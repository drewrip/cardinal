select c_custkey, o_orderkey from customer left join orders on c_custkey = o_custkey and o_orderpriority = '1-URGENT'
