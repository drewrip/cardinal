select o_orderpriority, count(*) from orders, customer
where o_custkey = c_custkey and c_mktsegment = 'BUILDING' group by o_orderpriority
