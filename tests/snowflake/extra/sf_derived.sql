select c_count, count(*) from (select c_custkey, count(o_orderkey) from customer left outer join orders on c_custkey = o_custkey group by c_custkey) as c_orders (c_custkey, c_count) group by c_count
