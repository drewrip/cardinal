select c_custkey, count(o_orderkey) as c_count from customer left outer join orders on c_custkey = o_custkey
group by c_custkey order by c_count desc, c_custkey limit 7 offset 3
