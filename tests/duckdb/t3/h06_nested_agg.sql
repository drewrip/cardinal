select cnt, count(*) from (select o_custkey, count(*) as cnt from orders group by o_custkey) t group by cnt
