select k, n from (select o_custkey as k, count(*) as n, max(o_totalprice) as top from orders group by o_custkey) s where n > 20 and top > 300000
