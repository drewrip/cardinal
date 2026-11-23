with t as (select o_custkey, count(*) as n from orders where o_orderstatus = 'F' group by o_custkey)
select count(*) from t a join t b on a.o_custkey = b.o_custkey + 1 where a.n > b.n
