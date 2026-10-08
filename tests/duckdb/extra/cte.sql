with per_customer as materialized (select o_custkey, count(*) as n from orders group by o_custkey)
select count(*) from per_customer a, per_customer b where a.o_custkey = b.o_custkey + 1 and b.o_custkey < 500
