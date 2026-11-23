with big as (select o_custkey, o_totalprice from orders where o_totalprice > 100000)
select count(*) from big b1 join big b2 on b1.o_custkey = b2.o_custkey where b1.o_totalprice > b2.o_totalprice
