select o_custkey % 10 as bucket, count(*), count(distinct o_orderstatus) from orders group by 1 having count(*) > 1400
