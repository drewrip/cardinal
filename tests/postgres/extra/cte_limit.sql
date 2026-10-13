with t as materialized (select o_orderkey, o_custkey from orders where o_orderstatus = 'P') select * from t limit 5
