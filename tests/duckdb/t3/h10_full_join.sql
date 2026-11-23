select c_custkey, o_orderkey from (select * from customer where c_acctbal < 0) c full join (select * from orders where o_orderstatus = 'P') o on c_custkey = o_custkey
