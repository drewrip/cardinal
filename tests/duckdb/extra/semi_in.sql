select count(*) from orders where o_custkey in (select c_custkey from customer where c_mktsegment = 'BUILDING')
