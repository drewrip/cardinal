select * from orders where exists (select * from lineitem where l_orderkey = o_orderkey and l_receiptdate > l_commitdate)
