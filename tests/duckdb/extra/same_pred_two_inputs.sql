select count(*) from lineitem, orders where l_orderkey = o_orderkey and o_orderstatus = 'F' and l_quantity < 10
