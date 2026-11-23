select l_orderkey from lineitem join orders on l_orderkey = o_orderkey where o_orderstatus = 'F' limit 10
