select count(*) from orders where not exists (select * from lineitem where l_orderkey = o_orderkey and l_quantity > 49)
