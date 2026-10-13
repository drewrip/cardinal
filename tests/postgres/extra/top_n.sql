select o_orderkey, o_totalprice from orders where o_orderstatus = 'F' order by o_totalprice desc limit 10 offset 5
