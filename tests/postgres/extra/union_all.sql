select o_orderkey as k from orders where o_totalprice > 300000 union all select l_orderkey from lineitem where l_quantity > 49
