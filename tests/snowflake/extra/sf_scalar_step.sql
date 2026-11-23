select o_orderstatus, count(*) from orders where o_totalprice > (select avg(o_totalprice) from orders) group by o_orderstatus
