select count(*) from customer where exists (select 1 from orders where o_totalprice > 400000)
