select case when o_totalprice > 200000 then 'big' else 'small' end as size, count(*) from orders group by 1
