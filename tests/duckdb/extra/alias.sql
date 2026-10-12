select yr, count(*) from (select extract(year from o_orderdate) as yr, o_totalprice from orders where o_totalprice > 100000) t group by yr
