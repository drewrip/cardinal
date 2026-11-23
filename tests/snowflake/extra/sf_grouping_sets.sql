select l_returnflag, l_linestatus, sum(l_quantity) from lineitem where l_shipmode in ('MAIL', 'SHIP')
group by grouping sets ((l_returnflag), (l_returnflag, l_linestatus))
