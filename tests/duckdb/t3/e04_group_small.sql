select l_returnflag, l_linestatus, count(*) from lineitem group by l_returnflag, l_linestatus
