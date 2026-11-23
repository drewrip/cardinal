select n_name, (select count(*) from supplier s where s.s_nationkey = n.n_nationkey) from nation n where n_regionkey = 1
