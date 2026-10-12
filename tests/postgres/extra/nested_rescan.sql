select count(*) from supplier s join nation n on s.s_nationkey < n.n_nationkey and n.n_name like 'A%'
