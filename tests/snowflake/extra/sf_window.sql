select n_name, row_number() over (partition by n_regionkey order by n_name) rn from nation order by n_name limit 3
