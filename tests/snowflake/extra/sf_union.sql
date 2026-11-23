select count(*) from (select n_name from nation union all select r_name from region union select s_name from supplier)
