select count(*) from nation where n_regionkey = 1 and n_nationkey in (select s_nationkey from supplier) and n_name = 'CANADA'
