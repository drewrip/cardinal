select count(*) from lineitem where (l_partkey, l_suppkey) in (select ps_partkey, ps_suppkey from partsupp where ps_availqty < 500)
