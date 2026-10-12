select count(*) from partsupp where (ps_partkey, ps_suppkey) not in (select l_partkey, l_suppkey from lineitem where l_quantity > 45)
