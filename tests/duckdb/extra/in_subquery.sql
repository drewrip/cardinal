select count(*) from part where p_partkey in (select ps_partkey from partsupp where ps_availqty < 100)
