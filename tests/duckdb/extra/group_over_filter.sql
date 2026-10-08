select l_suppkey, count(*) from lineitem where l_quantity < 10 group by l_suppkey
