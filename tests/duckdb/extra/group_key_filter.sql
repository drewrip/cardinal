select l_suppkey, count(*) from lineitem group by l_suppkey having l_suppkey < 50 and count(*) > 600
