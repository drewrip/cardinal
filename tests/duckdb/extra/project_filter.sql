select * from (select l_quantity, l_extendedprice * 2 as double_price from lineitem) t
where l_quantity < 10 and double_price > 10000 and random() >= 0
