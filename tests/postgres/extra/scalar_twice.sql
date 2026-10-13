select count(*) from lineitem where l_quantity > (select avg(l_quantity) from lineitem) and l_extendedprice < (select avg(l_extendedprice) from lineitem)
