select count(*) from lineitem where l_extendedprice > (select avg(l_extendedprice) from lineitem)
