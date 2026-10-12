select count(*) from orders where o_orderdate >= date '1995-01-01' and o_orderdate < date '1995-01-01' + interval '3 month' and extract(month from o_orderdate) = 2
