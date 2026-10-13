select c_name, s.n from customer join (select o_custkey as k, count(*) as n from orders where o_orderstatus = 'O' group by o_custkey) s on s.k = c_custkey where c_acctbal > 5000
