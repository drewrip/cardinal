-- Larger queries for tests/fact_truth.rs, each after a `-- name:` line.

-- name: five_way_filtered
select n_name, count(*) from customer, orders, lineitem, supplier, nation
where c_custkey = o_custkey and l_orderkey = o_orderkey and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey and s_nationkey = n_nationkey
  and o_orderdate >= date '1994-01-01' and l_discount between 0.05 and 0.07 and c_acctbal > 0
group by n_name

-- name: join_grouped_subquery
select c_name, big.n from customer join
  (select o_custkey, count(*) as n from orders where o_orderstatus = 'F' group by o_custkey) big
  on c_custkey = big.o_custkey
where c_mktsegment in ('BUILDING', 'MACHINERY') and big.n > 5

-- name: grouped_key_filter_in_join
select s_name, t.q from supplier join
  (select l_suppkey, sum(l_quantity) as q from lineitem group by l_suppkey) t on s_suppkey = t.l_suppkey
where t.l_suppkey < 40 and s_acctbal > 1000

-- name: nested_exists
select count(*) from part where exists (
  select * from partsupp where ps_partkey = p_partkey and ps_availqty > 5000 and exists (
    select * from supplier where s_suppkey = ps_suppkey and s_acctbal < 0))

-- name: exists_and_not_exists
select o_orderpriority, count(*) from orders
where exists (select * from lineitem where l_orderkey = o_orderkey and l_shipmode = 'AIR')
  and not exists (select * from lineitem where l_orderkey = o_orderkey and l_returnflag = 'R')
group by o_orderpriority

-- name: in_with_join_inside
select count(*) from customer where c_custkey in (
  select o_custkey from orders, lineitem where o_orderkey = l_orderkey and l_quantity > 48)

-- name: not_in_filtered
select count(*) from supplier where s_suppkey not in (
  select l_suppkey from lineitem where l_shipdate < date '1992-06-01')

-- name: correlated_inequality
select count(*) from lineitem l1 where l_quantity > 45 and exists (
  select * from lineitem l2 where l2.l_orderkey = l1.l_orderkey and l2.l_suppkey <> l1.l_suppkey)

-- name: left_where_on
select count(*) from customer left join orders on c_custkey = o_custkey and o_orderpriority = '1-URGENT'
where c_nationkey in (1, 2, 3)

-- name: left_rejecting_where
select c_custkey, o_orderkey from customer left join orders on c_custkey = o_custkey
where o_orderpriority = '1-URGENT' and c_acctbal < 0

-- name: left_is_null
select count(*) from customer left join orders on c_custkey = o_custkey where o_orderkey is null

-- name: left_chain
select count(*) from nation left join supplier on n_nationkey = s_nationkey and s_acctbal > 5000
  left join partsupp on s_suppkey = ps_suppkey and ps_availqty < 100

-- name: inner_then_left
select count(*) from region join nation on r_regionkey = n_regionkey
  left join customer on n_nationkey = c_nationkey and c_mktsegment = 'AUTOMOBILE'
where r_name in ('ASIA', 'EUROPE')

-- name: left_then_group
select c_custkey, count(o_orderkey) from customer left join orders on c_custkey = o_custkey and o_totalprice > 200000
group by c_custkey

-- name: full_filtered
select count(*) from supplier full join customer on s_nationkey = c_nationkey and s_acctbal > c_acctbal
where s_suppkey < 20

-- name: full_both_sides
select count(*) from supplier full join nation on s_nationkey = n_nationkey
where s_acctbal > 0 and n_regionkey = 2

-- name: group_having_key_and_value
select l_suppkey, count(*) from lineitem where l_quantity < 30
group by l_suppkey having l_suppkey between 10 and 60 and count(*) > 150

-- name: distinct_over_join
select distinct c_nationkey, o_orderstatus from customer, orders where c_custkey = o_custkey and o_totalprice < 50000

-- name: group_of_group
select n, count(*) from (select o_custkey, count(*) as n from orders group by o_custkey) group by n

-- name: cte_reused
with f as (select o_orderkey, o_custkey from orders where o_orderdate < date '1993-01-01')
select count(*) from f a join f b on a.o_custkey = b.o_custkey where a.o_orderkey < b.o_orderkey

-- name: self_join_filtered
select count(*) from partsupp a, partsupp b
where a.ps_partkey = b.ps_partkey and a.ps_suppkey < b.ps_suppkey and a.ps_availqty < 1000

-- name: union_all
select count(*) from (
  select c_nationkey as k from customer where c_acctbal > 9000
  union all select s_nationkey from supplier where s_acctbal > 9000)

-- name: scalar_subquery_join
select count(*) from part, partsupp where p_partkey = ps_partkey
  and ps_supplycost < (select avg(ps_supplycost) from partsupp) and p_size < 10

-- name: semi_under_join
select count(*) from orders, customer
where o_custkey = c_custkey and c_mktsegment = 'HOUSEHOLD'
  and o_orderkey in (select l_orderkey from lineitem where l_commitdate < l_receiptdate)

-- name: anti_over_grouped
select count(*) from (select o_custkey from orders group by o_custkey having count(*) > 20) g
where not exists (select * from customer where c_custkey = g.o_custkey and c_acctbal > 5000)

-- name: transitive_equalities
select count(*) from lineitem, orders, customer
where l_orderkey = o_orderkey and o_custkey = c_custkey and c_custkey < 100 and l_quantity < 20

-- name: or_across_tables
select count(*) from part, lineitem where p_partkey = l_partkey
  and ((p_brand = 'Brand#12' and l_quantity < 10) or (p_brand = 'Brand#23' and l_quantity > 40))

-- name: wide_star
select count(*) from lineitem, orders, customer, nation, region, part, supplier
where l_orderkey = o_orderkey and o_custkey = c_custkey and c_nationkey = n_nationkey
  and n_regionkey = r_regionkey and l_partkey = p_partkey and l_suppkey = s_suppkey
  and r_name = 'AMERICA' and p_type like '%STEEL' and o_orderstatus = 'O'

-- name: in_list_and_like
select count(*) from part where p_container in ('SM BOX', 'MED PACK', 'LG CASE') and p_name like '%green%'

-- name: exists_with_group_inside
select count(*) from supplier where exists (
  select l_suppkey from lineitem where l_suppkey = s_suppkey group by l_suppkey having sum(l_quantity) > 15000)
