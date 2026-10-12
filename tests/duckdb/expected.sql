-- True counts for facts the tests in tests/facts.rs assert, one row each.
SELECT 'lineitem' AS fact, count(*) AS value FROM lineitem
UNION ALL SELECT 'orders', count(*) FROM orders
UNION ALL SELECT 'customer', count(*) FROM customer
UNION ALL SELECT 'lineitem|l_quantity<10', count(*) FROM lineitem WHERE l_quantity < 10
UNION ALL SELECT 'lineitem|l_quantity>49', count(*) FROM lineitem WHERE l_quantity > 49
UNION ALL SELECT 'customer|c_mktsegment=BUILDING', count(*) FROM customer WHERE c_mktsegment = 'BUILDING'
UNION ALL SELECT 'orders|o_orderstatus=F', count(*) FROM orders WHERE o_orderstatus = 'F'
UNION ALL SELECT 'ndv(l_suppkey|lineitem)', count(DISTINCT l_suppkey) FROM lineitem
UNION ALL SELECT 'ndv(l_suppkey|lineitem,l_quantity<10)', count(DISTINCT l_suppkey) FROM lineitem WHERE l_quantity < 10
UNION ALL SELECT 'ndv(c_nationkey,c_mktsegment|customer)', count(*) FROM (SELECT DISTINCT c_nationkey, c_mktsegment FROM customer)
UNION ALL SELECT 'orders⋈customer|BUILDING', count(*) FROM orders, customer WHERE o_custkey = c_custkey AND c_mktsegment = 'BUILDING'
UNION ALL SELECT 'ndv(o_orderpriority|orders⋈customer,BUILDING)', count(DISTINCT o_orderpriority) FROM orders, customer WHERE o_custkey = c_custkey AND c_mktsegment = 'BUILDING'
UNION ALL SELECT 'lineitem⋈orders|F,l_quantity<10', count(*) FROM lineitem, orders WHERE l_orderkey = o_orderkey AND o_orderstatus = 'F' AND l_quantity < 10
UNION ALL SELECT 'orders semi lineitem>49', count(*) FROM orders WHERE EXISTS (SELECT * FROM lineitem WHERE l_orderkey = o_orderkey AND l_quantity > 49)
UNION ALL SELECT 'lineitem|l_quantity<10,l_extendedprice*2>10000', count(*) FROM lineitem WHERE l_quantity < 10 AND l_extendedprice * 2 > 10000
UNION ALL SELECT 'orders semi customer BUILDING', count(*) FROM orders WHERE o_custkey IN (SELECT c_custkey FROM customer WHERE c_mktsegment = 'BUILDING')
UNION ALL SELECT 'customer anti orders', count(*) FROM customer WHERE NOT EXISTS (SELECT * FROM orders WHERE o_custkey = c_custkey)
UNION ALL SELECT 'self join', count(*) FROM lineitem l1, lineitem l2 WHERE l1.l_orderkey = l2.l_orderkey AND l1.l_suppkey <> l2.l_suppkey AND l1.l_quantity < 5
UNION ALL SELECT 'orders anti lineitem>49', count(*) FROM orders WHERE NOT EXISTS (SELECT * FROM lineitem WHERE l_orderkey = o_orderkey AND l_quantity > 49)
UNION ALL SELECT 'part semi partsupp<100', count(*) FROM part WHERE p_partkey IN (SELECT ps_partkey FROM partsupp WHERE ps_availqty < 100)
UNION ALL SELECT 'part not in partsupp<100', count(*) FROM part WHERE p_partkey NOT IN (SELECT ps_partkey FROM partsupp WHERE ps_availqty < 100)
UNION ALL SELECT 'ndv(l_orderkey|lineitem)', count(DISTINCT l_orderkey) FROM lineitem
UNION ALL SELECT 'having sum>200', count(*) FROM (SELECT l_orderkey FROM lineitem GROUP BY l_orderkey HAVING sum(l_quantity) > 200)
UNION ALL SELECT 'price>avg', count(*) FROM lineitem WHERE l_extendedprice > (SELECT avg(l_extendedprice) FROM lineitem)
UNION ALL SELECT 'ndv(year|orders,price>100000)', count(DISTINCT extract(year FROM o_orderdate)) FROM orders WHERE o_totalprice > 100000
UNION ALL SELECT 'orders|price>100000', count(*) FROM orders WHERE o_totalprice > 100000
UNION ALL SELECT 'ndv(o_custkey|orders)', count(DISTINCT o_custkey) FROM orders
UNION ALL SELECT 'customer⟕orders>300000|acctbal>5000', count(*) FROM customer LEFT JOIN orders ON c_custkey = o_custkey AND o_totalprice > 300000 WHERE c_acctbal > 5000
UNION ALL SELECT 'customer⋈orders|price>300000', count(*) FROM customer, orders WHERE c_custkey = o_custkey AND o_totalprice > 300000
UNION ALL SELECT 'nation⋈customer⟕orders>300000|region=1', count(*) FROM nation JOIN customer ON n_nationkey = c_nationkey LEFT JOIN orders ON c_custkey = o_custkey AND o_totalprice > 300000 WHERE n_regionkey = 1
UNION ALL SELECT 'ndv(l_suppkey|lineitem,l_suppkey<50)', count(DISTINCT l_suppkey) FROM lineitem WHERE l_suppkey < 50;
