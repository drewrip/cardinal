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
UNION ALL SELECT 'customer anti orders', count(*) FROM customer WHERE NOT EXISTS (SELECT * FROM orders WHERE o_custkey = c_custkey);
