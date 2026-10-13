select distinct on (o_custkey) o_custkey, o_orderkey from orders where o_totalprice > 200000 order by o_custkey, o_orderdate desc
