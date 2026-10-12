select count(*) from lineitem where l_shipinstruct ilike 'deliver%' and l_comment is not null and l_tax between 0.02 and 0.04 and coalesce(l_discount, 0) > 0.05 and l_shipmode <> 'AIR'
