select count(*) from part where p_size in (1, 2, 3) and p_container in ('SM BOX', 'LG BOX') and p_brand not in ('Brand#11', 'Brand#12')
