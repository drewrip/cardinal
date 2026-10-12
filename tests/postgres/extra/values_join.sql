select n_name, x from (values (0), (1)) v(x) join nation on n_regionkey = x
