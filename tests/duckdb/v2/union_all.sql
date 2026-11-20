select count(*) from (
  select c_nationkey as k from customer where c_acctbal > 9000
  union all select s_nationkey from supplier where s_acctbal > 9000)
