open Prims
let read_rel1 :
  'Auu____27 .
    'Auu____27 FStar_ST.ref -> 'Auu____27 FStar_Relational_Relational.double
  =
  fun r  ->
    FStar_Relational_Comp.compose2_self FStar_Ref.read
      (FStar_Relational_Relational.twice r)
  
let read_rel2 :
  'Auu____217 .
    unit ->
      'Auu____217 FStar_ST.ref FStar_Relational_Relational.double ->
        'Auu____217 FStar_Relational_Relational.double
  = fun uu____232  -> FStar_Relational_Comp.compose2_self FStar_Ref.read 
let assign_rel1 :
  'Auu____397 .
    'Auu____397 FStar_ST.ref ->
      ('Auu____397,'Auu____397) FStar_Relational_Relational.rel ->
        unit FStar_Relational_Relational.double
  =
  fun r  ->
    fun v  ->
      FStar_Relational_Comp.compose2_self
        (fun uu____497  ->
           match uu____497 with | (a,b) -> FStar_Ref.write a b)
        (FStar_Relational_Relational.pair_rel
           (FStar_Relational_Relational.twice r) v)
  
let assign_rel2 :
  'Auu____600 .
    ('Auu____600 FStar_ST.ref,'Auu____600 FStar_ST.ref)
      FStar_Relational_Relational.rel ->
      ('Auu____600,'Auu____600) FStar_Relational_Relational.rel ->
        unit FStar_Relational_Relational.double
  =
  fun r  ->
    fun v  ->
      FStar_Relational_Comp.compose2_self
        (fun uu____690  ->
           match uu____690 with | (a,b) -> FStar_Ref.write a b)
        (FStar_Relational_Relational.pair_rel r v)
  