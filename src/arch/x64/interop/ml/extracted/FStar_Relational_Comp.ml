open Prims
type heap2 = FStar_Monotonic_Heap.heap FStar_Relational_Relational.double
type st2_Pre = unit
type ('Aa,'Apre) st2_Post' = unit
type 'Aa st2_Post = unit
type 'Aa st2_WP = unit
type ('Aa,'Ab,'Awp0,'Awp1,'Ap,'Ah2) comp = 'Awp0
let compose2 :
  'Aa0 'Ab0 'Awp0 'Aa1 'Ab1 'Awp1 .
    ('Aa0 -> 'Ab0) ->
      ('Aa1 -> 'Ab1) ->
        ('Aa0,'Aa1) FStar_Relational_Relational.rel ->
          ('Ab0,'Ab1) FStar_Relational_Relational.rel
  = fun c0  -> fun c1  -> fun x  -> failwith "Not yet implemented:compose2" 
let compose2_self :
  'Aa 'Ab 'Awp .
    ('Aa -> 'Ab) ->
      'Aa FStar_Relational_Relational.double ->
        'Ab FStar_Relational_Relational.double
  = fun f  -> fun x  -> compose2 f f x 
let cross :
  'Aa 'Ab 'Ac 'Ad 'Ap 'Ap' 'Aq 'Aq' .
    (unit FStar_Relational_Relational.double ->
       ('Aa,'Ab) FStar_Relational_Relational.rel)
      ->
      (unit FStar_Relational_Relational.double ->
         ('Ac,'Ad) FStar_Relational_Relational.rel)
        -> ('Aa,'Ad) FStar_Relational_Relational.rel
  = fun c1  -> fun c2  -> failwith "Not yet implemented:cross" 
type ('Aa0,'Aa1,'Ab0,'Ab1,'Aal,'Awp,'Ap,'Ahl) decomp_l = unit
type ('Aa0,'Aa1,'Ab0,'Ab1,'Aar,'Awp,'Ap,'Ahr) decomp_r = unit
let project_l :
  'Aa0 'Ab0 'Aa1 'Ab1 'Awp .
    (('Aa0,'Aa1) FStar_Relational_Relational.rel ->
       ('Ab0,'Ab1) FStar_Relational_Relational.rel)
      -> 'Aa0 -> 'Ab0
  = fun c  -> fun x  -> failwith "Not yet implemented:project_l" 
let project_r :
  'Aa0 'Ab0 'Aa1 'Ab1 'Awp .
    (('Aa0,'Aa1) FStar_Relational_Relational.rel ->
       ('Ab0,'Ab1) FStar_Relational_Relational.rel)
      -> 'Aa1 -> 'Ab1
  = fun c  -> fun x  -> failwith "Not yet implemented:project_r" 