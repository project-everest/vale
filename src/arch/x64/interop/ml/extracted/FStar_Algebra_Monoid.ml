open Prims
type ('Am,'Au,'Amult) right_unitality_lemma = unit
type ('Am,'Au,'Amult) left_unitality_lemma = unit
type ('Am,'Amult) associativity_lemma = unit
type 'Am monoid =
  | Monoid of 'Am * ('Am -> 'Am -> 'Am) * unit * unit * unit 
let uu___is_Monoid : 'Am . 'Am monoid -> Prims.bool = fun projectee  -> true 
let __proj__Monoid__item__unit : 'Am . 'Am monoid -> 'Am =
  fun projectee  ->
    match projectee with
    | Monoid (unit,mult,right_unitality,left_unitality,associativity) -> unit
  
let __proj__Monoid__item__mult : 'Am . 'Am monoid -> 'Am -> 'Am -> 'Am =
  fun projectee  ->
    match projectee with
    | Monoid (unit,mult,right_unitality,left_unitality,associativity) -> mult
  



let intro_monoid : 'Am . 'Am -> ('Am -> 'Am -> 'Am) -> 'Am monoid =
  fun u  -> fun mult  -> Monoid (u, mult, (), (), ()) 
let (nat_plus_monoid : Prims.nat monoid) =
  let add x y = x + y  in intro_monoid (Prims.parse_int "0") add 
let (int_plus_monoid : Prims.int monoid) =
  intro_monoid (Prims.parse_int "0") (+) 
let (conjunction_monoid : unit monoid) =
  intro_monoid () (fun a81  -> fun a82  -> ()) 
let (disjunction_monoid : unit monoid) =
  intro_monoid () (fun a83  -> fun a84  -> ()) 
let (bool_and_monoid : Prims.bool monoid) =
  let and_ b1 b2 = b1 && b2  in intro_monoid true and_ 
let (bool_or_monoid : Prims.bool monoid) =
  let or_ b1 b2 = b1 || b2  in intro_monoid false or_ 
let (bool_xor_monoid : Prims.bool monoid) =
  let xor b1 b2 = (b1 || b2) && (Prims.op_Negation (b1 && b2))  in
  intro_monoid false xor 
let lift_monoid_option :
  'Aa . 'Aa monoid -> 'Aa FStar_Pervasives_Native.option monoid =
  fun m  ->
    let mult x y =
      match (x, y) with
      | (FStar_Pervasives_Native.Some x0,FStar_Pervasives_Native.Some y0) ->
          FStar_Pervasives_Native.Some (__proj__Monoid__item__mult m x0 y0)
      | (uu____596,uu____597) -> FStar_Pervasives_Native.None  in
    intro_monoid
      (FStar_Pervasives_Native.Some (__proj__Monoid__item__unit m)) mult
  
type ('Aa,'Ab,'Af,'Ama,'Amb) monoid_morphism_unit_lemma = unit
type ('Aa,'Ab,'Af,'Ama,'Amb) monoid_morphism_mult_lemma = unit
type ('Aa,'Ab,'Af,'Ama,'Amb) monoid_morphism =
  | MonoidMorphism of unit * unit 
let uu___is_MonoidMorphism :
  'Aa 'Ab .
    ('Aa -> 'Ab) ->
      'Aa monoid ->
        'Ab monoid -> ('Aa,'Ab,unit,unit,unit) monoid_morphism -> Prims.bool
  = fun f  -> fun ma  -> fun mb  -> fun projectee  -> true 


let intro_monoid_morphism :
  'Aa 'Ab .
    ('Aa -> 'Ab) ->
      'Aa monoid -> 'Ab monoid -> ('Aa,'Ab,unit,unit,unit) monoid_morphism
  = fun f  -> fun ma  -> fun mb  -> MonoidMorphism ((), ()) 
let (embed_nat_int : Prims.nat -> Prims.int) = fun n  -> n 
let (uu___33 : (Prims.nat,Prims.int,unit,unit,unit) monoid_morphism) =
  intro_monoid_morphism embed_nat_int nat_plus_monoid int_plus_monoid 
type 'Ap neg = unit
let (uu___34 : (unit,unit,unit neg,unit,unit) monoid_morphism) =
  intro_monoid_morphism (fun a85  -> ()) conjunction_monoid
    disjunction_monoid
  
let (uu___35 : (unit,unit,unit neg,unit,unit) monoid_morphism) =
  intro_monoid_morphism (fun a86  -> ()) disjunction_monoid
    conjunction_monoid
  
type ('Am,'Aa,'Amult,'Aact) mult_act_lemma = unit
type ('Am,'Aa,'Au,'Aact) unit_act_lemma = unit
type ('Am,'Amm,'Aa) left_action =
  | LAct of ('Am -> 'Aa -> 'Aa) * unit * unit 
let uu___is_LAct :
  'Am . 'Am monoid -> unit -> ('Am,unit,Obj.t) left_action -> Prims.bool =
  fun mm  -> fun a  -> fun projectee  -> true 
let __proj__LAct__item__act :
  'Am .
    'Am monoid ->
      unit -> ('Am,unit,Obj.t) left_action -> 'Am -> Obj.t -> Obj.t
  =
  fun mm  ->
    fun a  ->
      fun projectee  ->
        match projectee with | LAct (act,mult_lemma,unit_lemma) -> act
  


type ('Aa,'Ab,'Ama,'Amb,'Af,'Amf,'Amma,'Ammb,'Ala,'Alb) left_action_morphism =
  unit