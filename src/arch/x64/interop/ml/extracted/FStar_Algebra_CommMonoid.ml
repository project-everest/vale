open Prims
type 'Aa cm =
  | CM of 'Aa * ('Aa -> 'Aa -> 'Aa) * unit * unit * unit 
let uu___is_CM : 'Aa . 'Aa cm -> Prims.bool = fun projectee  -> true 
let __proj__CM__item__unit : 'Aa . 'Aa cm -> 'Aa =
  fun projectee  ->
    match projectee with
    | CM (unit,mult,identity,associativity,commutativity) -> unit
  
let __proj__CM__item__mult : 'Aa . 'Aa cm -> 'Aa -> 'Aa -> 'Aa =
  fun projectee  ->
    match projectee with
    | CM (unit,mult,identity,associativity,commutativity) -> mult
  




let (int_plus_cm : Prims.int cm) =
  CM ((Prims.parse_int "0"), (+), (), (), ()) 
let (int_multiply_cm : Prims.int cm) =
  CM ((Prims.parse_int "1"), ( * ), (), (), ()) 