open Prims
type 'Ap squash = unit
let unsquash : 'Ap . unit -> 'Ap =
  fun uu____25  -> failwith "Not yet implemented:unsquash" 



type ('Aa,'Ax,'dummyV0) ceq =
  | Refl 
let uu___is_Refl : 'Aa . 'Aa -> 'Aa -> ('Aa,unit,unit) ceq -> Prims.bool =
  fun x  -> fun uu____117  -> fun projectee  -> true 
type 'At at_most_one_inhabitant = 'At -> 'At -> ('At,unit,unit) ceq
let drop_squash : 'Ap . 'Ap at_most_one_inhabitant -> unit -> 'Ap =
  fun a81  ->
    fun a82  ->
      (Obj.magic
         (fun uu____177  ->
            fun uu____178  -> failwith "Not yet implemented:drop_squash"))
        a81 a82
  