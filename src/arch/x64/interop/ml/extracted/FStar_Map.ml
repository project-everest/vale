open Prims
type ('Akey,'Avalue) t =
  {
  mappings: 'Akey -> 'Avalue ;
  domain: 'Akey FStar_Set.set }
let __proj__Mkt__item__mappings :
  'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue =
  fun projectee  ->
    match projectee with
    | { mappings = __fname__mappings; domain = __fname__domain;_} ->
        __fname__mappings
  
let __proj__Mkt__item__domain :
  'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey FStar_Set.set =
  fun projectee  ->
    match projectee with
    | { mappings = __fname__mappings; domain = __fname__domain;_} ->
        __fname__domain
  
let sel : 'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue =
  fun m  -> fun k  -> m.mappings k 
let upd :
  'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue -> ('Akey,'Avalue) t
  =
  fun m  ->
    fun k  ->
      fun v  ->
        {
          mappings = (fun x  -> if x = k then v else m.mappings x);
          domain = (FStar_Set.union m.domain (FStar_Set.singleton k))
        }
  
let const : 'Akey 'Avalue . 'Avalue -> ('Akey,'Avalue) t =
  fun v  ->
    {
      mappings = (fun uu____253  -> v);
      domain = (FStar_Set.complement FStar_Set.empty)
    }
  
let concat :
  'Akey 'Avalue . ('Akey,'Avalue) t -> ('Akey,'Avalue) t -> ('Akey,'Avalue) t
  =
  fun m1  ->
    fun m2  ->
      {
        mappings =
          (fun x  ->
             if FStar_Set.mem x m2.domain
             then m2.mappings x
             else m1.mappings x);
        domain = (FStar_Set.union m1.domain m2.domain)
      }
  
let contains : 'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> Prims.bool =
  fun m  -> fun k  -> FStar_Set.mem k m.domain 
let restrict :
  'Akey 'Avalue .
    'Akey FStar_Set.set -> ('Akey,'Avalue) t -> ('Akey,'Avalue) t
  =
  fun s  ->
    fun m  ->
      { mappings = (m.mappings); domain = (FStar_Set.intersect s m.domain) }
  
let domain : 'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey FStar_Set.set =
  fun m  -> m.domain 













type ('Akey,'Avalue,'Am1,'Am2) equal = unit



let const_on :
  'Akey 'Avalue . 'Akey FStar_Set.set -> 'Avalue -> ('Akey,'Avalue) t =
  fun dom  -> fun v  -> restrict dom (const v) 
type ('Akey,'Avalue,'Am1,'Am2) disjoint_dom = unit
type ('Akey,'Avalue,'Am,'Adom) has_dom = unit