module Collections.Lists_i

#reset-options "--initial_fuel 2 --max_fuel 2"
let singleton_list_rev #a x = ()
let list_cons_is_append #a h t = ()

let singleton_list_seq #a x =
  lemma_of_list_length [x];
  lemma_of_list [x] 0;
  assert (equal (of_list [x]) (create 1 x))
#reset-options

let rec list_append_length #a x y =
  match x with
  | [] -> ()
  | _::t -> list_append_length t y

let rec list_append_index #a x y i =
  match x with
  | [] -> ()
  | h::t -> (if i > 0 then list_append_index t y (i - 1))

let rec append_list_seq #a x y =
  lemma_of_list_length (x @ y);
  lemma_of_list_length x;
  lemma_of_list_length y;
  list_append_length x y;
  let n = List.length (x @ y) in
  let index_of_x_y (i:nat{i < n}) : a = index (of_list (x @ y)) i in
  let index_of_append_x_y (i:nat{i < n}) : a = index (append (of_list x) (of_list y)) i in
  let f (i:nat{i < n}) : Lemma (index_of_x_y i == index_of_append_x_y i) =
    list_append_index x y i;
    lemma_of_list (x @ y) i;
    (
      if i < List.length x then
        lemma_of_list x i
      else
        lemma_of_list y (i - List.length x)
    )
    in
  FStar.Classical.forall_intro f;
  assert (equal (of_list (x @ y)) (append (of_list x) (of_list y)))

#reset-options "--z3rlimit 20"
let rec lemma_from_list_le l =
  match l with
  | [] -> ()
  | h::t ->
    (
      lemma_from_list_le t;
      let rl = List.rev l in
      let rt = List.rev t in
      let sl = of_list rl in
      let st = of_list rt in
      let sh = create 1 h in
      let n = length st in
      rev_length l;
      rev_length t;
      lemma_of_list_length rl;
      lemma_of_list_length rt;

      rev_append [h] t;
      singleton_list_rev h;
      list_cons_is_append h t;
      append_list_seq rt [h];
      singleton_list_seq h;
      assert (equal st (slice sl 0 n))
    )

let lemma_from_list_be l =
  List.rev_involutive l;
  lemma_from_list_le (List.rev l)
