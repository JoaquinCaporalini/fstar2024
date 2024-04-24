module Clase5.Listas

open FStar.List.Tot

val sum_int : list int -> int
let rec sum_int xs =
  match xs with
 | [] -> 0
 | x::xs' -> x + sum_int xs'

(* Demuestre que sum_int "distribuye" sobre la concatenación de listas. *)
let rec sum_append (l1 l2 : list int)
  : Lemma (sum_int (l1 @ l2) == sum_int l1 + sum_int l2)
  = match l1 with
    | [] -> ()
    | x::xs -> sum_append xs l2

(* Idem para length, definida en la librería de F*. *)
let rec len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  = match l1 with
    | [] -> ()
    | x::xs -> len_append xs l2

// Agrega un elemento al final de la lista
let rec snoc (xs : list int) (x : int) : list int = 
  match xs with
  | [] -> [x]
  | y::ys -> y :: snoc ys x

(* unit-tests *)
let _ = assert (snoc [1;2;3] 4 == [1;2;3;4])
let _ = assert (snoc [1;2;3] 5 == [1;2;3;5])

let rec rev_int (xs : list int) : list int =
  match xs with
  | [] -> []
  | x::xs' -> snoc (rev_int xs') x

// let _ = assert (rev_int ([1;2;3] @ [7;8;9]) == rev_int [7;8;9] @ rev_int [1;2;3])

let rec snoc_append_int (xs ys : list int) (x : int)
  : Lemma (snoc (xs @ ys) x == xs @ snoc ys x)
  = match xs with
    | [] -> ()
    | x'::xs' -> snoc_append_int xs' ys x

let rec rev_append_int (xs ys : list int)
  : Lemma (rev_int (xs @ ys) == rev_int ys @ rev_int xs)
= match xs with
  | [] -> ()
  | x::xs' -> 
    // assert(rev_int (x::xs' @ ys) == snoc (rev_int (xs' @ ys)) x);
    rev_append_int xs' ys;
    // assert(snoc (rev_int (xs' @ ys)) x == snoc (rev_int ys @ rev_int xs') x);
    // assume(forall xs ys x. snoc (xs @ ys) x == xs @ snoc ys x)
    snoc_append_int (rev_int ys) (rev_int xs') x
    // assert(snoc (rev_int ys @ rev_int xs') x == rev_int ys @ rev_int xs)
    
let rec cons_snoc (xs : list int) (x : int)
: Lemma (rev_int (snoc xs x) == x :: (rev_int xs))
  = match xs with
    | [] -> ()
    | x'::xs' -> 
      assert (rev_int (snoc xs x) == rev_int (snoc (x'::xs') x));
      assert (rev_int (snoc (x'::xs') x) == rev_int (x'::(snoc xs' x)));
      assert (rev_int (x'::(snoc xs' x)) == snoc (rev_int (snoc xs' x)) x');
      cons_snoc xs' x;
      ()

let rec rev_rev (xs : list int)
  : Lemma (rev_int (rev_int xs) == xs)
= match xs with
  | [] -> ()
  | x::xs' -> 
    rev_rev xs';
    assert (rev_int (rev_int xs') == xs');
    assert (rev_int (rev_int (x::xs')) == rev_int (snoc (rev_int xs') x));
    // assume (rev_int (snoc (rev_int xs') x) == x :: (rev_int (rev_int xs')));
    cons_snoc (rev_int xs') x;
    ()

let rev_injective (xs ys : list int)
  : Lemma (requires rev_int xs == rev_int ys) (ensures xs == ys)
= assert (rev_int xs == rev_int ys);
  assert (rev_int (rev_int xs) == rev_int (rev_int ys));
  rev_rev xs;
  rev_rev ys;
  ()