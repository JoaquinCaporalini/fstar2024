module Clase3.Vec

type vec (a:Type) : nat -> Type =
  | VNil : vec a 0
  | VCons : #n:nat -> hd:a -> tl:vec a n -> vec a (n+1)
  
let vhd (#a:Type) (#n:pos) (xs : vec a n) : a =
  match xs with
  | VCons hd tl -> hd

let rec vidx (#a:Type) (#n:pos) (xs : vec a n) (i : nat{i < n}) : a =
  match xs with
  | VCons hd tl ->
    if i = 0
    then hd
    else vidx tl (i-1)

let rec vappend (#a:Type) (#n1 #n2 : nat) (xs : vec a n1) (ys : vec a n2) : vec a (n1 + n2) =
  // admit() (* completar *)
  match xs with
  | VNil -> ys
  | VCons hd tl -> VCons hd (vappend tl ys)

let rec vupd (#a:Type) (#n:pos) (xs : vec a n) (i : nat{i < n}) (x : a) : vec a n =
  // admit() (* completar *)
  match xs with
  | VCons hd tl ->
    if i = 0
    then VCons x tl
    else VCons hd (vupd tl (i-1) x)

(* Definir funciones similares para matrices. Se pueden
usar las definiciones anteriores. *)

let mat (a:Type) (m n : nat) : Type =
  // admit()
  vec (vec a n) m
  
let matidx (#a:Type) (#m #n : nat) (ma : mat a m n) (i : nat{i < m}) (j : nat{j < n}) : a =
  // 
  vidx (vidx ma i) j
  
let matupd (#a:Type) (#m #n : nat) (ma : mat a m n) (i : nat{i < m}) (j : nat{j < n}) (x : a) : mat a m n =
  // admit()
  vupd ma i (vupd (vidx ma i) j x)
