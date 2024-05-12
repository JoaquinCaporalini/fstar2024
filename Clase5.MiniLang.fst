module Clase5.MiniLang

type l_ty =
  | Int
  | Bool

type var = nat

(* Pequeño lenguaje de expresiones, indexado por el tipo de su resultado *)
type expr : l_ty -> Type =
  | EInt : int -> expr Int
  | EBool : bool -> expr Bool
  | EAdd : expr Int -> expr Int -> expr Int
  | EEq : expr Int -> expr Int -> expr Bool
  | EIf :
    #ty:_ ->
    expr Bool -> expr ty -> expr ty -> expr ty

(* Traducción de tipos de MiniLang a tipos de F* *)
let lift (ty : l_ty) : Type =
  match ty with
  | Int -> int
  | Bool -> bool
(* El evaluador intrínsecamente-tipado de MiniLang *)
val eval (#ty:l_ty) (e : expr ty) : Tot (lift ty)
let rec eval (#ty:l_ty) (e : expr ty) : Tot (lift ty) (decreases e) =
  match e with
  | EInt i -> i
  | EBool b -> b
  | EAdd m n -> eval m + eval n
  | EEq m n -> eval m = eval n
  | EIf c t e ->
    if eval c then eval t else eval e

(* Optimización sobre expresionse MiniLang: constant folding *)
let rec constant_fold (#ty:l_ty) (e : expr ty) : Tot (expr ty) (decreases e) =
  match e with
  | EAdd m n -> let m' = constant_fold m in
                let n' = constant_fold n in
                (match (m', n') with
                | EInt m', EInt n' -> EInt (m' + n')
                | _ -> EAdd m' n'
                )
  | EIf c t t' -> let c' = constant_fold c in
                  (match c' with
                  | EBool true -> constant_fold t
                  | EBool false -> constant_fold t'
                  | _ -> EIf c' (constant_fold t) (constant_fold t')
                  )
  | EEq m n -> (match (constant_fold m, constant_fold n) with
                | EInt m', EInt n' -> EBool (m' = n')
                | _ -> EEq (constant_fold m) (constant_fold n)
                )
  | _ -> e (* Completar con más casos. *)

(* Correctitud de la optimización de constant folding *)
let rec constant_fold_ok (#ty:l_ty) (e : expr ty)
  : Lemma (ensures eval e == eval (constant_fold e)) (decreases e)
=
  match e with
  | EAdd m n -> constant_fold_ok m; constant_fold_ok n
  | EIf c t t' -> 
    constant_fold_ok c; 
    (match constant_fold c with
    | EBool true -> constant_fold_ok t
    | EBool false -> constant_fold_ok t'
    | e' -> constant_fold_ok t; constant_fold_ok t')
  | EEq m n -> constant_fold_ok m; constant_fold_ok n
  | _ -> ()
