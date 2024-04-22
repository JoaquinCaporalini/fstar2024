module Clase3.GADT

type l_ty =
  | Int
  | Bool
  
type expr : l_ty -> Type =
  | EInt : int -> expr Int
  | EBool : bool -> expr Bool
  | EAdd : expr Int -> expr Int -> expr Int
  | EEq : expr Int -> expr Int -> expr Bool
  | EIf :
    #ty:_ ->
    expr Bool -> expr ty -> expr ty -> expr ty

let lift (ty : l_ty) : Type =
  match ty with
  | Int -> int
  | Bool -> bool


// val eval (#ty:l_ty) (e : expr ty) : Tot (lift ty)
let rec eval (#ty:l_ty) (e : expr ty) : Tot (lift ty) (decreases e)=
  // admit()
  match e with
  | EInt n -> n
  | EBool b -> b
  | EEq e1 e2 -> e1 = e2
  | EAdd e1 e2 -> (eval e1) + (eval e2)
  | EIf b e1 e2 -> 
    if eval b then
      eval e1
    else
      eval e2
  (* Completar *)