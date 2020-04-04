(* BEGIN FIX *)
From Coq Require Import Strings.String.

Inductive exp : Type :=
  | lit : nat -> exp
  | var : string -> exp
  | sub : exp -> exp -> exp
  | plus : exp -> exp -> exp.

Definition state : Type := string -> nat.

Fixpoint eval (e : exp)(s : state) : nat :=
  match e with
  | lit n => n
  | var x => s x
  | sub e1 e2 => eval e1 s - eval e2 s
  | plus e1 e2 => eval e1 s + eval e2 s
  end.

Definition empty : state := fun x => 0.

Definition W : string := "W".
Definition X : string := "X".

Fixpoint replace (e : exp)(x : string)(e' : exp) : exp :=
  match e with
  | lit n => lit n
  | var x' => if eqb x x' then e' else var x'
  | sub e1 e2 => sub (replace e1 x e') (replace e2 x e')
  | plus e1 e2 => plus (replace e1 x e') (replace e2 x e')
  end.

(* Ugy add meg e-t, hogy etest-et be tudd bizonyitani! *)
Definition e : exp := 
(* END FIX *)
   (plus (lit 5) (var W)).
(* BEGIN FIX *)
Lemma etest :
  eval
    (plus
       (replace e W (lit 3))
       (replace e X (lit 4)))
    empty = 13.
(* END FIX *)
Proof.
 simpl.
 reflexivity.
Qed. 