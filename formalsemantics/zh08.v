(* BEGIN FIX *)
From Coq Require Import Strings.String.

Inductive exp : Type :=
| lit (n : nat)
| var (x : string)
| plus (e1 e2 : exp).

Definition state : Type := string -> nat.

Definition empty : state := fun x => 0.

Definition update (x:string)(n:nat)(s:state) : state :=
  fun x' => match string_dec x x' with
  | left  e => n
  | right e => s x'
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Reserved Notation "e , s =v n" (at level 50).
Inductive evalb : exp -> state -> nat -> Prop :=
  | evalb_lit (n : nat)(s : state) :

    (*------------------*)
    lit n , s =v n

  | evalb_var (x : string)(s : state) :

    (*------------------*)
    var x , s =v s x

  | evalb_plus (n1 n2 : nat)(e1 e2 : exp)(s : state) :

    e1 , s =v n1  ->  e2 , s =v n2 ->
    (*---------------------------*)
    plus e1 e2 , s =v (n1 + n2)

  where "e , s =v n" := (evalb e s n).

Fixpoint evald (e : exp) : state -> nat := fun s => match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => evald e1 s + evald e2 s
  end.

Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), evald e s = n -> e , s =v n.
induction e; intros; simpl in H; rewrite <- H.
 * apply evalb_lit.
 * apply evalb_var.
 * apply (evalb_plus (evald e1 s) (evald e2 s)). apply IHe1. reflexivity.  apply IHe2. reflexivity.
Qed.  

Lemma zh : forall (e e' : exp)(s : state), exists (n : nat), plus e e' , s =v n.
(* END FIX *)
Proof.
  intros.
  exists ((evald e s) + (evald e' s)).
  apply (denot2bigstep).
  simpl. reflexivity.
Qed.



