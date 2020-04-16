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

Fixpoint evald (e : exp) : state -> nat := fun s => match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => evald e1 s + evald e2 s
  end.
Reserved Notation "e , s => e'" (at level 50).
Inductive evalo : exp -> state -> exp -> Prop :=
  | eval_var (x : string)(s : state) :

    (*------------------*)
    var x , s => lit (s x)

  | eval_plus_lhs (e1 e2 e1' : exp)(s : state) :

          e1 , s => e1'           ->
    (*-------------------------*)
    plus e1 e2 , s => plus e1' e2

  | eval_plus_rhs (e2 e2' : exp)(s : state)(n : nat) :

             e2 , s => e2'                  ->
    (*-----------------------------------*)
    plus (lit n) e2 , s => plus (lit n) e2'

  | eval_plus_fin (n m : nat)(s : state) :

    (*-----------------------------------*)
    plus (lit m) (lit n) , s => lit (m + n)

  where "e , s => e'" := (evalo e s e').

Reserved Notation "e , s =>* e'" (at level 50).
Inductive evalo_rtc : exp -> state -> exp -> Prop :=
  | eval_refl (e : exp)(s : state) : 

    e , s =>* e

  | eval_trans (e e' e'' : exp)(s : state) :

    e , s => e'    ->    e' , s =>* e'' ->
    (*-------------------------------*)
    e , s =>* e''

  where "e , s =>* e'" := (evalo_rtc e s e').

Lemma progress (e : exp)(s : state) : (exists (n : nat), e = lit n) \/ exists (e' : exp), e , s => e'.
Proof.
  induction e.
  - left.  exists n. reflexivity.
  - right. exists (lit (s x)). apply eval_var.
  - right. destruct IHe1. 
    * destruct IHe2.
      + destruct H. destruct H0. rewrite -> H. rewrite -> H0. exists (lit (x+x0)). apply eval_plus_fin.
      + destruct H. destruct H0. rewrite -> H. exists (plus (lit x) x0). apply eval_plus_rhs. exact H0.
    * destruct H. exists (plus x e2). apply eval_plus_lhs. exact H.
Qed.

Lemma determ (e e' : exp)(s : state) : e , s => e' -> forall e'', e , s => e'' -> e' = e''.
Proof.
  intro.
  induction H.
  { intros. inversion H. reflexivity. }
  { intros. inversion H0. 
    + Check IHevalo _ H5. rewrite -> (IHevalo _ H5). reflexivity. 
    + rewrite <- H1 in H. inversion H.
    + rewrite <- H2 in H. inversion H. }
  { intros. inversion H0.
    + inversion H5.
    + Check IHevalo _ H5. rewrite -> (IHevalo _ H5). reflexivity.
    + rewrite <- H3 in H. inversion H. }
  { intros. inversion H.
    + inversion H4.
    + inversion H4.
    + reflexivity. }
Qed.

Definition eval_singl (e e' : exp)(s : state) : e , s => e' -> e , s =>* e'.
Proof.
  intros.
  induction e.
  { inversion H. }
  { induction e'.
    + apply (eval_trans _ (lit (s x))).
      - apply eval_var.
      - inversion H. apply eval_refl.
    + inversion H.
    + inversion H. }
  { induction e'.
    + inversion H. apply (eval_trans _ (lit (m+n0))).
      - apply eval_plus_fin.
      - apply eval_refl.
    + inversion H.
    + 
Admitted.

(* HF *)
Lemma trans (e e' e'' : exp)(s : state) : e , s =>* e' -> e' , s =>* e'' -> e , s =>* e''.
intros.
induction H.
  - exact H0.
  - apply (eval_trans _ _ _ _ H). apply IHevalo_rtc. exact H0.
Qed.

Lemma eval_plus_lhs_rtc (e1 e1' e2 : exp)(s : state) : e1 , s =>* e1' -> plus e1 e2 , s =>* plus e1' e2.
Proof.
  intros.
  induction e1'.
  { apply (eval_trans _ (plus (lit n) e2)).
    - apply eval_plus_lhs.
Admitted.

Lemma eval_plus_rhs_rtc (n : nat)(e2 e2' : exp)(s : state) : e2 , s =>* e2' -> 
  plus (lit n) e2 , s =>* plus (lit n) e2'.
Admitted.

Lemma operDenot (e : exp)(s : state) : e , s =>* lit (evald e s).
Proof.
  induction e.
  { simpl. apply eval_refl. }
  { simpl. apply (eval_trans _ (lit (s x))).
    + apply eval_var.
    + apply eval_refl. }
  { 
Admitted.

Lemma totality (e : exp)(s : state) : exists (n : nat), e , s =>* lit n.
Proof.
  induction e.
  { exists n. apply eval_refl. }
  { exists (s x). apply (eval_trans _ (lit (s x))).
    + apply eval_var.
    + apply eval_refl. }
  { 
Admitted.

Lemma determ_rtc (e : exp)(s : state)(n : nat) : e , s =>* lit n -> forall n', e , s => lit n' -> n = n'.
Admitted.

Lemma denotVsOper (e : exp)(s : state)(n : nat) : evald e s = n <-> e , s =>* lit n.
Admitted.

(* big-step operational semantics *)

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
(*
Fixpoint evald (e : exp) : state -> nat := fun s => match e with
  | lit n => n
  | var x => s x
  | plus e1 e2 => evald e1 s + evald e2 s
  end.
*)

Example ex1d : evald (plus (plus (var W) (var X)) (lit 100)) (update W 200 empty) = 300.
Proof. simpl. reflexivity. Qed.

Example ex1 : plus (plus (var W) (var X)) (lit 100) , update W 200 empty =v 300.
Proof.
  apply (evalb_plus 200 100).
  { apply (evalb_plus 200 0). 
    { apply (evalb_var). }
    { apply (evalb_var). }
  }
  apply evalb_lit.
Qed.

Example ex2 : exists (n : nat),
  plus (plus (var X) (var Y)) (plus (lit 3) (var Z)) , update X 3 (update Y 2 empty) =v n.
Proof.
  exists 8.
  apply (evalb_plus 5 3).
  * apply (evalb_plus 3 2).
    + apply evalb_var.
    + apply evalb_var.
  * apply (evalb_plus 3 0).
    + apply evalb_lit.
    + apply evalb_var.
Qed.

Lemma determBigstep (e : exp)(s : state)(n : nat) : e , s =v n -> forall n', e , s =v n' -> n = n'.
Proof.
  intros.
  induction e.
  - 
Admitted.

Lemma denot2bigstep (e : exp)(s : state) : forall (n : nat), evald e s = n -> e , s =v n.
Proof.
induction e; intros; simpl in H; rewrite <- H.
 * apply evalb_lit.
 * apply evalb_var.
 * apply (evalb_plus (evald e1 s) (evald e2 s)).
   - apply IHe1. reflexivity.
   - apply IHe2. reflexivity.
Qed.

Lemma bigstep2denot (e : exp)(s : state) : forall (n : nat), e , s =v n -> evald e s = n.
Admitted.

Lemma bigstepVsdenot (e : exp)(s : state)(n : nat) : e , s =v n <-> evald e s = n.
Admitted.

Lemma notInvertible (n : nat)(s : state) : exists (e e' : exp), e <> e' /\ e , s =v n /\ e' , s =v n.
Admitted.