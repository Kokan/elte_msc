Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp).

Definition exTree : AExp := 
(APlus 
    (ASub 
        (ALit 1)
        (APlus
            (ALit 2)
            (ALit 3)
        )
     )
    (ALit 0)
).

Fixpoint leaves (a : AExp) : nat := match a with
  | ALit n => 1
  | APlus a1 a2 => leaves a1 + leaves a2
  | ASub a1 a2 => leaves a1 + leaves a2
  end.

Fixpoint height (a : AExp) : nat := match a with
  | ALit n => 0
  | APlus a1 a2 => 1 + max (height a1) (height a2)
  | ASub a1 a2 => 1 + max (height a1) (height a2)
  end.

Example exExp : AExp := (APlus (ALit 1) (ALit 2)).

Lemma exExpProp : height exExp = 1.
Proof.
  simpl.
  reflexivity.
Qed.
(*
Tactic reminder:

           INTRODUCTION     ELIMINATION
True       split
False                       destruct
/\         split            destruct
\/         left, right      destruct
forall     intro            apply
exists     exists           destruct
->         intro            apply

others:
assert
discriminate
simpl
*)


(*
Abstract representation levesl: 
ABT  not possible to represent "\x.(x+y" (\x read as lambda x) due to scope
WTT  not possible to represent "true+1" due to not possible to evaluate
Alg
HOAS
*)

Example expWithProperty : exists (a : AExp), leaves a = 3 /\ height a = 2.
Proof.
  exists (ASub (ALit 10) (ASub (ALit 1) (ALit 2))).
  simpl.
  split.
  all: reflexivity.
Qed.

Example notPoss : not (exists (a : AExp), leaves a = 2 /\ height a = 0).
Proof.
  unfold not.
  intros.
  destruct H.
  destruct H.
  destruct x.
  { unfold leaves in H. discriminate. }
  all: simpl in H0.
  all: discriminate H0.
Qed.


(* Denotational semantics *)
Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n      => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | ASub  a1 a2 => aeval a1 - aeval a2
  end.

Compute aeval exTree.
Compute exExp.
Compute aeval exExp.

Lemma eval_exExp : aeval exExp = 3.
Proof.
  simpl.
  reflexivity.
Qed.

Check ex_proj1.


Fixpoint optim (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus e1 (ALit 0) => optim e1
  | APlus e1 e2 => APlus (optim e1) (optim e2)
  | ASub  e1 e2 => ASub  (optim e1) (optim e2)
  end.

Compute optim exExp.
Compute aeval exExp.
Compute aeval (APlus (ALit 1) (ALit 2)).

Require Import Coq.Arith.Plus.

Check plus_0_r.


Lemma optim_sound (a : AExp) :
  aeval (optim a) = aeval a.
Proof.
  induction a.
  { simpl. reflexivity. }
  { simpl.
    destruct a2.
    destruct n.
    { rewrite IHa1. simpl. rewrite (plus_0_r). reflexivity. }
    { simpl. rewrite IHa1. reflexivity. }
    { simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity. }
    { simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity. }
  }
  { simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity. }
Qed.



Lemma optim_sound2 (a : AExp) :
  aeval (optim a) = aeval a.
Proof.
  induction a.
  all: try ( info_auto ).
  all: try ( simpl; rewrite -> IHa1; rewrite -> IHa2; reflexivity ).
  simpl.
  destruct a2.
  destruct n.
  all: try ( simpl; simpl in IHa2; rewrite IHa2; rewrite IHa1; info_auto ).
  all: try ( simpl; rewrite IHa1; reflexivity ).
  rewrite IHa1. simpl.  rewrite (plus_0_r). reflexivity.
Qed.

(* try, ; *)


Fixpoint optimoptim (a : AExp) : AExp := ALit (aeval a).

Lemma optimoptim_sound (a : AExp ) : aeval (optimoptim a) = aeval a.
Proof.
  induction a.
  all: simpl.
  all: reflexivity.
Qed.


Fixpoint optim' (a : AExp) : AExp :=
  match a with
  | ALit n => ALit n
  | APlus (ALit x) (ALit y) => ALit (x + y)
  | APlus e1 e2 => APlus (optim' e1) (optim' e2)
  | ASub  e1 e2 => ASub  (optim' e1) (optim' e2)
  end.

Lemma optim'_sound (a : AExp) : aeval (optim' a) = aeval a.
Proof.
  induction a.
  all: try ( simpl; reflexivity ).
  all: try ( simpl; rewrite IHa1; rewrite IHa2; reflexivity ).
  destruct a1.
  destruct a2.
  destruct n.
  all: try ( simpl; reflexivity ).
  all: try ( simpl in IHa2; simpl; rewrite IHa2; reflexivity ).
  all: try ( simpl in IHa1; simpl; rewrite IHa1; rewrite IHa2; reflexivity ).
Qed.

(* exercise: create more optimisations and prove them sound! *)
						   
Require Import Nat.
Require Import Arith.

(* standard library documentation *)

(* See Arith.Le *)

Check Nat.le_refl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.pow_le_mono.
Check Nat.add_le_mono.

Lemma leaves_height (a : AExp) : leaves a <= 2 ^ height a.