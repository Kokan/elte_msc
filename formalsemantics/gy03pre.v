Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y)
  (at level 50, left associativity).


Fixpoint sum1 (t : BinaryTree) : Nat :=
match t with
| Leaf n => n
| Node l r => sum1 l + sum1 r
end.

Fixpoint sum2 (t : BinaryTree) : Nat :=
match t with
| Leaf n => n
| Node l r => sum2 r + sum2 l
end.

Lemma rightid (x : Nat) : x + O = x.
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_r_S : forall (a b : Nat), a + S b = S (a + b).
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.

Lemma plus_comm (x y : Nat) : x + y = y + x.
Proof.
  induction x.
  - simpl. rewrite (rightid). reflexivity.
  - simpl. rewrite (plus_r_S). rewrite IHx. reflexivity.
Qed.

Lemma sum1_2_eq : forall t : BinaryTree, sum1 t = sum2 t.
Proof.
  intros.
  induction t.
  - simpl.  reflexivity.
  - simpl. rewrite <- (IHt2). rewrite (IHt1). rewrite (plus_comm). reflexivity.
Qed. 

From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat.

Check nat.

(* InnentĹl kezdve hasznĂĄljuk az STDLB NAT-jĂĄt *)
(* Aritmetikai nyelv formalizĂĄlĂĄsa, BNF: *)
(*a ::= n | a1 + a2 | a1 - a2*)
(*a ::= alit(n) | plus(a1,a2) | sub(a1,a2)*)
Inductive AExp : Type :=
 | ALit (n : nat)
 | APlus (n m : AExp)
 | ASub ( n m : AExp)
.

(* Checkek *)

(* Hogyan tudunk kiĂŠrtĂŠkelni aritmetikai kifejezĂŠseket --> denotĂĄciĂłs szemantika *)
Fixpoint aeval (a : AExp) : nat :=
  match a with
  | ALit n => n
  | APlus n m => (aeval n) + (aeval m)
  | ASub n m => (aeval n) - (aeval m)
  end.

Fixpoint leaves_count (a : AExp) : nat := 
  match a with
  | ALit _ => 1
  | APlus n m => (leaves_count n) + (leaves_count m)
  | ASub n m => (leaves_count n) + (leaves_count m)
  end.

Definition myA1 := (APlus (ALit 1) (ALit 2)).
Definition myA2 := (ASub (APlus (ALit 5) (ALit 7)) (ALit 42)).

Eval compute in leaves_count(myA1).
Eval compute in leaves_count(myA2).



Lemma leaf_l_r: forall (a1 a2 : AExp), leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
 intros.
 simpl.
 Search Nat.
 rewrite (Nat.add_comm).
 reflexivity.
Qed.

Lemma leaf_l_r_ind: forall (a1 a2 : AExp), leaves_count (APlus a1 a2) = leaves_count (APlus a2 a1).
Proof.
  intros.
  induction a1.
  - simpl. Search "+" S. rewrite (Nat.add_1_r). reflexivity.
  - simpl. rewrite (Nat.add_comm). reflexivity.
  - simpl. rewrite (Nat.add_comm). reflexivity.
Qed. 



