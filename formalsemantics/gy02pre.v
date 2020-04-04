Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.


Definition one  : Nat := S O.
Definition two : Nat := S (S O).
Definition three : Nat := S (S (S O)).
Definition four : Nat := S (S (S (S O))).
Definition five : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Definition isOne (n : Nat) : bool := 
  match n with
  | S O => true
  | _ => false
  end.

Eval compute in isOne four.
Eval compute in isOne six.
Eval compute in isOne O.
Eval compute in isOne (S O).

Fixpoint twice (n : Nat) : Nat := 
   match n with
   | O => O
   | S n' => S (S (twice n'))
   end.

Eval compute in twice six.

Lemma SStwice : forall (n : Nat), S (S (S (twice n))) = S (twice (S n)).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.



Fixpoint f (n : Nat) : Nat := match n with
  | O => O
  | S n => f n
  end.

Check Type.

Lemma a (a : Nat) : f a = O.
Proof.
 induction a.
 - simpl. reflexivity.
 - simpl. rewrite IHa. reflexivity.
Qed.

(* Fixpoint f (n : Nat) : Nat := f n. *)

Fixpoint plus (n m : Nat) {struct n} : Nat :=
  match n with 
  | O => m
  | S n' => S (plus n' m)
  end.

Eval compute in plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.
Proof.
  simpl. reflexivity.
Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof.
 induction n.
 - simpl. reflexivity.
 - simpl. rewrite IHn. reflexivity.
Qed.

Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.

Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
Proof.
  intros a_eq_b.
  rewrite a_eq_b.
  reflexivity.
Qed.

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
Proof.
  intros.
  induction a0.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa0. simpl. reflexivity.
Qed.


Fixpoint max (a b : Nat) : Nat :=
  match a, b with
  | O, b => b
  | S a, O => S a
  | S a, S b => S (max a b)
  end.

Compute (max four six).

Lemma idmax : forall (n : Nat ), (max O n) = n.
 intros n.
 simpl.
 reflexivity.
Qed.

Lemma idleftmax : forall (n : Nat ), (max n O) = n.
 induction n.
 all: simpl. 
 all: reflexivity.
Qed.

Lemma comm (a b : Nat) : a + b = b + a.
Proof.
  induction a.
  - Check (rightid b). rewrite (rightid b). simpl. reflexivity.
  - rewrite <- (plus_r_s). simpl. rewrite IHa. reflexivity.
Qed.


Fixpoint pred (n : Nat) : Nat :=
  match n with
  | O => O
  | S n' => n'
  end.

(*Lemma S_inj (a b : Nat) : S a = S b -> a = b.
Proof.
  intros.*)


(*Definition P : Nat -> Prop := fun n => *)

(*Lemma O_S_disj (a : Nat) : O <> S a.
Proof. *)
  

Fixpoint times (a b : Nat) : Nat :=
  match a with
  | O => O
  | S O => b
  | S a' => b + (times a' b)
  end.

Notation "x * y" := (times x y)
  (at level 40, left associativity).

Lemma times_leftid (a : Nat) : S O * a = a.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma times_rightid (a : Nat) : a * S O = a.
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. induction a0.
    * simpl. reflexivity.
    * reflexivity.
Qed. 

Lemma times_leftzero (a : Nat) : O * a = O.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma times_rightzero (a : Nat) : a * O = O.
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl.  rewrite IHa. induction a0. all: auto.
Qed.


Lemma times_assoc (a b c : Nat) : (a * b) * c = a * (b * c).

(*Lemma times_comm (a b : Nat) : a * b = b * a.*)


(*Lemma decEq (a b : Nat) : a = b \/ a <> b.*)

*)

Inductive BinaryTree : Type :=
| Leaf (n : Nat)
| Node (l r : BinaryTree).

Definition tree : BinaryTree := Node (Node (Leaf one) (Node (Leaf  two) (Leaf three))) (Node (Leaf four) (Leaf five)).

Fixpoint height (t : BinaryTree) : Nat := 
  match t with
  | Leaf _ => O
  | Node t t' => one + (max (height t) (height t'))
  end.


Fixpoint leaves_count (t : BinaryTree) : Nat :=
  match t with
  | Leaf _ => one
  | Node l r => (leaves_count l) + (leaves_count r)
  end.

(*
 nehez HF:
  exp2 (height t)
  leaves_count t 
*)

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


Lemma sum1_2_eq : forall t : BinaryTree, sum1 t = sum2 t.
Proof.
  intros.
  induction t.
  - simpl. reflexivity.
  - simpl. rewrite <- IHt2. rewrite <- IHt1. rewrite (comm). reflexivity.
Qed.


Fixpoint exp2 (n : Nat) : Nat :=
  match n with
  | O => S O
  | S m => exp2 m + exp2 m (* 2*2^m *)
  end.

Lemma leaves_height (t : BinaryTree) :
  max (exp2 (height t)) (leaves_count t) =
  exp2 (height t).






