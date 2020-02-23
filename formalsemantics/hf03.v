(* BEGIN FIX *)
Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Definition four : Nat := S (S (S (S O))).
Definition six  : Nat := S (S four).

Fixpoint f (n : Nat) : Nat :=
  match n with
  | O => O
  | S n => S (f n)
  end.

Lemma fid (a : Nat) : f a = a.
(* END FIX *)
Proof. induction a. all: simpl. reflexivity. rewrite IHa. reflexivity. Qed.
(* BEGIN FIX *)
Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.
Proof. reflexivity. Qed.

Lemma rightid (n : Nat) : n + O = n.
Proof. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma assoc (a b c : Nat) : (a + b) + c = a + (b + c).
Proof. induction a.
  - reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.

Lemma cong (f : Nat -> Nat)(a b : Nat) : a = b -> f a = f b.
Proof. intros. rewrite -> H. reflexivity. Qed.

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
(* END FIX *)
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa. reflexivity.
Qed.
(* BEGIN FIX *)
Lemma comm (a b : Nat) : a + b = b + a.
(* END FIX *)
(* In the inductive step, rewrite using (plus_r_s b a)! *)
Proof.
  induction a.
  - simpl. rewrite (rightid b). reflexivity.
  - rewrite <- (plus_r_s). simpl. rewrite IHa. reflexivity.
Qed.
(* BEGIN FIX *)
Fixpoint times (a b : Nat) : Nat :=
  match a with
  | O => O
  | S a' => b + times a' b
  end.

Notation "x * y" := (times x y)
  (at level 40, left associativity).

Lemma times_leftid (a : Nat) : S O * a = a.
(* END FIX *)
Proof. simpl. rewrite (rightid). reflexivity. Qed.
(* BEGIN FIX *)
Lemma times_rightid (a : Nat) : a * S O = a.
(* END FIX *)
Proof. induction a. simpl. reflexivity. simpl. rewrite IHa. reflexivity. Qed.
(* BEGIN FIX *)
Lemma times_leftzero (a : Nat) : O * a = O.
(* END FIX *)
Proof. simpl. reflexivity. Qed.
(* BEGIN FIX *)
Lemma times_rightzero (a : Nat) : a * O = O.
(* END FIX *)
Proof. induction a. simpl. reflexivity. simpl. rewrite IHa. reflexivity. Qed.
(* BEGIN FIX *)
Lemma rdistr (a b c : Nat) : (a + b) * c =  a * c + b * c.
(* END FIX *)
(* Use rewrite with assoc in the inductive step! *)
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite (assoc). rewrite (IHa). reflexivity.
Qed.
(* BEGIN FIX *)
Lemma times_assoc (a b c : Nat) : (a * b) * c = a * (b * c).
(* END FIX *)
(* Use rdistr in the inductive step! *)
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite (rdistr). rewrite IHa. reflexivity.
Qed.
(* BEGIN FIX *)
Lemma comm_helper (a b : Nat) : b + b * a = b * S a.
(* END FIX *)
(* You will have to use assoc and comm in the inductive step. *)
Proof.
  induction b.
  - simpl. reflexivity.
  -simpl. rewrite <- IHb. rewrite <- (assoc). rewrite <- (assoc). rewrite <- (comm b a). reflexivity.
Qed.
(* BEGIN FIX *)
Lemma times_comm (a b : Nat) : a * b = b * a.
(* END FIX *)
(* Use comm_helper in the inductive step. *)
Proof.
  induction a.
  - rewrite (times_leftzero). rewrite (times_rightzero). reflexivity.
  - rewrite <- (comm_helper). simpl. rewrite IHa. reflexivity.
Qed.
(* Facultative exercise: *)
Fixpoint pred (n : Nat) : Nat :=
  match n with
  | O => O
  | S n => n
  end.
(*
Lemma S_inj (a b : Nat) : S a = S b -> a = b.
(* Use cong pred! *)
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Definition P : Nat -> Prop := fun n =>
  match n with
  | O => True
  | S _ => False
  end.

Lemma O_S_O : ~ (S O <> O).

Lemma O_S_disj (a : Nat) : O <> S a.
*)

