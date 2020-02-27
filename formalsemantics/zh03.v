(* BEGIN FIX *)
Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint twice (n : Nat) : Nat :=
  match n with
  | O => O
  | S n => S (S (twice n))
  end.

Fixpoint plus (n m : Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y) (at level 50, left associativity).

Lemma plus_r_s : forall (a b : Nat), S a + b = a + S b.
Proof. intros. induction a.
  - reflexivity.
  - simpl. simpl in IHa. rewrite -> IHa. reflexivity.
Qed.

Lemma twice_prop (a : Nat) : twice a = a + a.
(* END FIX *)
(* Hint: use plus_r_s in the inductive step! *)
Proof.
  induction a.
  - simpl. reflexivity.
  -  simpl. rewrite IHa. rewrite <- (plus_r_s). simpl. reflexivity.
Qed.

(* Password: almafa *)