(* BEGIN FIX *)
Inductive Bool : Type :=
  | true  : Bool
  | false : Bool.

Definition notb (b : Bool) : Bool :=
  match b with
  | true => false
  | false => true
  end.

Lemma notnot : forall (a : Bool), notb a = (notb (notb (notb a))).
(* END FIX *)
Proof.
  intros a.
  destruct a.
  all: simpl.
  all: reflexivity.
Qed.