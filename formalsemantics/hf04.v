(* BEGIN FIX *)
Inductive AExp : Type :=
| ALit (n : nat)
| APlus (a1 a2 : AExp)
| ASub (a1 a2 : AExp)
(* END FIX *)
| AMul (a1 a2 : AExp)
.

(* BEGIN FIX *)
Fixpoint aeval (a : AExp) : nat :=
match a with
 | ALit n => n
 | APlus a1 a2 => aeval a1 + aeval a2
 | ASub a1 a2 => aeval a1 - aeval a2
(* END FIX *)
 | AMul a1 a2 => aeval a1 * aeval a2
end.

(* BEGIN FIX *)
Example aeval_test1 : forall n : nat, aeval (ALit n) = n.
Proof. reflexivity. Qed.
(* END FIX *)

(* BEGIN FIX *)
Example aeval_test2 : forall n m : nat, aeval (APlus (ALit n) (ALit m)) = n + m.
Proof. reflexivity. Qed.
(* END FIX *)

(* Irj egy tesztet a szorzasra az osszeadas mintajara *)
Example aeval_test3 : forall n m : nat, aeval (AMul (ALit n) (ALit m)) = n * m.
Proof.
  reflexivity.
Qed.