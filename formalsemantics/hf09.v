(* BEGIN FIX *)
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(*
BNF szintaxis:

a,a1,a2,... ::= n | x | a1 + a2 | a1 - a2 | a1 * a2
b,b1,b2,... ::= true | false | b1 && b2 | ~b | a1 = a2 | a1 <= a2
c,c1,c2 ::= SKIP | IF b THEN c1 ELSE c2 | WHILE b DO c END | x ::= a | c1 ;; c2
*)

(* Coq szintaxis: *)

Inductive aexp : Type :=
  | alit (n : nat)
  | avar (x : string)
  | aplus (a1 a2 : aexp)
  | aminus (a1 a2 : aexp)
  | amult (a1 a2 : aexp).
Inductive bexp : Type :=
| btrue
| bfalse
| band (b1 b2 : bexp)
| bnot (b : bexp)
| beq (a1 a2 : aexp)
| bleq (a1 a2 : aexp).
Inductive cmd : Type :=
| cskip
| cif (b : bexp) (c1 c2 : cmd)
| cwhile (b : bexp) (c : cmd)
| cassign (x : string) (a : aexp)
| cseq (c1 c2 : cmd).

Declare Scope myscope.

Coercion avar : string >-> aexp.
Coercion alit : nat >-> aexp.
Notation "x + y"     := (aplus x y) (at level 50, left associativity) : myscope.
Notation "x - y"     := (aminus x y) (at level 50, left associativity) : myscope.
Notation "x * y"     := (amult x y) (at level 40, left associativity) : myscope.
Definition bool2bexp (b : bool) : bexp := if b then btrue else bfalse.
Coercion bool2bexp : bool >-> bexp.
Notation "x & y" := (band x y) (at level 81, left associativity) : myscope.
Notation "'~' b" := (bnot b) (at level 75, right associativity) : myscope.
Notation "x == y" := (beq x y) (at level 70, no associativity) : myscope.
Notation "x <= y" := (bleq x y) (at level 70, no associativity) : myscope.
Notation "'SKIP'"    := cskip : myscope.
Notation "'IF' b 'THEN' c1 'ELSE' c2 'FI'" := (cif b c1 c2) (at level 80, right associativity) : myscope.
Notation "'WHILE' b 'DO' c 'END'" := (cwhile b c) (at level 80, right associativity) : myscope.
Notation "x '::=' a" := (cassign x a) (at level 60) : myscope.
Notation "c1 ;; c2"  := (cseq c1 c2) (at level 80, right associativity) : myscope.

Definition X : string := "X"%string.
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

Open Scope myscope.

Definition fac : cmd :=
  X ::= 1 ;;
  Y ::= 1 ;;
  WHILE Y <= Z DO
    X ::= X * Y ;;
    Y ::= Y + 1
  END.

Close Scope myscope.

(* Ird at fac'-t ugy, hogy fac-al megegyezzen, de a csunya jelolessel! *)
Definition fac' : cmd :=
(* END FIX *)
(cseq 
  (cassign X (alit 1))
  (cseq 
    (cassign Y (alit 1))
       (cwhile (bleq (avar Y) (avar Z))
               (cseq
                 (cassign X (amult (avar X) (avar Y)))
                 (cassign Y (aplus (avar Y)  (alit 1))
))))).
(* BEGIN FIX *)
Example facVsFac' : fac = fac'. reflexivity. Qed.

(* denotacios szemantika *)

Definition state : Type := string -> nat.
Definition empty : state := fun x => 0.
Definition update (x:string)(n:nat)(s:state) : state :=
  fun x' => match string_dec x x' with
  | left  e => n
  | right e => s x'
  end.
Fixpoint aeval (a : aexp)(s : state) : nat :=
match a with
| alit n => n
| avar x => s x
| aplus a1 a2 => (aeval a1 s) + (aeval a2 s)
| aminus a1 a2 => (aeval a1 s) - (aeval a2 s)
| amult a1 a2 => (aeval a1 s) * (aeval a2 s)
end.
Fixpoint beval (b : bexp)(s : state) : bool :=
match b with
 | btrue => true
 | bfalse => false
 | band b1 b2 => (beval b1 s) && (beval b2 s)
 | bnot b => negb (beval b s)
 | beq a1 a2 => aeval a1 s =? aeval a2 s
 | bleq a1 a2 => aeval a1 s <=? aeval a2 s
end.
Fixpoint ceval (c : cmd)(s : state)(n : nat) : state :=
match n with
| O => s
| S n' =>
  match c with
   | cskip => s
   | cif b c1 c2 => if beval b s
                    then (ceval c1 s n')
                    else (ceval c2 s n')
   | cassign x a => update x (aeval a s) s
   | cseq c1 c2 => ceval c2 (ceval c1 s n') n'
   | cwhile b c => if beval b s
                    then ceval (cwhile b c) (ceval c s n') n'
                    else s
  end
end.

Open Scope myscope.

Example prog1 : exists (c : cmd), forall (n : nat),
  ceval c (update X n empty) 10 X = (n + 1)%nat.
exists (X ::= X + 1). intros. simpl. reflexivity. Qed.

(* Irj programot, mely Y-ba beteszi X ketszereset! *)
Example prog2 : exists (c : cmd), forall (n : nat),
  ceval c (update X n empty) 10 Y = (2 * n)%nat.
(* END FIX *)
Proof.
  exists (Y ::= 2 * X).
  intros.
  simpl.
  reflexivity.
Qed.


(* BEGIN FIX *)
Definition prog3 : cmd :=
(* END FIX *)
WHILE Z == 1 DO Y ::= 1 END;;
WHILE Z == 2 DO Y ::= 3 END;;
WHILE Z == 3 DO Y ::= 6 END;;
WHILE Z == 4 DO Y ::= 10 END;;
WHILE Z == 5 DO Y ::= 15 END;;
WHILE Z == 6 DO Y ::= 21 END.

Compute ceval prog3 (update Z 4 empty) 10 Y.
Compute ceval prog3 (update Z 4 empty) 10 X.

(* BEGIN FIX *)
Lemma prog3Test1 : ceval prog3 (update Z 1 empty) 10 Y =  1. reflexivity. Qed.
Lemma prog3Test2 : ceval prog3 (update Z 2 empty) 10 Y =  3. reflexivity. Qed.
Lemma prog3Test3 : ceval prog3 (update Z 3 empty) 10 Y =  6. reflexivity. Qed.
Lemma prog3Test4 : ceval prog3 (update Z 4 empty) 10 Y = 10. reflexivity. Qed.
Lemma prog3Test5 : ceval prog3 (update Z 5 empty) 10 Y = 15. reflexivity. Qed.
Lemma prog3Test6 : ceval prog3 (update Z 6 empty) 10 Y = 21. reflexivity. Qed.

Definition prog4 (a b : nat) : cmd := Y ::= 1 ;; WHILE X + 1 <= b DO Y ::= Y * a ;; X ::= X + 1 END.

Definition f (a b : nat) : nat :=
(* END FIX *)
a^b.

(* BEGIN FIX *)
Lemma prog4Test1 : ceval (prog4 2 0) empty 10 Y = f 2 0. reflexivity. Qed.
Lemma prog4Test2 : ceval (prog4 2 1) (update Z 1 empty) 10 Y = f 2 1. reflexivity. Qed.
Lemma prog4Test3 : ceval (prog4 2 2) (update Z 1 empty) 10 Y = f 2 2. reflexivity. Qed.
Lemma prog4Test4 : ceval (prog4 2 3) (update Z 1 empty) 10 Y = f 2 3. reflexivity. Qed.
Lemma prog4Test5 : ceval (prog4 2 4) (update Z 1 empty) 10 Y = f 2 4. reflexivity. Qed.
Lemma prog4Test6 : ceval (prog4 3 1) (update Z 1 empty) 10 Y = f 3 1. reflexivity. Qed.
Lemma prog4Test7 : ceval (prog4 3 2) (update Z 1 empty) 10 Y = f 3 2. reflexivity. Qed.
Lemma prog4Test8 : ceval (prog4 3 3) (update Z 1 empty) 10 Y = f 3 3. reflexivity. Qed.
Lemma prog4Test9 : ceval (prog4 3 4) (update Z 1 empty) 10 Y = f 3 4. reflexivity. Qed.
(* END FIX *)