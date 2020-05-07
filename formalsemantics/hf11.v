(* BEGIN FIX *)
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

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

Coercion avar : string >-> aexp.
Coercion alit : nat >-> aexp.
Notation "x + y"     := (aplus x y) (at level 50, left associativity).
Notation "x - y"     := (aminus x y) (at level 50, left associativity).
Notation "x * y"     := (amult x y) (at level 40, left associativity).
Definition bool2bexp (b : bool) : bexp := if b then btrue else bfalse.
Coercion bool2bexp : bool >-> bexp.
Notation "x & y" := (band x y) (at level 81, left associativity).
Notation "'~' b" := (bnot b) (at level 75, right associativity).
Notation "x == y" := (beq x y) (at level 70, no associativity).
Notation "x <= y" := (bleq x y) (at level 70, no associativity).
Notation "'SKIP'"    := cskip.
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" := (cif b c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (cwhile b c) (at level 80, right associativity).
Notation "x '::=' a" := (cassign x a) (at level 60).
Notation "c1 ;; c2"  := (cseq c1 c2) (at level 80, right associativity).

Definition X : string := "X"%string.
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

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

Inductive result : Type :=
  | final : state -> result
  | outoffuel : state -> result.

Fixpoint ceval (c : cmd)(s : state)(n : nat) : result := match n with
  | O => outoffuel s
  | S n' => match c with
    | cskip       => final s
    | cif b c1 c2 => if beval b s then ceval c1 s n' else ceval c2 s n'
    | cwhile b c  => if beval b s then match ceval c s n' with
                                       | final s' => ceval (cwhile b c) s' n'
                                       | r => r
                                       end
                                  else final s
    | cassign x a => final (update x (aeval a s) s)
    | cseq c1 c2  => match ceval c1 s n' with
                     | final s' => ceval c2 s' n'
                     | r => r
                     end
    end
 end.

Reserved Notation "| s , st |=> st'" (at level 50).
Inductive cevalb : cmd -> state -> state -> Prop :=

  | cevalb_skip (s : state) :

       (*------------*)
       | SKIP , s |=> s

  | cevalb_assign (x : string)(a : aexp)(s : state) :

       (*------------------------------------*)
       | x ::= a , s |=> update x (aeval a s) s

  | cevalb_seq (c1 c2 : cmd)(s s' s'' : state) : 

       | c1 , s |=> s'  ->  | c2 , s' |=> s''  ->
       (*------------------------------------*)
              | c1 ;; c2 , s |=> s''

  | cevalb_if_true (b : bexp)(c1 c2 : cmd)(s s' : state) :

       beval b s = true -> | c1 , s |=> s' ->
       (*------------------------------------*)
       | TEST b THEN c1 ELSE c2 FI , s |=> s'

  | cevalb_if_false (b : bexp)(c1 c2 : cmd)(s s' : state) :

       beval b s = false -> | c2 , s |=> s' ->
       (*------------------------------------*)
       | TEST b THEN c1 ELSE c2 FI , s |=> s'

  | cevalb_while_false (b : bexp)(c : cmd)(s : state) :

           beval b s = false       ->
       (*------------------------*)
       | WHILE b DO c END , s |=> s

  | cevalb_while_true (b : bexp)(c : cmd)(s s' s'' : state) :

       beval b s = true                  ->
       | c , s |=> s'                    ->
       | WHILE b DO c END , s' |=> s''   ->
       (*---------------------------*)
       | WHILE b DO c END , s |=> s''

where "| c , s |=> s'" := (cevalb c s s').

Lemma l1 : exists c, exists s1, exists s2, | c , s1 |=> s2 /\ | c , s2 |=> s1.
(* END FIX *)
Proof.
  exists SKIP. exists empty. exists empty.
  split.
  all: apply cevalb_skip.
Qed.

(* BEGIN FIX *)
Definition Equiv0 (c1 c2 : cmd) : Prop := forall s,
  exists s1 s2, | c1 , s |=> s1 /\ | c2 , s |=> s2 /\ forall x, s1 x = s2 x.

Lemma l2 : Equiv0 (SKIP ;; SKIP) SKIP.
(* END FIX *)
Proof.
  unfold Equiv0. intro. exists s. exists s.
  split. 2: split.
  3: { intro. reflexivity. }
  1: apply cevalb_seq with s.
  all: apply cevalb_skip.
Qed.

(* BEGIN FIX *)
Lemma l3 : forall c1 c2, Equiv0 (WHILE false DO c1 END) (WHILE false DO c2 END).
(* END FIX *)
Proof.
  intros. unfold Equiv0. intro. exists s. exists s.
  split. 2: split.
  3: { intro. reflexivity. }
  all: apply cevalb_while_false.
  all: reflexivity.
Qed.

(* tipp: destruct VALAMI eqn:H. *)
(* BEGIN FIX *)
Lemma l4 : forall b, Equiv0 (TEST b THEN X ::= 1 ELSE X ::= 1 FI) (X ::= 1).
(* END FIX *)
Proof.
  intro. unfold Equiv0. intro. exists (update X 1 s). exists (update X 1 s).
  split. 2: split.
  3: { intro. reflexivity. }
  2: { apply cevalb_assign. }
  { case_eq (beval b s).
    { intro. apply cevalb_if_true.
      { exact H. }
      { apply cevalb_assign. } }
    { intro. apply cevalb_if_false.
      { exact H. }
      { apply cevalb_assign. } } }
Qed.

(* BEGIN FIX *)
Lemma l5 : Equiv0 (X ::= Y ;; X ::= X + 1) (X ::= Y + 1).
(* END FIX *)
Proof.
  unfold Equiv0. intro. exists (update X ((update X (s Y) s) X + 1) (update X (s Y) s)). exists (update X (s Y + 1) s).
  split. 2: split.
  { apply cevalb_seq with (update X (s Y) s).
    { apply cevalb_assign. }
    { apply cevalb_assign. } }
  { apply cevalb_assign. }
  { intro. unfold update. destruct (string_dec X x). destruct (string_dec X X). 
    { reflexivity. }
    { unfold not in n. destruct n. reflexivity. }
    { reflexivity. } }
Qed. 

(* BEGIN FIX *)
Lemma l6 : forall a, Equiv0 (X ::= a ;; X ::= X + 1) (X ::= a + 1).
(* END FIX *)
Proof.
  intro a.
  unfold Equiv0. intro. exists (update X ((update X (aeval a s) s) X + 1) (update X (aeval a s) s)).  exists (update X ((aeval a s) + 1) s).
  split. 2: split.
  { apply cevalb_seq with (update X (aeval a s) s).
    { apply cevalb_assign. }
    { apply cevalb_assign. } }
  { apply cevalb_assign. }
  { intro. unfold update. destruct (string_dec X x). destruct (string_dec X X).
    { reflexivity. }
    { unfold not in n. destruct n. reflexivity. }
    { reflexivity. } }
Qed.

(* BEGIN FIX *)
Lemma l7 : ~ forall a, Equiv0 (X ::= a + 1 ;; X ::= a) (X ::= a).
(* END FIX *)
Proof.
  unfold Equiv0; intro.

  destruct (H X empty); destruct H0 ; destruct H0; destruct H1.

  inversion H1; simpl in H6.

  inversion H0; inversion H9; inversion H12; rewrite <- H16 in H20; simpl in H20.

  rewrite <- H20 in H2; 
  rewrite <- H6 in H2.

  pose proof (H2 X).
  unfold update in H21; unfold empty in H21; simpl in H21.
  discriminate H21.
Qed.



