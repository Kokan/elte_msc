

(* Piet programming language *)

(*

Coloure cycles:
* Hue Cycle: red -> yellow -> green -> cyan -> blue -> magenta -> red
* Lightness Cycle: light -> normal -> dark -> light
*)

Inductive Hue : Type := 
  | Red
  | Yellow
  | Green
  | Cyan
  | Blue
  | Magenta
  | Black
  | White
  .

Inductive Lightness : Type :=
  | Light
  | Normal
  | Dark
  .

Definition hue_cycle (h : Hue) : Hue :=
  match h with
  | Red => Yellow
  | Yellow => Green
  | Green => Cyan
  | Cyan => Blue
  | Blue => Magenta
  | Magenta => Red
  | Black => Black
  | White => White
  end.


Definition lightness_cycle (l : Lightness) : Lightness :=
  match l with
  | Light => Normal
  | Normal => Dark
  | Dark => Light
  end.

Lemma hue_one_loop (h : Hue) : (hue_cycle (hue_cycle (hue_cycle (hue_cycle (hue_cycle (hue_cycle h)))))) = h.
  destruct h.
  all: simpl.
  all: reflexivity.
Qed.


Lemma lightness_one_loop (l : Lightness) : (lightness_cycle (lightness_cycle (lightness_cycle l))) = l.
  destruct l.
  all: simpl.
  all: reflexivity.
Qed.


Lemma foo : forall A:Type, forall P:A->Prop, forall x y:A, (x=y) -> (P x = P y).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.



