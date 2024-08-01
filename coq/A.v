(** printing nat $\mathbb{N}$ #\(\mathbb{N}\)# *)
(** printing negb $\lnot$ #\(\lnot\)# *)
(** Here's a Coqdoc comment.*)
Require Strict.
Section classical.
(** Clicking on [nat] below takes you to the definition of [nat] in the stdlib. *)
Definition mydef := nat.
(** Clicking on [Strict.box] below takes you to the definition of [Strict.box] in another file in this library. *)
Definition box := MyTheory.Strict.box.

(** A basic theorem: $\forall b : \mathsf{bool},\lnot\lnot b = b$#\(\forall b : \mathsf{bool},\lnot\lnot b = b\)#. *)

Theorem double_negation (b : bool) : negb (negb b) = b.
Proof.
destruct b.
{ reflexivity. }
{ reflexivity. }
Qed.
End classical.

(** Cool. *)
