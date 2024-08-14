(** printing nat $\mathbb{N}$ #\(\mathbb{N}\)# *)
(** printing negb $\lnot$ #\(\lnot\)# *)
(** Here's a Coqdoc comment.*)
From Coq Require Datatypes.
From Coq Require Import Ltac.

Require Import nat_example.
Require Import eq_example.


Section classical.
(** Clicking on [Datatypes.nat] below takes you to the definition of [nat] in the stdlib. *)
Definition mydef := Datatypes.nat.

(** Clicking on [nat_example.bool] below takes you to the definition of [nat_example.bool] in another file in this library. *)
Definition bool := MyTheory.nat_example.bool.

(** A basic theorem: $\forall b : \mathsf{bool},\lnot\lnot b = b$#\(\forall b : \mathsf{bool},\lnot\lnot b = b\)#. *)

Theorem double_negation (b : bool) : eq (negb (negb b)) b.
Proof.
destruct b.
{ refine (refl _). }
{ refine (refl _). }
Qed.
End classical.

(** Cool. *)
