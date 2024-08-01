(*|Here's some basic literate programming using the Alectryon framework.|*)

(** Here's a Coqdoc comment.*)

(** printing nat #<p>a</p>#*)

Section classical.
Definition mydef := nat.

(*|
A basic theorem:  :math:`\forall b : \mathsf{bool},\lnot\lnot b = b`
.. coq::
|*)

Theorem double_negation (b : bool) : negb (negb b) = b.
Proof.
destruct b.
{ reflexivity. }
{ reflexivity. }
Qed.

End classical.

(*|Here's a link to the definition of the boolean datatype. :coqid:`Boolean <Coq.Init.Datatypes.bool>`|*)
(*|
.. role:: mylib(coqid)
   :url: file:///home/patrick/forest/coq/html/$modpath.html#$ident

Here's a link to a definition in another file. :mylib:`Box <Strict.box>`
|*)
