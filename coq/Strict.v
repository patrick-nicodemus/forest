(** In this document, I define something basic using StrictProp. *)

Inductive box (A: Type) : A -> SProp :=
  | Box a : box A a.
