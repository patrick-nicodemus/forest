From elpi Require Export elpi.
From Coq.Init Require Import Notations.

Notation "x -> y" := (forall (_ : x), y).
