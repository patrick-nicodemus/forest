(*|This text was written in an Alectryon comment.|*)
Definition mydef := nat.
Theorem double_negation (b : bool) : negb (negb b) = b.
Proof.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.
(*|Not too shabby.|*)
