Require Import core.
Require Import nat_example.

(** Okay, so let's talk about the most important inductive type in HoTT. *)

Inductive eq {A : Type} : A -> A -> Type :=
  refl x : eq x x.

(** We don't have to prove reflexivity because it's trivial. *)

(** This proof is just like the other examples we've done with inductive types,
    there are no new principles at work here.
    although it takes some work to see the resemblance. *)
Definition eq_sym : forall (A : Type) (x y : A), eq x y -> eq y x :=
  (** We don't bother introducing names for [x] and [y] because
   we don't need them. *)
  fun A _ _ eq_xy =>
    (** Because [eq] is an inductive type, we can only use it by
      pattern matching, it's the only thing we know how to do. *)
    (** The reason we didn't bother introducing names for [x] and [y] above
        is because only reason we care about the value of [x] and [y]
        is to specify the return type of the function -
        but the only variables you can use to specify the return type
        of the function are the ones you introduce using the [as] and [in]
        keywords. *)
    match eq_xy as _ in eq z z' return eq z' z with
    | refl a =>
       (** At this branch of the match statement, the variables [z] and [z']
           take on more concrete, specialized values for this branch,
           corresponding to the constructor. By definition [refl a : eq a a],
           so [z] becomes [a] and [z'] also becomes [a].

         But now, because [z] and [z'] are both [a], [eq z' z] is also [eq a a]!
         Again you can see this by entering tactic mode and doing a [refine]
         with the proof at this point. This means we can return [refl a],
         which is of the correct type.
         *)
        refl a
    end.

Definition eq_trans : forall (A : Type) (x y z : A), eq x y -> eq y z -> eq x z :=
  (** It's a common problem for intro proof students that they
      choose an induction hypothesis that is too weak. For example,
      they want to prove that [forall n, m, n + m = n + m] and so they
      pick some fixed [m] and try to prove by induction on [n] that
      [m + n = n + m]. But this doesn't work!

      Instead of trying to prove [0 + m = m + 0] and
      [(n + m) = (m + n) -> (S n + m) = (m + S n)],

      the induction hypothesis needs to be stronger:

      [forall m, 0 + m = m + 0]

      [(forall m, (n + m) = (m + n)) -> (forall m, (S n + m)= (m + S n))]

      Something similar happens here.
      We have to strengthen the induction hypothesis.
      What we really want to prove is:

      [forall (A : Type), forall (x y : A), eq x y ->
           forall z : A, y = z -> x = z].
   *)
  fun A _ _ z eq_xy eq_yz=>

    (** First we prove that
           forall z : A, y = z -> x = z. *)
    (match eq_xy as _ in eq x' y' return
          forall (z' : A), eq y' z -> eq x' z with
    | refl a =>
    (** At this point in the code, both x' and y' are equal to a,
       and we want to prove that for all z, a = z -> a = x. *)
        fun z' eq_az => eq_az
     end)
      (** Then we apply this to our z and eq_yz. *)
      z eq_yz.

(** Theorem: Functions preserve equality. *)
Definition fmap : forall (A B : Type) (f : A -> B) (a a' : A),
    eq a a' -> eq (f a) (f a') :=
  fun A B f _ _ eq_aa' =>
    match eq_aa' in eq x y return eq (f x) (f y) with
    | refl z =>
        (** At this point in the code, eq x y becomes eq z z;
           and we are trying to return a value of type eq (f z) (f z).
           But this is immediate by reflexivity. *)
        refl (f z)
    end.

(** The inductive type False has no constructors. *)
Inductive False := .

Definition explosion_principle (A : Type) : False -> A :=
  fun pf_false =>
    match pf_false with
    (** Here we return a value for each of the constructors for False.
       Since there are no constructors for false, the match statement
       has no cases. *)
    end.

(** The inductive type True has a single constructor. *)
Inductive True :=
| unit.

(** We end with a nontrivial theorem that requires a lemma,
    which we do using a let binding, as in Haskell or OCaml. *)
Definition true_is_not_false : eq tt ff -> False :=
  (** The proof of this goes by a standard trick. *)
  (** First, we define a family of dependent types on bool,
     P tt tt = True
     P ff tt = False
     P tt ff = False
     P ff ff = True
   *)
  let P : bool -> bool -> Type :=
    fun b1 b2 =>
      match b1, b2 with
      | tt, tt => True
      | ff, tt => False
      | tt, ff => False
      | ff, ff => True
      end
  in
  let lemma : (forall b1 b2 : bool, eq b1 b2 -> P b1 b2) :=
    fun _ _ eq_b1_b2 =>
      (match eq_b1_b2 in eq z1 z2 with
      | refl a => (** Return type of the function is now P a a *)
          match a as a' return P a' a' with
          | tt => (** Return type of the function is now P tt tt *)
              unit
          | ff => (** Return type of the function is now P ff ff *)
              unit
          end
      end)
  in
  (** Now that we've proven that P b1 b2 has a section for all p1 p2,
     we just apply it to the assumptions in the question.
   *)
  fun eq_tt_ff => lemma tt ff eq_tt_ff.
