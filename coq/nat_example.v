Require Import core.
(**
  This is a brief tutorial on Coq that does not require much
  understanding of tactic based theorem proving.
  It assumes some general familiarity with programming in a
  statically typed functional programming language such as OCaml or Haskell.
  This will help you
  understand Coq's type theory at a lower level than you would get
  from using the [apply] and [rewrite] tactics in proofs.
 
  We can define algebraic data types
  with the [Inductive] keyword.
  This is similar to the "data" keyword in Haskell, or
  the "type" keyword in OCaml.
 *)

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Local Notation "0" := O.
Local Notation "1" := (S O).
Local Notation "2" := (S (S O)).

Inductive bool : Type :=
| tt : bool
| ff : bool.

(** Basic recursion with natural numbers and booleans;
    pattern matching. *)

Definition is_zero : nat -> bool :=
  fun n =>
      match n with
      | O => tt
      | S _ => ff
      end.

Definition negb (b : bool) : bool :=
  match b with
  | tt => ff
  | ff => tt
  end.

(** In Coq, you can define recursive functions with the [fix] keyword.

    The [fix] keyword is similar to [fun] (lambda abstraction) except
    that it is used for recursive functions. It is necessary to mark a
    function as recursive.

    To motivate the use of a new keyword for defining recursive
    functions, notice that it would be very inconvenient to try and
    implement recursion using anonymous functions, as you have to give
    the function a name so it can call itself. *)

(** Define [n + m] by induction on [n]. *)
Definition add : nat -> nat -> nat :=
  fix add_recursive (n m: nat) : nat :=
       match n with
       | O => m
       | S n' => S (add_recursive n' m)
       end.

Notation "a + b" := (add a b) (at level 50, left associativity).

(** Coq doesn't permit arbitrary recursive functions,
    only functions that are defined by recursion on the structure
    of an inductively defined data type, such as natural numbers or lists.

    A function can only recursively call itself in the branches of
    a pattern-match, like above. Coq always identifies one particular
    argument of the recursive function call as the "decreasing" argument -
    the argument that gets pattern-matched each time, or unfolded.
    In the example above, n is the "structurally decreasing" argument,
    because it gets "unfolded" by one step with every recursive call,
    eventually terminating with zero.

    Coq is usually able to infer from context what the structurally
    decreasing argument is meant to be, but if it can't figure it out,
    you can explicitly hint it using the [struct] keyword, as below. *)
Check fix add_recursive (n m: nat) {struct n} : nat :=
       match n with
       | O => m
       | S n' => add_recursive n' (S m)
       end.
(** Prints [nat -> nat -> nat] *)

(** Just like in Haskell, inductive data types can be
    polymorphic in a type parameter. *)
Inductive list (A : Type) :=
| nil : list A
| cons : A -> list A -> list A.

(** After defining a function, you can mark arguments as implicit
    using the [Arguments] command.  *)
Check cons.
(** [cons : forall A : Type, A -> list A -> list A] *)

(** We don't want to supply the argument [A] every time so we mark it implicit.
    Coq is able to infer from context what [A] is. *)
Arguments cons {A} head tail.
Arguments nil {A}.

Check cons 2 nil.

(** If you want to temporarily make implicit arguments explicit,
    (for example, because Coq is having trouble inferring what it should be),
    put the [@] sign in front of the term. *)
Check @cons nat 2 (@nil nat).

Local Notation "[]" := nil.
Local Notation "head :: tail" := (cons head tail)
                                 (at level 70, right associativity).

Check 2 :: 1 :: 0 :: [].

Definition length (A : Type) : list A -> nat :=
  fix length_rec (l : list A) {struct l} :=
    match l with
    | nil => 0
    | cons head tail => S (length_rec tail)
    end.
(** Remember, [fix] is like [fun] except for recursive functions, and
    [{struct l}] is a hint to the Coq typechecker
    that the definition is by "structural recursion on the variable [l]".
    i.e., that the function is "decreasing" in [l] - the argument [l]
    gets smaller in every recursive function call.

    You do not have to include this because Coq can figure it out from
    context. I only include it to help you debug things, because often
    you print the definition of a term to see what's going on, and Coq
    will generally show you the "fully annotated" definitions and it
    is confusing / overwhelming if you don't understand the extra
    annotations. *)

Definition concatenate (A : Type) : list A -> list A -> list A :=
  fix concat_rec (l1 : list A) (l2 : list A) {struct l1} :=
    match l1 with
    | nil => l2
    | cons head tail => cons head (concat_rec tail l2)
    end.

(** The "Fixpoint" command is syntactic sugar for a recursive Definition.
    It's a bit more concise.
    The following illustrates this syntactic sugar.
    It is exactly equivalent to what we did above. *)
Fixpoint concat {A : Type} (l1 : list A) (l2 : list A) :=
  match l1 with
  | nil => l2
  | cons head tail => cons head (concat tail l2)
  end.

(** Because Coq is a dependently typed language, it's possible to use
    the Inductive keyword to generate _families_ of types, indexed by
    a variable.

    Here is an example where we use this feature to incorporate the
    length of a list as part of its type, which lets us use the type
    checker to enforce guarantees about the length of lists, such as
    guaranteeing that if a list of length n is appended to a list of
    length m, the result is of length n + m. *)

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall n : nat, A -> vector A n -> vector A (S n).

Arguments vnil {A}.
Arguments vcons {A} {n} head tail.

(** [vector] is both a polymorphic type (one can have a vector of [A]'s
    for all types [A]) and a dependent type, a family of types indexed by
    the natural numbers.

    It has two constructors: [vnil], which is an element of the type [vector A 0];
    and [vcons]. To define a function on the type of vectors,
    it suffices to define it on the constructors. *)

(** This function can be seen as a "verified" version of the concat
    function we defined earlier. The fact that this definition
    type-checks means that Coq has guaranteed that indeed the
    concatenation of a list of length [n] with a list of length [m] is of
    length [n + m]. *)
Definition vconcat (A : Type) {n : nat} (l1 : vector A n) {m : nat} (l2 : vector A m) : vector A (n + m) :=
  (** The type signature above is easy to read and reflects how we might
      want to use it, but giving every argument a name
      (fixing some specific [n] and [l1], as we did)
      is not really a good fit for defining
      functions by recursion. The fixpoint operator [fix] is used to define a
      function quantified over _all_ its inputs, not just the specific ones
      given to us; 
      so we're just going to define this function for _all_
      [n'] and [l1'], and then apply it to the specific [n] and [l1] given to us.
      I introduce new variable names in defining [vconcat_rec]
      to avoid confusion;
      you could reuse the same names, but it would just shadow the outer names.
  *)
  (fix vconcat_rec {n'} (l1' : vector A n') : vector A (n' + m) :=
     match l1' with
     | vnil => l2
     | vcons head tail => vcons head (vconcat_rec tail)
     end) n l1.

(** In the example above, if you remove [: vector A (n' + m)], it
    won't compile. Coq is unable to infer the return type unless it is
    explicitly annotated. As a general rule, if your code doesn't
    compile, adding more type annotations and filling in implicit
    arguments may help you get better error messages, and make the
    typechecker happy, _up to a point_.

    However, if you don't understand how to correctly communicate type
    annotations to the compiler, then all your efforts will be in
    vain, which is why it's so important to understand how to read and
    write dependent pattern matching type annotations in Coq - but, at
    the same time, this is probably one of the most challenging things
    about learning Coq.

    I learned how to do this by reading Adam Chlipala's explanation
    (#<a href="http://adam.chlipala.net/cpdt/html/MoreDep.html">here</a>#),
    which I
    think is very good; I'm just trying to explain it in my own words
    and give examples. Read the section
    "The One Rule of Dependent Pattern Matching"
    *)

(**
  Let's start with an example.
  [is_even] is a dependent type, a family of types indexed by the natural numbers.
  It has two constructors:
  - [z_is_even], which is an element of the type [s_even 0];
  - [ss_is_even], which is a function from [is_even n] to [is_even (S (S n))]
    for any natural number [n].
 *)

Inductive is_even : nat -> Type :=
| z_is_even : is_even 0
| ss_is_even : forall n : nat, is_even n -> is_even (S (S n)).

(** We can think of the is_even family of types as a predicate on the natural
    numbers. To prove that a number [n] is even, we construct an inhabitant 
    of the type [is_even n].*)

(**
    The bigger picture is that we have some base type, [A] (here [A] is [nat])
    and then an inductively generated dependent type [B : A -> Type].
    How can we map into and out of [B]?
    Well, constructing inhabitants of [B] should be the easy part, we just
    use the constructors.
    The nontrivial part is how do we map out of [B], i.e., structurally
    recurse on the dependent type?

    Say you have built a term:
    [a : A, b : B a |-  t(a,b) : C]

    What might the type of [t] be? [C] could be a constant type, or
    [C] could vary as a function of [a]. 
    In full generality, [C] could be a function of both [a] and [b].

    So, in writing down a function [t] of [a] and [b], we need to be able
    to express how the type of [t] varies as a function of [a] and [b].
    If [B] is an inductive data type with multiple cases,
    we need to express how [C] varies as a function of [a] and [b] in each
    of the possible cases of [b].

    For this we extend [match] with new syntax.
*)

Definition sum_even:
  forall n m : nat, is_even n -> is_even m -> is_even (n + m) :=
  fix sum_even_rec (n m : nat) (p : is_even n) (q : is_even m) : is_even (n + m) :=
    match p as b in is_even a return is_even (a + m) with
    | z_is_even => (* 1 *) q 
    | ss_is_even n' p' => (* 2 *) ss_is_even (n' + m) (sum_even_rec n' m p' q)
    end.

(** This example extends the [match] statement with new syntax, the
    keywords [as], [is] and [return].

    The basic meaning of [return] is clear: it specifies the return
    type of the match statement. But unlike languages such as Haskell
    or OCaml, the return type of the match statement is allowed to
    vary as a function of its argument, and so the type specified
    after the [return] keyword is allowed to depend on the input.

    The keyword [as] lets us declare a new variable, in this case [b],
    which refers to the input to the match; we can refer to the
    variable [b] in the return type, if the return type depends on the
    input. In this case, it doesn't: we are trying to build a term of
    type [is_even (n + m)], and the type [is_even (n + m)] doesn't
    depend on the proof [p]. So, we could have written an underscore _
    instead of [b], or even omitted [as b] altogether. 

    The keyword [in] also allows us to introduce one or more new
    variables, here called [a], which are the indexing arguments of
    the dependent type we're matching on.

    The return type is allowed to depend on both [a] and [b].
    The variables [a] and [b] cannot be referred to anywhere outside the
    definition of the return type - their only purpose is to explain
    how the return type varies with each branch of the pattern match.

    [a] and [b] will take on different values as a result of the different
    branches. In the first branch, (after the [| z_is_zero => ] ),
    [b] becomes equal to the constant [zz_is_even], and [a] becomes equal to 0.
    Thus, at [q] , the return type is
    [is_even (0 + m)].
    In the second branch, [a] becomes equal to [(S (S n'))] and
    [b] is equal to [ss_is_even n' p']; thus, the return type is
    [is_even (S (S n') + m)].

    We can confirm this by entering proof mode, putting holes
    to replace [q] and [ss_is_even (...)],
    and using [refine] to fill in everything but the holes.
    The interactive proof mode shows us what the type of each hole is.
    As you can see, it depends on the value of the variable [a]. 
 *)

From Coq Require Import Ltac.
Definition sum_even' :
  forall n m : nat, is_even n -> is_even m -> is_even (n + m).
Proof.
  refine (fix sum_even_rec (n m : nat) (p : is_even n) (q : is_even m) :
       is_even (n + m) :=
       match p as b in is_even a return is_even (a + m) with
       | z_is_even => (* 1 *) _
       | ss_is_even n' p' => (* 2 *) _
       end).
Abort.

(** Let's try to prove the induction principle for the natural numbers by
    using dependent pattern matching. We can often get away without type
    annotations - see what happens when you delete [as w return P w].
 *)

Definition nat_induction :
  forall (P  : nat -> Type),
    (P 0) -> (forall n, P n -> P (S n)) -> (forall n, P n) :=
  (* [P], [pf_0] and [pf_succ] are all "constants" from the point of view of the
     induction, so we start by introducing them, as they don't have to occur
     under/inside the fixpoint recursion.
   *)
  fun P pf_0 pf_succ =>
    fix nat_rec (n : nat) : P n :=
    match n as w return P w with
    | 0 => (* 1 *) pf_0
    | S n' => (* 2 *) pf_succ n' (nat_rec n')
    end.

(* In this example, the return type depends on [n], so we use the [as]
   keyword to introduce a new variable [w] to refer to [n], and we refer to [w]
   in the return type. [nat] is not a dependent type, so there is no
   need for the [in nat] clause, because there is no "indexing
   parameter" of the inductive type.

   One way of understanding why the variable [w] is necessary is that
   the input [n] won't always be a variable, it could be a more
   complicated term like [S (S n)]. It is just a coincidence that it
   happens to be a variable in these examples, but we could plug in
   any term whose type is [nat]. In this case, it doesn't really make
   sense to talk about the way [P] depends on the _term_ as a function of
   the _branch_.

   You can think of the input [n] as somehow "opaque", the
   typechecker does not look inside it when checking the type of the
   return. The return type is only controlled by the variables
   introduced in the [in] and [as] clauses.

   I think that [match n return P n] is shorthand for [match n as n
   return P n]. As long as we keep in mind that these are two
   semantically distinct variables and one is shadowing the other, this
   seems fine. *)

(** Try the same trick here of looking at the return type using [refine]
   to see how the context and return type changes inside the branches
   [| tt => _ ] and [| ff => _ ]. *)
  
Definition bool_induction :
  forall P : bool -> Type,
    P tt -> P ff -> forall b : bool, P b :=
  fun P pf_tt pf_ff b =>
  match b as b' return P b' with
  | tt => (* 1 *) pf_tt
  | ff => (* 2 *) pf_ff
  end.

