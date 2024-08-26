From Coq Require Import Prelude.

Require Import core.
From Coq.Classes Require Import CRelationClasses.
From elpi Require Import elpi.

(** Let's try and learn some Elpi. *)
(** Elpi is a logic programming language, it is a variant of Prolog
    which extends Prolog with functional features like lambda abstraction.

    This is mostly for my own benefit, but you may gain something by following along
    and watching me solve some simple problems using Elpi.

    A good place to start with Elpi is the tutorials:
    - #<a href="https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html">Tutorial on the Elpi programming language</a>#
    - #<a href="https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html">Tutorial on higher-order abstract syntax for Coq terms</a>#
    - #<a href="https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_command.html">Tutorial on Coq commands</a>#
    - #<a href="https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html">Tutorial on Coq tactics</a>#
    
    In order to use Elpi to write tactics, you will need to constantly reference the Coq/Elpi API to see
    how to accomplish certain things. The functionality available is spread out over a mix of Elpi files in the Coq-Elpi Github repository. Two important ones are

    - #<a href="https://github.com/LPCIC/coq-elpi/blob/2ef66b2640af1e3ef2e859f7b49b40d47272e10a/builtin-doc/coq-builtin.elpi">coq-builtin.elpi</a>#
    - #<a href="https://github.com/LPCIC/coq-elpi/blob/2ef66b2640af1e3ef2e859f7b49b40d47272e10a/elpi/coq-HOAS.elpi">coq-HOAS.elpi</a>#


    You may need to consult other files in the same coq-elpi/elpi directory to find definitions.

    Let's first understand the way Elpi models the domain. A [goal] in Elpi is
    documented 
    #<a href="https://github.com/LPCIC/coq-elpi/blob/2ef66b2640af1e3ef2e859f7b49b40d47272e10a/builtin-doc/coq-builtin.elpi">here</a>#.

    From glancing through the codebase, it seems like an idiom is that,
    for "algebraic data types" with one constructor,
    you give the constructor the same name as the type (a kind of punning).
    In particular the type [goal] has a single constructor, also called [goal].

    This goal wraps the following arguments:
    - the goal context
    - the "trigger" argument
    - the goal formula (the type we are trying to construct an inhabitant of)
    - the current proof, which is allowed to depend on the context hypotheses
    - the list of arguments passed to the parent tactic

    We put the "algebraic data types" in quotes because I think 
    there is no exhaustiveness checking for constructors.
 *)

Elpi Program __ lp:{{
    type goal goal-ctx -> term -> term -> term -> list argument -> goal.
}}.

Elpi Tactic intro1.

(** Our first example will match the goal to a product type,
    and, if it is a product we will refine it using an application.
    The Coq [forall] binder is represented in Elpi using the
    [prod] constant, 
    #<a href="https://github.com/LPCIC/coq-elpi/blob/2ef66b2640af1e3ef2e859f7b49b40d47272e10a/builtin-doc/coq-builtin.elpi">here</a># .
    
    The term [forall (x: A), B] would be represented as something like

    [prod `x` {{ A }} (y\ {{ B(y) }})]
    
    where the dependence of [B] on [x] is captured by making it a function.

    It takes a (meaningless) name, the type of the parameterizing input,
    and the return type expressed as a function of the input.
*)

Elpi Accumulate lp:{{
    solve (goal _ _ (prod _ _ _) _ _ as G) GL :- 
        refine (fun `X` _ _) G GL.
}}.
Elpi Typecheck.

From Coq Require Import Logic Datatypes.
Goal forall x y : nat, x = x.
Proof.
    elpi intro1.
    elpi intro1.
    (** Hypotheses: [X, elpi_ctx_entry_1_ : nat] *)
    Abort.

Elpi Tactic intro2.
(** Same, except we introduce a fresh identifier.*)
Elpi Accumulate lp:{{
    solve (goal _ _ (prod _ _ _) _ _ as G) GL :- 
        % Introduce a fresh identifier with "x" as its root.
        coq.ltac.fresh-id "x" _ X,
        % Get the name of the identifier.
        coq.id->name X Y,
        % Move the name Y into the current context.
        refine (fun Y _ _) G GL.
}}.

Elpi Typecheck.
Goal forall x y : nat, x = x.
Proof.
    elpi intro2.
    elpi intro2.
    Abort.

Elpi Tactic intro3.
(** Accept an argument telling us what the input should be.*)
Elpi Accumulate lp:{{
    solve (goal _ _ (prod _ _ _) _ (str Arg :: _) as G) GL :- 
        coq.ltac.fresh-id Arg _ X,
        coq.id->name X Y,
        refine (fun Y _ _) G GL.
}}.

Elpi Typecheck.
Goal forall x y : nat, x = x.
Proof.
    elpi intro3 a.
    elpi intro3 a.
    (** Hypotheses [a,a0 : nat]*)
    Abort.

Elpi Tactic intro4.
(** If the goal is a definition, unfold it to see if it exposes a forall clause. *)
Elpi Accumulate lp:{{
    solve (goal _ _ Goal _ _ as G) GL :- 
        % Try to unfold Goal and get the identifier for a constant
        Goal = global (const C),
        % Try to unwrap the definition of the constant C, 
        % failing if the constant is opaque
        coq.env.const-body C (some Body),
        % Proceed if the body is a forall type
        Body = prod _ _ _,
        refine (fun `a` _ _) G GL.
}}.
Elpi Typecheck.

Definition adef := forall x :nat, x = x.
Goal adef.
    elpi intro4.
    Abort.

(** A nice generalization of intro4 would be to unfold the top term recursively,
    repeatedly simplifying the term until the pattern is found.
    It looks like the functions in coq-elpi/elpi/elpi-reduction.elpi 
    can help with this.
 *)

Elpi Tactic rewrite1.

(** Eq is a constant from the global environment whose type is an equality proof 
    [a = b]. Rewrite all occurrences of [b] to [a], going from right to left. 
    Note that all the rewrite examples currently use Paulin-Mohring equality.  *)

Elpi Accumulate lp:{{
    solve (goal _ _ GoalType _ [trm Eq] as G) GL :-
        % Unpack Eq and get the global reference inside 
        Eq = global Gref,
        % EqTy is the declared type of Gref
        coq.env.typeof Gref EqTy,
        % EqTy is the type X = Y for X, Y : Ty
        EqTy = {{ @eq lp:Ty _ lp:Y }},
        % Ty = {{ lp:{{_}} = lp:{{_}}  }},
        % type match term -> term -> list term -> term.
        % match t p [branch])
        % This function is from coq-elpi/elpi/coq-lib.elpi
        pi y\ copy Y y =>
            copy GoalType (Goalfn y),
            refine (match 
                Eq
                (fun _ Ty (a\ 
                   fun _ EqTy (_\
                     Goalfn a
                )))
        [{{_}}]) G GL.
}}.
Elpi Typecheck.


Theorem abc : 3 = 5 - 2.
Proof.
    exact eq_refl.
Qed.

Goal forall A : Prop, 5 - 2 = 5 - 2 -> A.
Proof.
    elpi rewrite1 (abc).
    Abort.

Elpi Tactic rewrite2.
(** Argument is the name of a hypothesis in the context,
    whose type is of the form forall (x : A), P = Q *)
Elpi Accumulate lp:{{
    solve (goal Ctx _ GoalType _ [trm Eq] as G) GL :-
        std.mem Ctx (decl Eq _ Ty),
        Ty = prod _ A (c\ {{ @eq lp:S lp:{{ Q0 c}} lp:{{Q c}} }}),
        Hole = {{ _ }}, 
        coq.typecheck Hole A ok,
        pi x\ (copy J x :- 
            coq.unify-leq (Q Hole) J ok) => 
            copy GoalType (P x),
            if (occurs x (P x))
            (refine (match 
                (app [Eq, Hole])
                (fun _ S (a\   
                   fun _ {{ @eq lp:S lp:{{ Q0 Hole}} lp:{{Q Hole}} }} (_\
                     P a
                )))
        [{{_}}]) G GL 
            )
            (coq.ltac.fail _ "Couldn't unify.").
}}.
Elpi Typecheck.

From Coq Require Import Peano.
Goal (forall x : nat, 1 + x = x + 1) -> 
    forall y,  2 * ((y+y) + 1) = ((y + y)+1) * 2.
Proof.
    intro H. 
    intro x.
    elpi rewrite2 (H).

    (** Goal is [2 * (1 + (x + x)) = (1 + (x + x)) * 2] *)
    Abort.

(** An interesting bug I hit while 
    working through this next one: Elpi usually parses
    the name of a global reference as a global reference.
    But if you have implicit arguments enabled, and automatic
    application turned on, then Coq will automatically
    apply your term to metavariables before feeding it to Elpi,
    and once it's applied, it's a term, not a global reference.
*)

Elpi Tactic rewrite3.
(** Argument either the name of a hypothesis in the context,
    or the name of a global definition (variables count as global references
    as far as Elpi is concerned, although you can get a list of
    the section-local variables by calling coq.env.section.
    
    The declared type of the argument should be type is of the form 
    [forall (x1 : A1) (x2 : A2) ... P = Q]
    
    Unifies Q with a subterm of the goal and rewrites right to left.
*)
Elpi Accumulate lp:{{
    pred nested_forall i:term, i:term, o:goal, o:list sealed-goal.
    nested_forall Eqpf {{@eq lp:S lp:P lp:Q }} (goal _ _ GoalType _ _ as G) GL :- 
        pi x\ (copy J x :- coq.unify-leq Q J ok) =>
            copy GoalType (A x),
            if (occurs x (A x))
            (refine (match
                Eqpf 
                (fun _ S (a\
                   fun _ {{ @eq lp:S lp:P lp:Q }} (_\ A a )
                   ))
                % We only want to create one hole,
                % the one corresponding to the 
                % contents of the (single) branch of the match.
                [{{_}}])
                G GL 
            )
            (coq.ltac.fail _ "Couldn't unify.").

    nested_forall Eqpf (prod _ A B) G GL :-
        Hole = {{ _ }},
        coq.typecheck Hole A ok,
        % This might not make progress if
        % Eqpf is opaque or an assumption.
        whd (app [Eqpf, Hole]) [] HD ARGS,
        unwind HD ARGS Eqpf',
        nested_forall Eqpf' (B Hole) G GL.

    solve (goal Ctx _ _ _ [trm Eq] as G) GL :- (
        % Eq is a direct reference to a global definition or axiom
        Eq = global Gref, coq.env.typeof Gref Ty;
        % Eq is a direct Gallina term and we will infer its type
        % from context
        coq.typecheck Eq Ty ok;
        % Eq is a reference to a declared variable in the context
        std.mem Ctx (decl Eq _ Ty)),
        nested_forall Eq Ty G GL.
}}.
Elpi Typecheck.

Section Example_rewrite3.
Variable A : Type.
Variable B : A -> Type.
Variable C : forall (a : A) (b : B a), Type.
Variable add : forall {a : A} {b : B a}, C a b -> C a b -> C a b.
Variable sym : forall {a : A} {b : B a} (c c' : C a b), add c c' = add c' c.

Goal forall (a : A) (b : B a) (x y : C a b),
    add x y = add y x /\ add x y = add y x.
Proof.
    intros a b x y.
    elpi rewrite3 (@sym).
    (** [add y x = add y x /\ add y x = add y x] *)
    Abort.

End Example_rewrite3.
(** Okay. I still need more practice with 
Elpi but this is a good start. 
We will have to continue and extend the rewrite example, and add other variations.
*)
(** Another good exercise would be to build a database of reflexive or symmetric relations,
that tactics can query to dispatch certain kinds of proofs automatically.*)