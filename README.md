# CoqCheatSheet

This project is to contain a listing of common facts for working with the Coq language.
**The listing sheet, as PDF, can be found [here](https://github.com/alhassy/CoqCheatSheet/blob/master/CheatSheet.pdf)**, while below is an html rendition.


# Table of Contents

1.  [Emacs COMMENT Setup](#orgee45ef7)
2.  [Example Proof](#orge567a35)
3.  [Administrivia, Syntax](#orgb4b6a65)
4.  [`intros` Tactic: ‘∀, ⇒’ Introduction](#org8e3cc59)
5.  [`exact` Tactic](#orgffacadc)
6.  [Tactics `refine` & `pose` [local declarations]](#org052b935)
7.  [Simple Tactics](#orgd9a3a69)
8.  [Todo COMMENT Algebraic Datatypes](#orgff6f444)
9.  [Pattern matching with `destruct`](#org1c70008)
10. [`Notation`, `Definition`, and the tactics `fold` and `unfold`](#orge847a72)
11. [Todo COMMENT Proof Refinement](#orgea2dd24)
12. [Examples of Common Datatypes](#org7b2e9e7)
13. [`True, False, true, false`](#org33f6484)
14. [Existence ∃](#orgd918359)
15. [Equality, `rewrite`, and `reflexivity`](#org805395a)
16. [Discrepancy](#org0eb2dda)
17. [Searching for Existing Proofs](#org514a2c5)
18. [Todo COMMENT More Basic Tactics](#orgb88156a)












<a id="orgee45ef7"></a>

# Emacs COMMENT Setup

[Proof General](https://proofgeneral.github.io/) is a generic Emacs interface for interactive proof assistants &#x2014;predominately [Coq](https://coq.inria.fr/).
We use [company-coq](https://github.com/cpitclaudel/company-coq) code completion &#x2014;that link has many screenshots and gifs ;-)
Execute `M-x company-coq-tutorial` to see what it does; including on the fly documentation for identifiers with source definitions,
prettification of operators, auto-completion of identifiers and module names, jumping to definitions, and proof folding.

    ;; Install Coq from here: https://coq.inria.fr/opam-using.html
    ;; More easily: brew install coq
    ;; Either way ensure: $ coqc --version  ⇒  8.9.1

    ;; Now add it to Emacs' path; obtained by invoking: which coqtop
    (add-to-list 'exec-path "/Users/musa/opam-coq.8.9.1/ocaml-base-compiler.4.02.3/bin/")
    ;; Alternatively: (setq coq-prog-name "PATH/TO/coqtop")

    (use-package proof-general :demand t)

    ;; Let's also obtain code completion.
    (use-package company-coq :demand t)
    ;; Load company-coq when opening Coq files
    (add-hook 'coq-mode-hook #'company-coq-mode)

    ;; When working literately with Coq, I've found this to be nice.
    (setq org-src-window-setup 'split-window-below)
      ;; (setq org-src-window-setup 'reorganize-frame) ;; default

    ;; Ensure goals and proof checking responses have dedicated buffers.
    ;; t ⇒ takes up the entire screen for a total of 3 buffers.
    (setq proof-three-window-enable t)

-   Files ending in the appropriate extension, or invoking the prover's mode, will automatically enable Proof General.
-   Besides the new menu bar, press `C-h m` to obtain more help about Proof General.

    In a Coq script, press `C-c C-RETURN` to have the script up to the current point
    evaluated &#x2014;Proof General will colour that portion blue.

    -   `C-c C-n` to step through a script.
    -   For literate programming with Org-mode, press `C-c '` on a src block first,
	check the proof, then `C-c '` to return to literate fashion.

\room
To prove a theorem in Coq, you state the theorem, provide tactics that reduce it to a number
of sub-goals, then recurse on each sub-goal until there are no more.
Many, if not all subgoals, are simple enough to be discharged with automation.



<a id="orge567a35"></a>

# Example Proof

    (* “for all things you could prove, *)
    (*    if you have a proof of it, then you have a proof of it.” *)
    Theorem my_first_proof : (forall A : Prop, A -> A).
    Proof.
      intros A.
      intros proof_of_A.
      exact proof_of_A.
      (* Press C-c C-Enter after the next command to see what the proof *)
      (* would look like in a declarative fashion; i.e., without tactics in λ-calculus. *)
      Show Proof.
      (* Earlier in the proof, this commands shows a partial λ-term. *)
    Qed.

-   As you can see, **every** Coq command ends with a period.

-   `Prop` is the type of *propositions*: The type of things which could have a proof.

-   Coq uses 3 ‘languages’:

    1.  *Vernacular*: The top-level commands that begin with a capital letter.
    2.  *Tactics*: Lower-case commands that form the proof; ‘proof strategies’.
    3.  *Terms*: The expressions of what we want to prove; e.g., `forall, Prop, ->`.

    This is unsurprising since [a language has many tongues](https://alhassy.github.io/next-700-module-systems-proposal/thesis-proposal.html#org6c659c0).

-   *Proofs and functions are the same thing!*
    -   We can view what we call a proof as function by using `Show Proof`, as above.
    -   We can write functions directly or use [proof] tactics to write functions!


<a id="orgb4b6a65"></a>

# Administrivia, Syntax

-   Every Coq command ends with a period.
-   The phrase *Theorem T identifying statement S is proven by P*
    is formalised as

	Theorem T : S.  (* T is only a name and can be used later. *)
	Proof.
	P  (* See the current state of the proof in the CoqIde by clicking, in the toolbar,
	      on the green arrow pointing at a yellow ball;
	      or do "C-c C-Enter" in Proof General with Emacs. *)
	Qed.

-   Instead of `Theorem`, you may also see proofs that start with
    `Example`, `Lemma`, `Remark`, `Fact`, `Corollary`, and `Proposition`, which all
    mean the same thing. This difference is mostly a matter of style.

-   The command `Admitted`, in-place of `Qed`, can be used as a placeholder for an
    incomplete proof or definition.
    -   Useful if you have a subgoal that you want to ignore for a while.

-   `Abort`, in-place of `Qed`, is used to give up on a proof for the moment,
    say for presentation purposes, and it may be begun later with no error
    about theorems having the same name.

-   **Comments:** `(* I may be a multiline comment. *)`

-   **Stand alone commands:** As top-level items, we may make commands for:
    -   **Normalisation:** `Compute X` executes all the function calls in `X` and prints the result.
    -   **Type inspection:** Command `Check X.` asks Coq to print the type of expression `X`.

-   **Introduce local definitions:** Two ways,
    -   Simple alias: `pose (new_thing := complicated_expression).`
    -   More involved: Write tactic `assert (x : X).` to define a new identifier
	`x` for a proof of `X` which then follows, and is conventionally indented.

-   **Imports:** Loading definitions from a library,

	Require Import Bool.

\iffalse

-   **Pattern matching with `case`:** If we do a `case` on an item of type `A \/ B` then we obtain two new subgoals:
      `A → …` and `B → …`, which may be begun with `intros` as usual.
    -   `case` alters subgoals and never the context already `intro`-duced.

The "case" tactic only changes the subgoal.
Hence whether it is invoked before all possible intros or not gives different
proof power. For example, try proving:

    Theorem thm_eqb_a_t: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).

\fi


<a id="org8e3cc59"></a>

# `intros` Tactic: ‘∀, ⇒’ Introduction

-   To prove *∀ x, Px*: “Let *x* be arbitrary, now we aim to prove *Px*.”
-   This strategy is achieved by the `intros x` tactic.
-   To prove `∀ x0 x1 ... xN, Pxs` use `intros x0 x1 ... xN` to obtain the subgoal `Pxs`.
    -   Using just `“intros.”` is the same as `intros H H0 H1 ... HN-1.` &#x2014;‘H’ for hypothesis.
    -   Prop names are introduced with the name declared;
	e.g., `“intros.”` for `“∀ A : Prop, Px”`
	uses the name `A` automatically.
-   Note: `(A → B) = (∀ a:A, B)` and so `intros` works for ‘→’ as well.
-   `Show Proof` will desugar `intros` into argument declarations of a function.


<a id="orgffacadc"></a>

# `exact` Tactic

-   If the goal matches a hypothesis `H` *exactly*, then use tactic `exact H`.
-   `Show Proof` desugars `exact H` into `H`, which acts as the result of the
    currently defined function.


<a id="org052b935"></a>

# Tactics `refine` & `pose` [local declarations]

If the current goal is \(C\) and you have a proof \(p : A_0 \to \cdots \to A_n \to C\),
then `refine (p _ _ ... _)` introduces \(n\) possibly simpler subgoals corresponding to
the arguments of `p`.

-   This is useful when the arguments may be difficult to prove.
-   If we happen to have a proof of any \(A_i\), then we may use it instead of an ‘\_’.
-   Any one of the underscores could itself be `(q _ ... _)` if we for some proof `q`.

**Exercise:**
Prove the ‘modus ponens’ proposition in three ways.

    Theorem refine_with_one_subgoal : forall A B : Prop, A -> (A -> B) -> B. Abort.

    Theorem using_only_exact : forall A B : Prop, A -> (A -> B) -> B. Abort.

    Theorem refine_with_no_subgoals : forall A B : Prop, A -> (A -> B) -> B. Abort.

Likewise, prove \(∀ A B C,  A → (A → B) → (B → C) → C\) in three such ways.

In contrast, you could declare proofs \(p_i\) for each \(A_i\), the arguments of `p`, first
*then* simply invoke `exact (p p0 p1 ... pN)`. To do this, use the `pose` tactic for forming
local declarations: `pose (res := definition_of_p_i)`. The parentheses are important.

-   `Show Proof` desugars `pose` into `let...in...` declarations.

**Exercise:**
Reprove the above without using `refine`, by using `pose` instead.


<a id="orgd9a3a69"></a>

# Simple Tactics

-   **`simpl`:** If the current subgoal contains a function call with all its arguments, `simpl` will execute the function on the arguments.
    -   Sometimes a call to `unfold f`, for a particular function `f`, is needed before `simpl` will work.

-   **Modus ponens, or function application:** If we have `imp : A -> B, a : A`
    then `imp a` is of type `B`. This also works if the `imp` contains `forall`'s.

-   **Local tactic application:** `t in s` performs the tactic `t` only within
    the hypothesis, term, `s`. For example, `unfold defnName in item` performs a local rewrite.


<a id="orgff6f444"></a>

# Todo COMMENT Algebraic Datatypes

The vernacular command `Inductive` lets us create new types.

-   After a type, say, `T` is defined, we are automatically provided with
    `T_rect` and `T_ind`.


<a id="org1c70008"></a>

# Pattern matching with `destruct`

We case on value `e` by `destruct e as [ a00 … am0 | ⋯ | a0n … amn ]`,
which gives us `n` new subgoals corresponding to the number of constructors that
could have produced `e` such that the *i*-th constructor has arguments `ai0, …, akᵢ`.

-   The intros pattern `as [ ⋯ ]` lets us use any friendly names of our choosing.
    We may not provide it at the cost of Coq's generated names for arguments.

-   Many proofs pattern match on a variable right after introducing it,
    `intros e. destruct e as [⋯]`, and this is abbreviated by the intro pattern:
    `intros [⋯]`.

-   If there are no arguments to name, in the case of a nullary construction, we can just write `[]`.


<a id="orge847a72"></a>

# `Notation`, `Definition`, and the tactics `fold` and `unfold`

`Definition` is a vernacular command that says two expressions are interchangeable.
Below `(not A)` and `A -> False` are declared interchangeable.

    Definition not (A:Prop) := A -> False.

    Notation "~ x" := (not x) : type_scope.

Tactics `unfold defnName` and `fold defnName` will interchange them.

`Notation` creates an operator and defines it as an alternate notation for an expression.

( Use `intros` when working with negations since they are implications! )

    (* If this is a recursive function, use `Fixpoint` in-place of `Definition`.*)
    Definition my_function (a0 : A0) ⋯ (a99 : A99) : B :=
      match a0 , …,  a99 with
      | C₀ p₀ … p_n, …, C_k q₀ ⋯ q_m =>  definition_here_for_these_constructors_Cᵢ
      ⋮
      end.

-   **Telescoping:** If `x₀, ⋯, x_n` have the same type, say `T`,
    we may declare their typing by `(x₀ ⋯ x_n : T)`.
-   **Notation:** Before the final ".", we may include a variant of
    `where "n + m" := (my_function n m) : B_scope.` for introducing
    an operator immediately with a function definition.


<a id="orgea2dd24"></a>

# Todo COMMENT Proof Refinement

Suppose our goal is to prove B but we have a proof `imp : A → B`,
then if we have an `A` function application suffices. However,
when we have no `A` lying about and would like to focus on constructing
such an `A` we use `refine (imp _)` which forces us into constructing
a subgoal `A`. It is good practice to then indent proof for the new subgoal.

-   If `imp` has more arguments then `refine` would take more underscores corresponding
    to the arguments we do not have proofs of; we may place the arguments which we
    do have access to there and then.

-   Needless to say, a `refine` may occur within a `refine`.

\iffalse

    Theorem nexted_refine_example : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
    Proof.
      intros A B C.
      intros Apf AtoB AthenBthenC.
      refine (AthenBthenC _ _).
	exact Apf.
	refine (AtoB _).
	  exact Apf.
    Qed.

    Theorem direct_proof : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
    Proof.
      intros A B C Apf AB ABC.
      exact (ABC Apf (AB Apf)).
    Qed.

\fi

\newpage


<a id="org7b2e9e7"></a>

# Examples of Common Datatypes

-   `Prop` Type
    -   A `Prop` either has a proof or it does not have a proof.
    -   Coq restricts Prop to being either proven or unproven, rather than true or false.

-   Sums

	Inductive or (A B:Prop) : Prop :=
	  | or_introl : A -> A \/ B
	  | or_intror : B -> A \/ B
	where "A \/ B" := (or A B) : type_scope.

-   Products

	Inductive and (A B:Prop) : Prop :=
	  conj : A -> B -> A /\ B
	where "A /\ B" := (and A B) : type_scope.

-   ℕaturals

	Inductive nat : Set :=
	  | O : nat   (* Capital-letter O, not the number zero. *)
	  | S : nat -> nat.

-   Options

	Inductive option (A : Type) : Type :=
	  | Some : A -> option A
	  | None : option .A

-   Lists

	Inductive list (A : Type) : Type :=
	 | nil : list A
	 | cons : A -> list A -> list A.

	Infix "::" := cons (at level 60, right associativity) : list_scope.


<a id="org33f6484"></a>

# `True, False, true, false`

The vernacular command `Inductive` lets you create a new type.

-   The empty Prop, having no proofs, is `False.`
-   The top Prop, having a single proof named `I`, is `True`.
-   The `bool` type has two values: `true` and `false`.

    Inductive False : Prop := .

    Inductive True : Prop :=
      | I : True.

    Inductive bool : Set :=
      | true : bool
      | false : bool.

\iffalse principle of explosion

    Theorem ex_falso_quod_libet : (forall A : Prop, False -> A).
    Proof.
      intros A []
    Qed.

\fi

In the boolean library there is a function `Is_true` which converts booleans
into their associated Prop counterparts.


<a id="orgd918359"></a>

# Existence ∃

    Inductive ex (A:Type) (P:A -> Prop) : Prop :=
      ex_intro : forall x:A, P x -> ex (A:=A) P.

    Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
      : type_scope.

Note that the constructor takes 3 arguments: The predicate `P`, the witness `x`, and a proof of `P x`.

If we pose a witness beforehand then `refine (ex_intro _ witness _).`, Coq will infer `P` from
the current goal and the new subgoal is the proof that the witness satisfies the predicate.

\iffalse
Note that De Morgan's law, ¬∀≈∃¬, holds! Prove an implication to see this.

    Theorem demorgan : (forall P : Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
    Proof.
      intros P.
      intros noP.
      unfold not.
      intros ex.
      destruct ex as [ witness  proof ].
      pose (uhoh := noP witness).
      pose (absurd := uhoh proof).
      case absurd.
    Qed.

The converse is also true!
\fi


<a id="org805395a"></a>

# Equality, `rewrite`, and `reflexivity`

Two operators,

-   `x = y :> A` says that `x` and `y` are equal and both have type `A`.
-   `x = y` does the same but let's Coq infer the type `A`.

    Inductive eq (A:Type) (x:A) : A -> Prop :=
	eq_refl : x = x :>A

    where "x = y :> A" := (@eq A x y) : type_scope.

    Notation "x = y" := (x = y :>_) : type_scope.

\iffalse

The "Inductive" statement creates a new type "eq" which is a function of a type A and 2 values of type A to Prop. (NOTE: One value of type A is written (x:A) before the ":" and the other is written "A ->" after. This is done so Coq infers the type "A" from the first value and not the second.) Calling "eq" with all its arguments returns a proposition (with type Prop). A proof of "eq x y" means that "x" and "y" both have the same type and that "x" equals "y".

The only way to create a proof of type "eq" is to use the only constructor "eq<sub>refl</sub>". It takes a value of "x" of type "A" and returns "@eq A x x", that is, that "x" is equal to itself. (The "@" prevents Coq from inferring values, like the type "A".) The name "eq<sub>refl</sub>" comes from the reflexive property of equality.

\fi

Rather than using `destruct`, most proofs using equality use the tactics `rewrite ⟨orientation⟩.`
If `xEy` has type `x = y`, then `rewrite -> xEy` will replace `x` with `y` in the subgoal, while using orientation `<-` rewrites the
other-way, replacing `y` with `x`.

-   This can also be used with a previously proved theorem.
    If the statement of said theorem involves quantified variables,
    Coq tries to instantiate them by matching with the current goal.

-   As with destructing, the pattern `intros eq. rewrite -> eq.`
    is abbreviated by the intro pattern `intros [].` which performs
    a left-to-right rewrite in the goal.

Use the `reflexivity` tactic to discharge a goal of type `x = x`.

-   This tactic performs some simplification automatically
    when checking that two sides are equal; e.g., it tries `simpl` and `unfold`.

    \iffalse
    Moreover, it will be useful later to know that [reflexivity]
    does somewhat <span class="underline">more</span> simplification than [simpl] does &#x2013; for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.
    \fi


<a id="org0eb2dda"></a>

# Discrepancy

Coq uses the operator `<>` for inequality, which really means *equality is unprovable* or *equality implies False*.

    Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
    Notation "x <> y" := (x <> y :>_) : type_scope.

Datatype constructors are necessarily disjoint, hence if we ever obtain a proof `pf`
of distinct constructors being equal then we may invoke `discriminate pf` to short-circuit the
current goal, thereby eliminating a case that could not have happened.

\iffalse
`discriminate` operates on a hypothesis where values of inductive type are compared using equality. If the constructors used to generate the equality type are different, like here where we have `true = false`, then Coq knows that situation can never happen. It's like a proof of `False`. In that case, `discriminate <hypname>.` ends the subgoal.

    Theorem example  : forall A, true = false -> A.
    Proof.
      intros A tEf.
      discriminate tEf.
    Qed.

When working with inductive types, you will use "discriminate" to eliminate a lot of cases that can never happen.

RULE: If you have a hypothesis "<name> : (<constructor1> &#x2026;) = (<constructor2> &#x2026;) OR "<name> : <constant1> = <constant2> Then use the tactic "discriminate <name>"
\fi


<a id="org514a2c5"></a>

# Searching for Existing Proofs

-   Searching for utility functions, proofs, that involve a particular identifier by using `Search`.
-   In contrast, `SearchPattern` takes a pattern with holes ‘\_’ for expressions.
-   Finally, `SearchRewrite` only looks for proofs whose conclusion in an equality involving the given pattern.

    Search le.
    (* le_n: forall n : nat, n <= n *)
    (* le_0_n: forall n : nat, 0 <= n *)
    (* min_l: forall n m : nat, n <= m -> Nat.min n m = n *)
    (* and many more *)

    (* Let's load some terribly useful arithmetic proofs. *)
    Require Import Arith Omega.

    SearchPattern (_+_ <= _+_).
    (* plus_le_compat_r: forall n m p : nat, n <= m -> n + p <= m + p *)
    (* Nat.add_le_mono: forall n m p q : nat, n <= m -> p <= q -> n + p <= m + q *)
    (* etc. *)

    SearchRewrite (_ + (_ - _)).
    (* le_plus_minus: forall n m : nat, n <= m -> m = n + (m - n) *)
    (* le_plus_minus_r: forall n m : nat, n <= m -> n + (m - n) = m *)
    (* Nat.add_sub_assoc: forall n m p : nat, p <= m -> n + (m - p) = n + m - p *)


<a id="orgb88156a"></a>

# Todo COMMENT More Basic Tactics

-   If we have access to some `H : ∀ 𝓍, A₁ → … Aₙ → G` where `G`,
    up to substitution, is exactly
    the current goal, then `apply f` introduces `n` many new subgoals
    that need to then be tackled and variables `𝓍` are inferred.
    ( "Modus Ponens"! )
    -   When a variable cannot be inferred we must give it explicitly: `apply H with (xᵢ := ⋯).`
    -   `apply` will perform simplification first, if needed.

-   `symmetry` switches the left and right sides of an equality in
    the goal.

-   The constructors of inductively defined types are injective and disjoint.
    These principles are invoked by the tactic `inversion H`, where `H` denotes an
    equality involving constructors as main application.
    For same constructors this acts as injectivity, generating all equations
    resulting from `H` and rewriting the goal along them.
    For distinct constructors, it produces no goals: What you have is impossible,
    ergo a contradiction whence anything follows.
    -   We can name the equations that `inversion` generates with an
	`as ...`.

-   This is useful theorem, not a tactic:
    `f_equal : ∀ (A B : Type) (f: A -> B) (x y: A), x = y -> f x = f y`

-   Using Tactics on Hypotheses:
    By default, most tactics work on the goal and leave the context unchanged.
    However, most tactics also have a variant that performs a similar operation
    on a statement in the context: `t in H` performs tactic `t` only on `H` thereby
    altering only `H`.

**With induction, don't introduce things unless you have to!**
What we can do instead is to first introduce all the quantified
    variables and then <span class="underline">re-generalize</span> one or more of them,
    selectively taking variables out of the context and putting them
    back at the beginning of the goal.  The [generalize dependent m]
    tactic does this.
