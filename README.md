<h1> CoqCheatSheet </h1>

This project is to contain a listing of common facts for working with the Coq language.

**The listing sheet, as PDF, can be found
[here](<https://github.com/alhassy/CoqCheatSheet/blob/master/CheatSheet.pdf>)**,
while below is an unruly html rendition.

This reference sheet is built around the system
<https://github.com/alhassy/CheatSheet>.


# Table of Contents

1.  [Functions & Variables](#org2ad82a9)
2.  [Booleans](#orgc67eca9)
3.  [Strings](#org88dff25)
4.  [Records](#org2f8b274):convert:
5.  [Variants and Pattern Matching](#org66dd23a):convert:
6.  [Tuples and Lists](#org82d005e):convert:
7.  [Options](#org0ab6c28):convert:
8.  [Example Proof](#org1362369):Maybe_prove_classic_demorgan_instead:
9.  [Administrivia, Syntax](#orgdbefe31)
10. [`intros` Tactic: ‘∀, ⇒’ Introduction](#org8826991)
11. [`exact` Tactic](#orgfc95040)
12. [Tactics `refine` & `pose` [local declarations]](#orgea57d77)
13. [Algebraic Datatypes ---`Inductive` and `case`](#orgf64e78c)
14. [Examples of Common Datatypes](#orgb1dfecd)
15. [`True, False, true, false`](#org13c28f6)
16. [`Notation`, `Definition`, and the tactics `fold` and `unfold`](#orgda7698f)
17. [Function Tactic `simpl` &#x2014;“simplify”](#orgbf6b1dd)
18. [Conjunction & Disjunction &#x2014;products & sums&#x2014; and ‘iff’](#org7639a17)
19. [Existence ∃](#org67dfa39)
20. [Searching for Existing Proofs](#orgaceee4f)
21. [Coq Modules](#org699e6cf)
22. [Reads](#orgdc02afb)












OCaml is a strict language;
it is strongly typed where types are inferred.

I may write explicit type annotations below for demonstration
or clarity purposes.

    (* Using explicit type annotations *)
    let x : int = 3;;
    let f (x : int) (y : string) (r : 'a) : float = 3.14;;

Only when interacting with the top-level interpreter,
commands must be terminated by `;;`.
OCaml uses `;` as an expression *separator* &#x2014;not a terminator!

My Emacs setup for OCaml can be found on this [CheatSheet's repo](https://github.com/alhassy/OCamlCheatSheet).


<a id="org2ad82a9"></a>

# Functions & Variables

  A function is declared with the `Definition ⋯ := ⋯.` syntax
&#x2014;variables are functions of zero arguments.
Function & varaible names *must* begin with a lowercase letter, and may use \_ or `'`.

-   They cannot begin with capital letters or numbers, or contain dashes!
-   Functions are like variables, but with arguments, so the same syntax applies.

<div style="column-rule-style:solid;column-count:2;"    (* A curried function *)
    Definition f x y := x + y.

    (* Function application; no computation *)
    Definition result := f 10 (2 * 6).
    Compute result. (* Normalises to 22 *)

    (* Partial application *)
    Definition g x := f x.

Recursive functions use the `Fixpoint` keyword instead.

    Fixpoint fact n := match n with
                       | O   => 1
                       | S n => S n * fact n end.

    Compute fact 5. (* 120 *)
</div>

Here's an example of a higher-order function & multiple local functions
& an anonymous function & the main method is
parametricly polymorphic.

    Definition try_sum {A : Type} (bop : A -> A -> A) (test : A -> bool)
               (default : A) (x : A) (y : A)
    := let wrap a := if test a then a else default
       in bop (wrap x) (wrap y).

    Require Import Nat.
    Compute try_sum Nat.add (fun a => eqb (modulo a 3) 0) 666 1 33. (* 699 *)


<a id="orgc67eca9"></a>

# Booleans

    Require Import Bool.
    Compute (true || false , true && false, if true then 1 else 2).
    (* eqb, implb, and ifb is an alias for if-then-else. *)


<a id="org88dff25"></a>

# Strings

    Require Import String.
    Compute ("string catenation" =? ("string " ++ "catenation"))%string.
    (* The parens are important. *)


<a id="org2f8b274"></a>

# Records     :convert:

Records: Products with named, rather than positional, components.

    type point2d = {x : float; y : float};;

    (* Construction *)
    let p = {y = 2.0; x = 3.4};;

    (* Pattern matching for deconstruction *)
    let {x = px; y = py} = p;;
    let go {x = qx; y = qy} = qx +. qy;;

    (* More tersely, using “field punning”: Variables must coincide with field names. *)
    let erroenous ({xx; y} : point2d )= x +. y;;
    let works {x; y} = 0.0;;

    (* Or we can use dot notation *)
    let go q = q.x +. q.y;;


<a id="org66dd23a"></a>

# Variants and Pattern Matching     :convert:

Variant types: A unified way to combine different types into a single type;
each case is distinuighed by a capitalised tag.

    (* Constructors must start with a capital letter, like in Haskell *)
    type 'a fancy_num =   Nothing | Boring of int | Fancy of 'a
                | Point of point2d | Pair of 'a fancy_num * 'a fancy_num

    let example = Pair (Fancy "twenty", Point {x = 1.2; y = 3.14})

The tags allow us to *extract* components of a variant value
as well as to case against values by inspecting their tags.
This is *pattern matching*.

    (* Destructuring a value *)
    let Pair(head, _) = example;;

    (* Guarded pattern matching, with in-line casing via ‘match’ *)
    let rec sum acc = function
      | Nothing -> 0 + (match acc with true -> 1 | false -> 0)
      | Fancy x when x <= "nine" -> 0
      | (Fancy "twenty") as p -> failwith "Evil!"
      | Pair(l, r) -> sum acc l + sum acc r
      | _ -> 2 (* Default case *)

    let res = sum true example (* Exception: Failure "Evil!" *)

    (* Type aliases can also be formed this way *)
    type myints = int

Note that we can give a pattern a name; above we mentioned `p`,
but did not use it.

-   Repeated & non-exhaustive patterns trigger a warning; e.g., remove the default case above.

-   You can pattern match on arrays too; e.g.,
    `[| x ; y ; z|] -> y`.

The above mechanisms apply to all variants &#x2014;including tuples, lists, and options.


<a id="org82d005e"></a>

# Tuples and Lists     :convert:

Tuples: Parentheses are optional, comma is the main operator.

    let mytuple  : int * string * float = (3, "three", 3.0);;

    (* Pattern matching & projection *)
    let (woah0, woah1, woah2) = mytuple;;
    let add_1and4 (w, x, y, z) = w + z;;
    let that = fst ("that", false)

    (* A singelton list of one tuple !!!!  *)
    let zs = [ 1, "two", true ]

    (* Lists:  type 'a list = [] | (::) of 'a * 'a list  *)
    let xs = [1; 2; 3]
    [1; 2; 3] = 1 :: 2 :: 3 :: [];; (* Syntactic sugar *)

    (* List catenation *)
    [1;2;4;6] = [1;2] @ [4;6];;

    (* Pattern matching example; Only works on lists of length 3 *)
    let go [x; y; z] = x + y + z;;
    14 = go [2;5;7];;

    (* Labelled arguments, using ‘~’, means position is irrelevant *)
    [1; 2; 3] = List.map ["a", "ab", "abc"] ~f:String.length;;
    [1; 2; 3] = List.map  ~f:String.length ["a", "ab", "abc"];;


<a id="org0ab6c28"></a>

# Options     :convert:

Option: Expressing whether a value is present or not.

    (* type 'a option = None | Some of 'a *)

    let divide x y : int option = if y = 0 then None else Some (x / y);;

    let getInt ox = match ox with None -> 0 | Some x -> x;;
    0 = getInt None;;
    2 = getInt (Some 2);;


<a id="org1362369"></a>

# Example Proof     :Maybe_prove_classic_demorgan_instead:

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


<a id="orgdbefe31"></a>

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

-   A defined theorem is essentially a function and so it can be used with arguments,
    in order to prove a result, as if it were a function.

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

-   **Local tactic application:** `t in s` performs the tactic `t` only within
    the hypothesis, term, `s`. For example, `unfold defnName in H` performs a local rewrite
    in hypothesis `H`.
    -   By default, tactics apply to the current subgoal.


<a id="org8826991"></a>

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


<a id="orgfc95040"></a>

# `exact` Tactic

-   If the goal matches a hypothesis `H` *exactly*, then use tactic `exact H`.
-   `Show Proof` desugars `exact H` into `H`, which acts as the result of the
    currently defined function.


<a id="orgea57d77"></a>

# Tactics `refine` & `pose` [local declarations]

If the current goal is \(C\) and you have a proof \(p : A_0 \to \cdots \to A_n \to C\),
then `refine (p _ _ ... _)` introduces \(n\) possibly simpler subgoals corresponding to
the arguments of `p`.

-   This is useful when the arguments may be difficult to prove.
-   If we happen to have a proof of any \(A_i\), then we may use it instead of an ‘\_’.
-   Any one of the underscores could itself be `(q _ ... _)` if we for some proof `q`.

In contrast, you could declare proofs \(p_i\) for each \(A_i\), the arguments of `p`, first
*then* simply invoke `exact (p p0 p1 ... pN)`. To do this, use the `pose` tactic for forming
local declarations: `pose (res := definition_of_p_i)`. The parentheses are important.

-   `Show Proof` desugars `pose` into `let...in...` declarations.


<a id="orgf64e78c"></a>

# Algebraic Datatypes ---`Inductive` and `case`

‘forall’ and type construction allow us to regain many common datatypes, including
∃, ∧, ∨, =, ~, ⊤, ⊥.

The vernacular command `Inductive` lets us create new types.

-   After a type, say, `T` is defined, we are automatically provided with
    an elimination rule `T_rec` and an induction principle `T_ind`.
-   Use `“Check T_rec.”` to view their types.

Tactic `“case x.”` creates subgoals for every possible way that `x` could have been
constructed &#x2014;where ideally `x` occurs in the goal.

-   In particular, for empty type `False`, it creates no new subgoals.
-   If `x` occurs in some hypothesis of interest, then try performing the `case` *before*
    introducing the hypothesis so that the case analysis propagates into it.
-   `case` only changes the goal &#x2014;never the context.
-   Whenever you use this tactic, indent and place `- admit.` for each possible case,
    so that way you don't forget about them and the indentation make it clear which
    tactics are associated with which subgoals.
    -   Tactic `admit` let's us ignore a goal for a while, but the proof is marked incomplete.
-   If `x` is constructed from by `cons a0 ... aN`, then the goal obtains
    these arguments. It's thus very common to have `“case H. intros.”`; in-fact it's so
    common that this combination is packaged up as the `destruct` tactic.

    `case H. intros a0 ... aN.`  ≈  `destruct H as [a0 ... aN]`.

    -   If no `a_i` are provided, the `as` clause may be omitted, and `H`-ypothesis
        names are generated.
    -   If the `case` provides multiple cases, then `destruct` won't work.

If the goal is a value of an ADT, use `refine (name_of_constructor _ ... _)`
then build up the constituents one at a time.

-   For example, to prove `A ∧ B`, use `refine (conj _ _).`


<a id="orgb1dfecd"></a>

# Examples of Common Datatypes

-   `Prop` Type
    -   A `Prop` either has a proof or it does not have a proof.
    -   Coq restricts Prop to being either proven or unproven, rather than true or false.

-   ℕaturals

        Inductive nat : Set :=
          | O : nat   (* Capital-letter O, not the number zero. *)
          | S : nat -> nat.

-   Options

        Inductive option (A : Type) : Type :=
          | Some : A -> option A
          | None : option A.

-   Lists

        Inductive list (A : Type) : Type :=
         | nil : list A
         | cons : A -> list A -> list A.

        Infix "::" := cons (at level 60, right associativity) : list_scope.


<a id="org13c28f6"></a>

# `True, False, true, false`

-   The empty Prop, having no proofs, is `False.`
-   The top Prop, having a single proof named `I`, is `True`.
-   The `bool` type has two values: `true` and `false`.

    Inductive False : Prop := .

    Inductive True : Prop :=
      | I : True.

    (* ‘Set’ is the type of normal datatypes. *)
    Inductive bool : Set :=
      | true : bool
      | false : bool.

    (* From: Require Import Bool *)
    Definition eqb (p q : bool) : bool :=
      match p, q with
        | true, true => true
        | true, false => false
        | false, true => false
        | false, false => true
      end.

In the boolean library there is a function `Is_true` which converts booleans
into their associated Prop counterparts.

    (* “Require Import” is the vernacular to load definitions from a library *)
    Require Import Bool.

**Exercises:**

    Theorem two: not (Is_true(eqb false true)). Abort.
    Theorem same: forall a : bool, Is_true(eqb a a). Abort.
    Theorem ex_falso_quod_libet : (forall A : Prop, False -> A). Abort.
    Theorem use_case_carefully: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)). Abort.


<a id="orgda7698f"></a>

# `Notation`, `Definition`, and the tactics `fold` and `unfold`

`Definition` is a vernacular command that says two expressions are interchangeable.
Below `(not A)` and `A -> False` are declared interchangeable.

    Definition not (A:Prop) := A -> False.

    Notation "~ x" := (not x) : type_scope.

-   A common proof technique is to ‘unfold’ a definition into familiar operators,
    work with that, then ‘fold’ up the result using a definition.

-   Tactics `unfold defnName` and `fold defnName` will interchange them.

-   In Coq, we use the tactic `unfold f` to rewrite the goal using the definition of `f`,
    then use `fold f`, if need be.
-   `Notation` creates an operator and defines it as an alternate notation for an expression.
-   ( Use `intros` when working with negations since they are implications! )

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


<a id="orgbf6b1dd"></a>

# Function Tactic `simpl` &#x2014;“simplify”

-   If the current subgoal contains a function call with all its arguments,
    `simpl` will execute the function on the arguments.
    -   Sometimes a unfold is needed before `simpl` will work.

-   **Modus ponens, or function application:** If we have `imp : A -> B, a : A`
    then `imp a` is of type `B`. This also works if the `imp` contains `forall`'s.


<a id="org7639a17"></a>

# Conjunction & Disjunction &#x2014;products & sums&#x2014; and ‘iff’

    (* Haskell: Either a b = Left a | Right b *)
    Inductive or (A B:Prop) : Prop :=
      | or_introl : A -> A \/ B
      | or_intror : B -> A \/ B
    where "A \/ B" := (or A B) : type_scope.

    (* Haskell: Pair a b = MkPair a b *)
    Inductive and (A B:Prop) : Prop :=
      conj : A -> B -> A /\ B
    where "A /\ B" := (and A B) : type_scope.

    Definition iff (A B:Prop) := (A -> B) /\ (B -> A).
    Notation "A <-> B" := (iff A B) : type_scope.


<a id="org67dfa39"></a>

# Existence ∃

    Inductive ex (A:Type) (P:A -> Prop) : Prop :=
      ex_intro : forall x:A, P x -> ex (A:=A) P.

    Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
      : type_scope.

Note that the constructor takes 3 arguments:
The predicate `P`, the witness `x`, and a proof of `P x`.

If we pose a witness beforehand then `refine (ex_intro _ witness _).`, Coq will infer `P` from
the current goal and the new subgoal is the proof that the witness satisfies the predicate. This is the way to prove an existence claim.


<a id="orgaceee4f"></a>

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


<a id="org699e6cf"></a>

# Coq Modules

Module systems parameterise proofs and tactics over structures.

    Check 0.
    (**

    1. A ~Module Type~ contains the signature of the abstract structure to work from;
       it lists the ~Parameter~'s and ~Axiom~'s we want to use, possibly along
       with notation declaration to make the syntax easier.
    **)
    (**

    |      || Signature     | Structure      |
    | Coq  || ≈ module type | ≈ module       |
    | Agda || ≈ record type | ≈ record value |
    | JavaScript || ≈ prototype | ≈ JSON object |

    It is perhaps seen most easily in the last entry in the table, that
    modules and modules types are essentially the same thing: They are just
    partially defined record types. Again there is a difference in the usage intent:

    | Concept | Intent |
    |---------|--------|
    | Module types | Any name may be opaque, undefined. |
    | Modules | All names must be fully defined. |

    **)

    Module Type Graph.
      Parameter Vertex : Type.
      Parameter Edges : Vertex -> Vertex -> Prop.
      Infix "<=" := Edges : order_scope.
      Open Scope order_scope.
      Axiom loops : forall e, e <= e.
      Parameter decidable : forall x y, {x <= y} + {not (x <= y)}.
      Parameter connected : forall x y, {x <= y} + {y <= x}.
    End Graph.

    (* To form an instance of the graph module type, we define a module *)
    (* that satisfies the module type signature: The ~<:~ declaration requires *)
    (* us to have definitions and theorems with the same names and types *)
    (* as those listed in the module type's signature. *)

    Require Import Bool.

    Module BoolGraph <: Graph.
      Definition Vertex := bool.
      Definition Edges  := fun x => fun y => leb x y.
      Infix "<=" := Edges : order_scope.
      Open Scope order_scope.
      Theorem loops: forall x : Vertex, x <= x.
        Proof.
        intros; unfold Edges, leb; destruct x; tauto.
        Qed.
      Theorem decidable: forall x y, {Edges x y} + {not (Edges x y)}.
        Proof.
          intros; unfold Edges, leb; destruct x, y.
          all: (right; discriminate) || (left; trivial).
      Qed.
      Theorem connected: forall x y, {Edges x y} + {Edges y x}.
        Proof.
          intros; unfold Edges, leb. destruct x, y.
          all: (right; trivial; fail) || left; trivial.
      Qed.
    End BoolGraph.

    (*
    Now we can write a “module functor”: A module that takes some ~Module Type~ parameters. E.g., here is a module that define a minimum function.

    Min is a function-on-modules; the input type is Graph
    and the output module type is “Sig Definition min : ⋯. Parameter case_analysis: ⋯. End”. This is similar to JavaScript's approach.
    *)
    Module Min (G : Graph).
      Import G. (* I.e., open it so we can use names in unquantifed form. *)
      Definition min a b : Vertex := if (decidable a b) then a else b.
      Theorem case_analysis: forall P : Vertex -> Type, forall x y,        (x <= y -> P x) -> (y <= x -> P y) -> P (min x y).
      Proof.
        intros. (* P, x, y, and hypothesises H₀, H₁ now in scope*)
        (* Goal: P (min x y) *)
        unfold min. (* Rewrite “min” according to its definition. *)
        (* Goal: P (if decidable x y then x else y) *)
        destruct (decidable x y). (* Pattern match on the result of “decidable”. *)
        (* Subgoal 1: P x  ---along with new hypothesis H₃ : x ≤ y *)
        tauto. (* i.e., modus ponens using H₁ and H₃ *)
        (* Subgoal 2: P y  ---along with new hypothesis H₃ : ¬ x ≤ y *)
        destruct (connected x y).
        (* Subgoal 2.1: P y ---along with new hypothesis H₄ : x ≤ y *)
        absurd (x <= y); assumption.
        (* Subgoal 2.2: P y ---along with new hypothesis H₄ : y ≤ x *)
        tauto. (* i.e., modus ponens using H₂ and H₄ *)
      Qed.
    End Min.

    (* We may now apply the module functor. *)

    Module Conjunction := Min BoolGraph.
    Export Conjunction.
    Print min.
    (*
    min =
    fun a b : BoolGraph.Vertex => if BoolGraph.decidable a b then a else b
         : BoolGraph.Vertex -> BoolGraph.Vertex -> BoolGraph.Vertex
     *)

    (*
    Unlike the previous functor, which had its return type inferred, we may
    explicitly declare a return type. E.g., the following functor is
    a Graph → Graph function.
    *)
    Module Dual (G : Graph) <: Graph.
      Definition Vertex := G.Vertex.
      Definition Edges  x y : Prop := G.Edges y x.
      Definition loops := G.loops.
      Infix "<=" := Edges : order_scope.
      Open Scope order_scope.
      Theorem decidable: forall x y, {x <= y} + {not (x <= y)}.
        Proof.
          unfold Edges. pose (H := G.decidable). auto.
      Qed.
      Theorem connected: forall x y, {Edges x y} + {Edges y x}.
        Proof.
          unfold Edges.  pose (H := G.connected). auto.
      Qed.
    End Dual.

    (* Example use, with renaming “min ↦ max” *)
    Module Max (G : Graph).
      (* Module applications cannot be chained; intermediate modules must be named. *)
      Module DualG   := Dual G.
      Module Flipped := Min DualG.
      Import G.
      Definition max := Flipped.min.
      Definition max_case_analysis:
            forall P : Vertex -> Type, forall x y,
            (y <= x -> P x) -> (x <= y -> P y) -> P (max x y)
            := Flipped.case_analysis.
    End Max.

    (*
    See the ModuleSystemTutorial in Github coq/coq:
    https://github.com/coq/coq/wiki/ModuleSystemTutorial
    *)


    (* ---------------------------------------------------------------------------- *)

    (* Coq has generative modules: Each application produces a new datatype instance. *)
    Module Type Unit. End Unit. (* Empty signature. *)
    Module TT <: Unit. End TT.  (* Empty structure. *)
    Module F (X : Unit).
      Inductive t : Type := MakeT.
    End F.

    Module A := F TT.
    Module B := F TT.
    Fail Check eq_refl : A.t = B.t.
    Print A.t.

    Module Type Carrier. Parameter t : Type. End Carrier.
    Module Nat <: Carrier. Definition t := nat. End Nat.

    Module Type Morphism (X : Carrier) <: Carrier. Parameter t : Type. End Morphism.
    Module Identity (X : Carrier) <: Morphism X. Definition t := X.t. End Identity.

    Module Alias  (X : Carrier). Module M := X. End Alias.
    Module AtNat  (F : Morphism). Module M := F Nat. End AtNat.

    Module N := Alias Nat.
    Print N.M.t.
    (* N.M.t = Nat.t
         : Type

    Modules η-expand and so aliasing does nothing.
     *)

    Module O := AtNat Identity.
    Print O.M.t.
    (*
    [ O.M.t : Type ] ; i.e., an opaque type

    Type of functors do not η-reduce, and as such one cannot expect them to be applicative, and so are generative ^_^

    See coq/coq OpenIssuesWithModules: https://github.com/coq/coq/wiki/OpenIssuesWithModules
     *)


<a id="orgdc02afb"></a>

# Reads

-   [ ] [A tutorial by Mike Nahas](https://coq.inria.fr/tutorial-nahas) &#x2014;an excellent beginner's tutorial!
-   [ ] [Theorem proving with Coq](http://flint.cs.yale.edu/cs430/sectionNotes/section1/CoqTutorial.pdf) &#x2014;terse Coq overview, 13 pages
-   [ ] [The Coq Proof Assistant, A Tutorial](http://flint.cs.yale.edu/cs430/coq/pdf/Tutorial.pdf) &#x2014;gentle, 53 pages.
-   [ ] [Introduction to the Coq proof-assistant for practical software verification](https://www.lri.fr/~paulin/LASER/course-notes.pdf) &#x2014;compact! 50 pages
-   [ ] [Mathematical Components](https://math-comp.github.io/mcb/book.pdf) &#x2014;formalisation techniques ♥‿♥
-   [ ] [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/html/toc.html)
-   [ ] [Mechanizing Mathematics with Dependent Types](https://ilyasergey.net/pnp/pnp.pdf) &#x2014;ssreflect!
-   [ ] [A Tutorial on (Co-)Inductive Types in Coq](http://www.labri.fr/perso/casteran/RecTutorial.pdf)
-   [ ] [Software Foundations](https://softwarefoundations.cis.upenn.edu/) &#x2014;and ‘vfa’!

[Theory behind Coq](https://github.com/coq/coq/wiki/TheoryBehindCoq)
