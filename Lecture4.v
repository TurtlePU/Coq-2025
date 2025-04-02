(** * Programming with Propositions *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Lectures Require Export Lecture3.

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if it is equal to [x'] or if it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition (!): *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also reason about more generic statements involving [In]. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** (Note here how [In] starts out applied to a variable and only
    gets expanded when we do case analysis on this variable.) *)

(** This way of defining propositions recursively is very convenient in
    some cases, less so in others.  In particular, it is subject to Coq's
    usual restrictions regarding the definition of recursive functions,
    e.g., the requirement that they be "obviously terminating."

    In the next chapter, we will see how to define propositions
    _inductively_ -- a different technique with its own strengths and
    limitations. *)

(** **** Exercise: 2 stars, standard (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (All)

    We noted above that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] says that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (combine_odd_even)

    Complete the definition of [combine_odd_even] below.  It takes as
    arguments two properties of numbers, [Podd] and [Peven], and it should
    return a property [P] such that [P n] is equivalent to [Podd n] when
    [n] is [odd] and equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** One feature that distinguishes Coq from some other popular proof
    assistants (e.g., ACL2 and Isabelle) is that it treats _proofs_ as
    first-class objects.

    There is a great deal to be said about this, but it is not necessary to
    understand it all in order to use Coq.  This section gives just a
    taste, leaving a deeper exploration for the optional chapters
    [ProofObjects] and [IndPrinciples]. *)

(** We have seen that we can use [Check] to ask Coq to check whether
    an expression has a given type: *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

(** We can also use it to check the theorem a particular identifier
    refers to: *)

Check add_comm        : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

(** Coq checks the _statements_ of the [add_comm] and
    [plus_id_example] theorems in the same way that it checks the
    _type_ of any term (e.g., plus). If we leave off the colon and
    type, Coq will print these types for us.

    Why? *)

(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_ -- a logical derivation establishing the truth of the
    statement [forall n m : nat, n + m = m + n].  The type of this object
    is the proposition that it is a proof of.

    The type of an ordinary function tells us what we can do with it.
       - If we have a term of type [nat -> nat -> nat], we can give it two
         [nat]s as arguments and get a [nat] back.

    Similarly, the statement of a theorem tells us what we can use that
    theorem for.
       - If we have a term of type [forall n m, n = m -> n + n = m + m] and we
         provide it two numbers [n] and [m] and a third "argument" of type
         [n = m], we can derive [n + n = m + m]. *)

(** Operationally, this analogy goes even further: by applying a
    theorem as if it were a function, i.e., applying it to values and
    hypotheses with matching types, we can specialize its result
    without having to resort to intermediate assertions.  For example,
    suppose we wanted to prove the following result: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this by
    rewriting with [add_comm] twice to make the two sides match.  The
    problem is that the second [rewrite] will undo the effect of the
    first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(** We encountered similar issues back in [Induction], and we saw
    one way to work around them by using [assert] to derive a specialized
    version of [add_comm] that can be used to rewrite exactly where we
    want. *)

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [add_comm] directly
    to the arguments we want to instantiate it with, in much the same
    way as we apply a polymorphic function to a type argument. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** If we really wanted, we could in fact do it for both rewrites. *)

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Here's another example of using a trivial theorem about lists like
    a function.

    The theorem says: if a list [l] contains some
    element [x], then [l] must be nonempty. *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** What makes this interesting is that one quantified variable
    ([x]) does not appear in the conclusion ([l <> []]). *)

(** Intuitively, we should be able to use this theorem to prove the special
    case where [x] is [42]. However, simply invoking the tactic [apply
    in_not_nil] will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis (causing the values of the
    other parameters to be inferred). *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(** You can "use a theorem as a function" in this way with almost any
    tactic that can take a theorem's name as an argument.

    Note, also, that theorem application uses the same inference
    mechanisms as function application; thus, it is possible, for
    example, to supply wildcards as arguments to be inferred, or to
    declare some hypotheses to a theorem as implicit by default.
    These features are illustrated in the proof below. (The details of
    how this proof works are not critical -- the goal here is just to
    illustrate applying theorems to arguments.) *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)

(* ################################################################# *)
(** * Working with Decidable Properties *)

(** We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           works with rewrite tactic?      no        yes
*)

(** The crucial difference between the two worlds is _decidability_.
    Every (closed) Coq expression of type [bool] can be simplified in a
    finite number of steps to either [true] or [false] -- i.e., there is a
    terminating mechanical procedure for deciding whether or not it is
    [true].

    This means that, for example, the type [nat -> bool] is inhabited only
    by functions that, given a [nat], always yield either [true] or [false]
    in finite time; and this, in turn, means (by a standard computability
    argument) that there is _no_ function in [nat -> bool] that checks
    whether a given number is the code of a terminating Turing machine.

    By contrast, the type [Prop] includes both decidable and undecidable
    mathematical propositions; in particular, the type [nat -> Prop] does
    contain functions representing properties like "the nth Turing machine
    halts."

    The second row in the table follows directly from this essential
    difference.  To evaluate a pattern match (or conditional) on a boolean,
    we need to know whether the scrutinee evaluates to [true] or [false];
    this only works for [bool], not [Prop].

    The third row highlights another important practical difference:
    equality functions like [eqb_nat] that return a boolean cannot be used
    directly to justify rewriting with the [rewrite] tactic; propositional
    equality is required for this. *)


(** Since [Prop] includes _both_ decidable and undecidable properties, we
    have two options when we want to formalize a property that happens to
    be decidable: we can express it either as a boolean computation or as a
    function into [Prop]. *)

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

(** Of course, it would be pretty strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!  Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars, standard (even_double_conv) *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now the main theorem: *)
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(** In view of this theorem, we can say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent: *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** Even when the boolean and propositional formulations of a claim are
    interchangeable from a purely logical perspective, it can be more
    convenient to use one over the other. *)

(** For example, there is no effective way to _test_ whether or not a
    [Prop] is true in a function definition; thus the
    following definition is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects an
    element of [bool] (or some other inductive type with two constructors).
    This has to do with the _computational_ nature of Coq's core language,
    which is designed so that every function it can express is computable
    and total.  One reason for this is to allow the extraction of
    executable programs from Coq developments.  As a consequence, [Prop] in
    Coq does _not_ have a universal case analysis operation telling whether
    any given proposition is true or false, since such an operation would
    allow us to write non-computable functions.  *)

(** Rather, we have to state this definition using a boolean equality
    test. *)

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

(** Beyond the fact that non-computable properties are impossible in
    general to phrase as boolean computations, even many _computable_
    properties are easier to express using [Prop] than [bool], since
    recursive function definitions in Coq are subject to significant
    restrictions.  For instance, the next chapter shows how to define the
    property that a regular expression matches a given string using [Prop].
    Doing the same with [bool] would amount to writing a regular expression
    matching algorithm, which would be more complicated, harder to
    understand, and harder to reason about than a simple (non-algorithmic)
    definition of this property.

    Conversely, an important side benefit of stating facts using booleans
    is enabling some proof automation through computation with Coq terms, a
    technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is simpler, because we
    don't have to invent the witness [500]: Coq's computation mechanism
    does it for us! *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** Now, the useful observation is that, since the two notions are
    equivalent, we can use the boolean formulation to prove the other one
    without mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    line count in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Coq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** Another advantage of booleans is that the negation of a "boolean fact"
    is straightforward to state and prove: simply flip the expected boolean
    result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

(** In contrast, propositional negation can be difficult to work with
    directly.

    For example, suppose we state the non-evenness of [1001]
    propositionally: *)

Example not_even_1001' : ~(Even 1001).

(** Proving this directly -- by assuming that there is some [n] such that
    [1001 = double n] and then somehow reasoning to a contradiction --
    would be rather complicated.

    But if we convert it to a claim about the boolean [even] function, we
    can let Coq do the work for us. *)

Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** Conversely, there are complementary situations where it can be easier
    to work with propositions rather than booleans.

    In particular, knowing that [(n =? m) = true] is generally of little
    direct help in the middle of a proof involving [n] and [m], but if we
    convert the statement to the equivalent form [n = m], we can rewrite
    with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** We won't discuss reflection any further for the moment, but
    it serves as a good example showing the different strengths of
    booleans and general propositions.

    Being able to cross back and forth between the boolean and
    propositional worlds will often be convenient in later chapters. *)

(** **** Exercise: 2 stars, standard (logical_connectives)

    The following theorems relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (eqb_neq)

    The following theorem is an alternate "negative" formulation of
    [eqb_eq] that is more convenient in certain situations.  (We'll see
    examples in later chapters.)  Hint: [not_true_iff_false]. *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (eqb_list)

    Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (All_forallb)

    Prove the theorem below, which relates [forallb], from the
    exercise [forall_exists_challenge] in chapter [Tactics], to
    the [All] property defined above. *)

(** Copy the definition of [forallb] from your [Tactics] here
    so that this file can be graded on its own. *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

(** (Ungraded thought question) Are there any important properties of
    the function [forallb] which are not captured by this
    specification? *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * The Logic of Coq *)

(** Coq's logical core, the _Calculus of Inductive
    Constructions_, differs in some important ways from other formal
    systems that are used by mathematicians to write down precise and
    rigorous definitions and proofs -- in particular from
    Zermelo-Fraenkel Set Theory (ZFC), the most popular foundation for
    paper-and-pencil mathematics.

    We conclude this chapter with a brief discussion of some of the
    most significant differences between these two worlds. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** Coq's logic is quite minimalistic.  This means that one occasionally
    encounters cases where translating standard mathematical reasoning into
    Coq is cumbersome -- or even impossible -- unless we enrich its core
    logic with additional axioms. *)

(** For example, the equality assertions that we have seen so far
    mostly have concerned elements of inductive types ([nat], [bool],
    etc.).  But, since Coq's equality operator is polymorphic, we can use
    it at _any_ type -- in particular, we can write propositions claiming
    that two _functions_ are equal to each other:

    In certain cases Coq can successfully prove equality propositions stating
    that two _functions_ are equal to each other: **)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** This works when Coq can simplify the functions to the same expression,
    but this doesn't always happen. **)

(** These two functions are equal just by simplification, but in general
    functions can be equal for more interesting reasons.

    In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** (Informally, an "extensional property" is one that pertains to an
    object's observable behavior.  Thus, functional extensionality
    simply means that a function's identity is completely determined
    by what we can observe from it -- i.e., the results we obtain
    after applying it.) *)

(** However, functional extensionality is not part of Coq's built-in logic.
    This means that some intuitively obvious propositions are not
    provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

(** However, if we like, we can add functional extensionality to Coq
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** Naturally, we need to be quite careful when adding new axioms into
    Coq's logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False], [2+2=5],
    etc.!

    In general, there is no simple way of telling whether an axiom is safe
    to add: hard work by highly trained mathematicians is often required to
    establish the consistency of any particular combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:

      Print Assumptions function_equality_ex2
*)
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g

    (If you try this yourself, you may also see [add_comm] listed as
    an assumption, depending on whether the copy of [Tactics.v] in the
    local directory has the proof of [add_comm] filled in.) *)

(** **** Exercise: 4 stars, standard (tr_rev_correct)

    One problem with the definition of the list-reversing function [rev]
    that we have is that it performs a call to [app] on each step.  Running
    [app] takes time asymptotically linear in the size of the list, which
    means that [rev] is asymptotically quadratic.

    We can improve this with the following two-argument definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version of [rev] is said to be _tail-recursive_, because the
    recursive call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.

    Prove that the two definitions are indeed equivalent. *)

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies in _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** In the special case where we happen to know that [P] is reflected in
    some boolean term [b], knowing whether it holds or not is trivial: we
    just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** Sadly, this trick only works for decidable propositions. *)

(** It may seem strange that the general excluded middle is not
    available by default in Coq, since it is a standard feature of familiar
    logics like ZFC.  But there is a distinct advantage in _not_ assuming
    the excluded middle: statements in Coq make stronger claims than the
    analogous statements in standard mathematics.  Notably, a Coq proof of
    [exists x, P x] always includes a particular value of [x] for which we
    can prove [P x] -- in other words, every proof of existence is
    _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle may
    lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] ([a] to the power [b]) is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.  If
    [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b = sqrt 2] and
    we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is irrational.  In this
    case, we can take [a = sqrt 2 ^ sqrt 2] and [b = sqrt 2], since [a ^ b
    = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2].  []

    Do you see what happened here?  We used the excluded middle to consider
    separately the cases where [sqrt 2 ^ sqrt 2] is rational and where it
    is not, without knowing which one actually holds!  Because of this, we
    finish the proof knowing that such [a] and [b] exist, but not knowing
    their actual values.

    As useful as constructive logic is, it does have its limitations: There
    are many statements that can easily be proven in classical logic but
    that have only much more complicated constructive proofs, and there are
    some that are known to have no constructive proof at all!  Fortunately,
    like functional extensionality, the excluded middle is known to be
    compatible with Coq's logic, allowing us to add it safely as an axiom.
    However, we will not need to do so here: the results that we cover can
    be developed entirely within constructive logic at negligible extra
    cost.

    It takes some practice to understand which proof techniques must be
    avoided in constructive reasoning, but arguments by contradiction, in
    particular, are infamous for leading to non-constructive proofs.
    Here's a typical example: suppose that we want to show that there
    exists [x] with some property [P], i.e., such that [P x].  We start by
    assuming that our conclusion is false; that is, [~ exists x, P x]. From
    this premise, it is not hard to derive [forall x, ~ P x].  If we manage
    to show that this intermediate fact results in a contradiction, we
    arrive at an existence proof without ever exhibiting a value of [x] for
    which [P x] holds!

    The technical flaw here, from a constructive standpoint, is that we
    claimed to prove [exists x, P x] using a proof of [~ ~ (exists x, P x)].
    Allowing ourselves to remove double negations from arbitrary
    statements is equivalent to assuming the excluded middle law, as shown
    in one of the exercises below.  Thus, this line of reasoning cannot be
    encoded in Coq without assuming additional axioms. *)

(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable)

    Proving the consistency of Coq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Coq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    the negation of such an axiom leads to a contradiction.  If [~ (P
    \/ ~P)] were provable, then by [de_morgan_not_or] as proved above,
    [P /\ ~P] would be provable, which would be a contradiction. So, it
    is safe to add [P \/ ~P] as an axiom for any particular [P].

    Succinctly: for any proposition P,
        [Coq is consistent ==> (Coq + P \/ ~P) is consistent]. *)

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)

    It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (classical_axioms)

    For those who like a challenge, here is an exercise adapted from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following five statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all six propositions (these five plus [excluded_middle])
    are equivalent.

    Hint: Rather than considering all pairs of statements pairwise,
    prove a single circular chain of implications that connects them
    all. *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * IndProp: Inductively Defined Propositions *)

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.

    In this chapter, we bring yet another new tool into the mix:
    _inductively defined propositions_.

    To begin, some examples... *)

(* ================================================================= *)
(** ** Example: The Collatz Conjecture *)

(** The _Collatz Conjecture_ is a famous open problem in number
    theory.

    Its statement is quite simple.  First, we define a function [csf]
    on numbers, as follows (where [csf] stands for "Collatz step function"): *)

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(** Next, we look at what happens when we repeatedly apply [csf] to
    some given starting number.  For example, [csf 12] is [6], and
    [csf 6] is [3], so by repeatedly applying [csf] we get the
    sequence [12, 6, 3, 10, 5, 16, 8, 4, 2, 1].

    Similarly, if we start with [19], we get the longer sequence [19,
    58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
    4, 2, 1].

    Both of these sequences eventually reach [1].  The question posed
    by Collatz was: Is the sequence starting from _any_ positive
    natural number guaranteed to reach [1] eventually? *)

(** To formalize this question in Coq, we might try to define a
    recursive _function_ that calculates the total number of steps
    that it takes for such a sequence to reach [1]. *)

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

(** You can write this definition in a standard programming language.
    This definition is, however, rejected by Coq's termination
    checker, since the argument to the recursive call, [csf n], is not
    "obviously smaller" than [n].

    Indeed, this isn't just a pointless limitation: functions in Coq
    are required to be total, to ensure logical consistency.

    Moreover, we can't fix it by devising a more clever termination
    checker: deciding whether this particular function is total
    would be equivalent to settling the Collatz conjecture! *)

(** Another idea could be to express the concept of "eventually
    reaches [1] in the Collatz sequence" as an _recursively defined
    property_ of numbers [Collatz_holds_for : nat -> Prop]. *)

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

(** This recursive function is also rejected by the termination
    checker, since while we can in principle convince Coq that
    [div2 n] is smaller than [n], we can't convince it that
    [(3 * n) + 1] is smaller than [n]. Since it's definitely not! *)

(** Fortunately, there is another way to do it: We can express the
    concept "reaches [1] eventually in the Collatz sequence" as an
    _inductively defined property_ of numbers. Intuitively, this
    property is defined by a set of rules:

                  ------------------- (Chf_one)
                  Collatz_holds_for 1

     even n = true      Collatz_holds_for (div2 n)
     --------------------------------------------- (Chf_even)
                     Collatz_holds_for n

     even n = false    Collatz_holds_for ((3 * n) + 1)
     ------------------------------------------------- (Chf_odd)
                    Collatz_holds_for n

    So there are three ways to prove that a number [n] eventually
    reaches 1 in the Collatz sequence:
        - [n] is 1;
        - [n] is even and [div2 n] reaches 1;
        - [n] is odd and [(3 * n) + 1] reaches 1.
*)
(** We can prove that a number reaches 1 by constructing a (finite)
    derivation using these rules. For instance, here is the derivation
    proving that 12 reaches 1 (where we left out the evenness/oddness
    premises):

                    ———————————————————— (Chf_one)
                    Collatz_holds_for 1
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 2
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 4
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 8
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 16
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 5
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 10
                    ———————————————————— (Chf_odd)
                    Collatz_holds_for 3
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 6
                    ———————————————————— (Chf_even)
                    Collatz_holds_for 12
*)

(** Formally in Coq, the [Collatz_holds_for] property is
    _inductively defined_: *)

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) :  even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

(** What we've done here is to use Coq's [Inductive] definition
    mechanism to characterize the property "Collatz holds for..." by
    stating three different ways in which it can hold: (1) Collatz
    holds for [1], (2) if Collatz holds for [div2 n] and [n] is even
    then Collatz holds for [n], and (3) if Collatz holds for [(3 * n)
    + 1] and [n] is even then Collatz holds for [n]. This Coq definition
    directly corresponds to the three rules we wrote informally above. *)

(** For particular numbers, we can now prove that the Collatz sequence
    reaches [1] (we'll go through the details of how it works a bit
    later in the chapter): *)

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

(** The Collatz conjecture then states that the sequence beginning
    from _any_ positive number reaches [1]: *)

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

(** If you succeed in proving this conjecture, you've got a bright
    future as a number theorist!  But don't spend too long on it --
    it's been open since 1937. *)

(* ================================================================= *)
(** ** Example: Binary relation for comparing numbers *)

(** A binary _relation_ on a set [X] has Coq type [X -> X -> Prop].
    This is a family of propositions parameterized by two elements of
    [X] -- i.e., a proposition about pairs of elements of [X]. *)

(** For example, one familiar binary relation on [nat] is [le : nat ->
    nat -> Prop], the less-than-or-equal-to relation, which can be
    inductively defined by the following two rules: *)

(**

                           ------ (le_n)
                           le n n

                           le n m
                         ---------- (le_S)
                         le n (S m)
*)
(** These rules say that there are two ways to show that a
    number is less than or equal to another: either observe that they
    are the same number, or, if the second has the form [S m], give
    evidence that the first is less than or equal to [m]. *)

(** This corresponds to the following inductive definition in Coq: *)

Module LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

(** This definition is a bit simpler and more elegant than the Boolean function
    [leb] we defined in [Basics]. As usual, [le] and [leb] are
    equivalent, and there is an exercise about that later. *)

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

End LePlayground.

(* ================================================================= *)
(** ** Example: Transitive Closure *)

(** As another example, the _transitive closure_ of a relation [R]
    is the smallest relation that contains [R] and that is transitive.
    This can be defined by the following two rules:

                     R x y
                ---------------- (t_step)
                clos_trans R x y

       clos_trans R x y    clos_trans R y z
       ------------------------------------ (t_trans)
                clos_trans R x z

    In Coq this looks as follows:
*)

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

(** For example, suppose we define a "parent of" relation on a group
    of people... *)

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

(** In this example, [Sage] is a parent of both [Cleo] and
    [Ridley]; and [Cleo] is a parent of [Moss]. *)

(** The [parent_of] relation is not transitive, but we can define
   an "ancestor of" relation as its transitive closure: *)

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

(** Here is a derivation showing that Sage is an ancestor of Moss:

 ———————————————————(po_SC)     ———————————————————(po_CM)
 parent_of Sage Cleo            parent_of Cleo Moss
—————————————————————(t_step)  —————————————————————(t_step)
ancestor_of Sage Cleo          ancestor_of Cleo Moss
————————————————————————————————————————————————————(t_trans)
                ancestor_of Sage Moss
*)

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.

(** Computing the transitive closure can be undecidable even for
    a relation R that is decidable (e.g., the [cms] relation below), so in
    general we can't expect to define transitive closure as a boolean
    function. Fortunately, Coq allows us to define transitive closure
    as an inductive relation.

    The transitive closure of a binary relation cannot, in general, be
    expressed in first-order logic. The logic of Coq is, however, much
    more powerful, and can easily define such inductive relations. *)

(* ================================================================= *)
(** ** Example: Reflexive and Transitive Closure *)

(** As another example, the _reflexive and transitive closure_
    of a relation [R] is the
    smallest relation that contains [R] and that is reflexive and
    transitive. This can be defined by the following three rules
    (where we added a reflexivity rule to [clos_trans]):

                        R x y
                --------------------- (rt_step)
                clos_refl_trans R x y

                --------------------- (rt_refl)
                clos_refl_trans R x x

     clos_refl_trans R x y    clos_refl_trans R y z
     ---------------------------------------------- (rt_trans)
                clos_refl_trans R x z
*)

Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

(** For instance, this enables an equivalent definition of the Collatz
    conjecture.  First we define the binary relation corresponding to
    the Collatz step function [csf]: *)

Definition cs (n m : nat) : Prop := csf n = m.

(** This Collatz step relation can be used in conjunction with the
    reflexive and transitive closure operation to define a Collatz
    multi-step ([cms]) relation, expressing that a number [n]
    reaches another number [m] in zero or more Collatz steps: *)

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(** This [cms] relation defined in terms of
    [clos_refl_trans] allows for more interesting derivations than the
    linear ones of the directly-defined [Collatz_holds_for] relation:

csf 16 = 8         csf 8 = 4         csf 4 = 2         csf 2 = 1
————————(rt_step)  ———————(rt_step)  ———————(rt_step)  ———————(rt_step)
cms 16 8           cms 8 4           cms 4 2           cms 2 1
—————————————————————————(rt_trans)  ————————————————————————(rt_trans)
        cms 16 4                              cms 4 1
        —————————————————————————————————————————————(rt_trans)
                           cms 16 1
*)

(** **** Exercise: 1 star, standard, optional (clos_refl_trans_sym)

    How would you modify the [clos_refl_trans] definition above so as
    to define the reflexive, symmetric, and transitive closure? *)

(* FILL IN HERE

    [] *)

(* ================================================================= *)
(** ** Example: Permutations *)

(** The familiar mathematical concept of _permutation_ also has an
    elegant formulation as an inductive relation.  For simplicity,
    let's focus on permutations of lists with exactly three
    elements. We can define them by the following rules:

               --------------------- (perm3_swap12)
               Perm3 [a;b;c] [b;a;c]

               --------------------- (perm3_swap23)
               Perm3 [a;b;c] [a;c;b]

            Perm3 l1 l2       Perm3 l2 l3
            ----------------------------- (perm3_trans)
                     Perm3 l1 l3

    For instance we can derive [Perm3 [1;2;3] [3;2;1]] as follows:

————————(perm_swap12)  —————————————————————(perm_swap23)
Perm3 [1;2;3] [2;1;3]  Perm3 [2;1;3] [2;3;1]
——————————————————————————————(perm_trans)  ————————————(perm_swap12)
    Perm3 [1;2;3] [2;3;1]                   Perm [2;3;1] [3;2;1]
    —————————————————————————————————————————————————————(perm_trans)
                      Perm3 [1;2;3] [3;2;1]
*)

(** This definition says:
      - If [l2] can be obtained from [l1] by swapping the first and
        second elements, then [l2] is a permutation of [l1].
      - If [l2] can be obtained from [l1] by swapping the second and
        third elements, then [l2] is a permutation of [l1].
      - If [l2] is a permutation of [l1] and [l3] is a permutation of
        [l2], then [l3] is a permutation of [l1]. *)

(** In Coq [Perm3] is given the following inductive definition: *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(** **** Exercise: 1 star, standard, optional (perm)

    According to this definition, is [[1;2;3]] a permutation of
    itself? *)

(* FILL IN HERE

    [] *)

(* ================================================================= *)
(** ** Example: Evenness (yet again) *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true] (using the recursive boolean function [even]), or

      (2) [exists k, n = double k] (using an existential quantifier). *)

(** A third possibility, which we'll use as a simple running example
    here, is to say that a number is even if we can
    _establish_ its evenness from the following two rules:

                          ---- (ev_0)
                          ev 0

                          ev n
                      ------------ (ev_SS)
                      ev (S (S n))
*)

(** Intuitively these rules say that:
       - The number [0] is even.
       - If [n] is even, then [S (S n)] is even. *)

(** (Defining evenness in this way may seem a bit confusing,
    since we have already seen two perfectly good ways of doing
    it. It makes a convenient running example because it is
    simple and compact, but we will soon return to the more compelling
    examples above.) *)

(** To illustrate how this new definition of evenness works, let's
    imagine using it to show that [4] is even:

                           ———— (ev_0)
                           ev 0
                       ———————————— (ev_SS)
                       ev (S (S 0))
                   ———————————————————— (ev_SS)
                   ev (S (S (S (S 0))))
*)

(** In words, to show that [4] is even, by rule [ev_SS], it
   suffices to show that [2] is even. This, in turn, is again
   guaranteed by rule [ev_SS], as long as we can show that [0] is
   even. But this last fact follows directly from the [ev_0] rule. *)

(** We can translate the informal definition of evenness from above
    into a formal [Inductive] declaration, where each "way that a
    number can be even" corresponds to a separate constructor: *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** Such definitions are interestingly different from previous uses of
    [Inductive] for defining inductive datatypes like [nat] or [list].
    For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of [ev]
    appears to the _right_ of the colon on the first line, it is
    allowed to take _different_ values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

    or equivalently:

    Inductive list (X:Type) : Type :=
      | nil                       : list X
      | cons (x : X) (l : list X) : list X.

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same type (i.e., [list X]).  But if we had tried to bring [nat]
   to the left of the colon in defining [ev], we would have seen an
   error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]" as 1st
        argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter, while in [Inductive ev : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** Beyond this syntactic distinction, we can think of the inductive
    definition of [ev] as defining a Coq property [ev : nat -> Prop],
    together with two "evidence constructors": *)

Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).

(** In fact, Coq also accepts the following equivalent definition of [ev]: *)

Module EvPlayground.

Inductive ev : nat -> Prop :=
  | ev_0  : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.

(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used just like proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Constructing Evidence for Permutations *)

(** Similarly we can apply the evidence constructors to obtain
    evidence of [Perm3 [1;2;3] [3;2;1]]: *)

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.

(** And again we can equivalently use function application syntax to
    combine several constructors. Note that the Coq type checker can
    infer not only types, but also nats and lists. *)

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.

(** So the informal derivation trees we drew above are not too far
    from what's happening formally.  Formally we're using the evidence
    constructors to build _evidence trees_, similar to the finite trees we
    built using the constructors of data types such as nat, list,
    binary trees, etc. *)

(** **** Exercise: 1 star, standard (Perm3) *)
Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  (* FILL IN HERE *) Admitted.

Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, reasoning about how it could have been
    built.

    Defining [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the proposition
    [ev n], then we know that [E] must be one of two things:

      - [E = ev_0] and [n = O], or
      - [E = ev_SS n' E'], where [n = S (S n')] and [E'] is
        evidence for [ev n']. *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Destructing and Inverting Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of [ev n], using
    [destruct]. *)

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived.

    Here, there are two ways to prove [ev n], and the inversion
    lemma makes this explicit. *)

(** **** Exercise: 1 star, standard (le_inversion)

    Let's prove a similar inversion lemma for [le]. *)
Theorem le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can use the inversion lemma that we proved above to help
    structure proofs: *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. apply ev_inversion in E. destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

(** Note how the inversion lemma produces two subgoals, which
    correspond to the two ways of proving [ev].  The first subgoal is
    a contradiction that is discharged with [discriminate].  The
    second subgoal makes use of [injection] and [rewrite].

    Coq provides a handy tactic called [inversion] that factors out
    this common pattern, saving us the trouble of explicitly stating
    and proving an inversion lemma for every [Inductive] definition we
    make.

    Here, the [inversion] tactic can detect (1) that the first case,
    where [n = 0], does not apply and (2) that the [n'] that appears
    in the [ev_SS] case must be the same as [n].  It includes an
    "[as]" annotation similar to [destruct], allowing us to assign
    names rather than have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Hnn'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. Compare: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)

    Prove the following result using [inversion].  (For extra
    practice, you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied to analyze
    evidence for arbitrary inductively defined propositions, not just
    equality.  As examples, we'll use it to re-prove some theorems
    from chapter [Tactics].  (Here we are being a bit lazy by
    omitting the [as] clause from [inversion], thereby asking Coq to
    choose names for the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.
      - Suppose the name [H] refers to an assumption [P] in the
        current context, where [P] has been defined by an [Inductive]
        declaration.
      - Then, for each of the constructors of [P], [inversion H]
        generates a subgoal in which [H] has been replaced by the
        specific conditions under which this constructor could have
        been used to prove [P].
      - Some of these subgoals will be self-contradictory; [inversion]
        throws these away.
      - The ones that are left represent the cases that must be proved
        to establish the original goal.  For those, [inversion] adds
        to the proof context all equations that must hold of the
        arguments given to [P] -- e.g., [n' = n] in the proof of
        [evSS_ev]). *)

(** The [ev_double] exercise above allows us to easily show that
    our new notion of evenness is implied by the two earlier ones
    (since, by [even_bool_prop] in chapter [Logic], we already
    know that those are equivalent to each other). To show that all
    three coincide, we just need the following lemma. *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *) unfold Even.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy seems
    unpromising, because (as we've noted before) the induction
    hypothesis will talk about [n-1] (which is _not_ even!).  Thus, it
    seems better to first try [inversion] on the evidence for [ev].
    Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - (* E = ev_SS n' E'

    Unfortunately, the second case is harder.  We need to show [exists
    n0, S (S n') = double n0], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]: namely
    [E'].  More formally, we could finish our proof if we could show
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result would suffice. *)
    assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.

    (** Unfortunately, now we are stuck. To see this clearly, let's
        move [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is obvious that we are trying to prove another instance
        of the same theorem we set out to prove -- only here we are
        talking about [n'] instead of [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this story feels familiar, it is no coincidence: We
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have been used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of [n] holds for all even numbers (i.e.,
    those for which [ev n] holds), we can use induction on [ev
    n]. This requires us to prove two things, corresponding to the two
    ways in which [ev n] could have been constructed. If it was
    constructed by [ev_0], then [n=0] and the property must hold of
    [0]. If it was constructed by [ev_SS], then the evidence of [ev n]
    is of the form [ev_SS n' E'], where [n = S (S n')] and [E'] is
    evidence for [ev n']. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for [n']. *)

(** Let's try proving that lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas -- in particular for
    formalizing the semantics of programming languages. *)

(** The following exercises provide simpler examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint: Is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the [Logic]
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** We can do similar inductive proofs on the [Perm3] relation,
    which we defined earlier as follows: *)

Module Perm3Reminder.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

End Perm3Reminder.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    * apply IH23.
    * apply IH12.
Qed.

(** **** Exercise: 2 stars, standard (Perm3_In) *)
Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (Perm3_NotIn) *)
Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (NotPerm3)

    Proving that something is NOT a permutation is quite tricky. Some
    of the lemmas above, like [Perm3_In] can be useful for this. *)
Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ################################################################# *)
(** * Exercising with Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on numbers
    that we briefly saw above. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** (We've written the definition a bit differently this time,
    giving explicit names to the arguments to the constructors and
    moving them to the left of the colons.) *)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m : nat) := le (S n) m.

Notation "n < m" := (lt n m).

(** The [>=] operation is defined in terms of [<=]. *)

Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

End Playground.


(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

(** **** Exercise: 3 stars, standard, especially useful (le_facts) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (plus_le_facts1) *)

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
 (* FILL IN HERE *) Admitted.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  (** Hint: May be easiest to prove by induction on [n]. *)
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (plus_le_facts2) *)

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (lt_facts) *)
Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (leb_le) *)
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** Hint: The next two can easily be proved without using [induction]. *)

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq. *)

Definition fR : nat -> nat -> nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3]. *)

Inductive subseq : list nat -> list nat -> Prop :=
(* FILL IN HERE *)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* Hint: be careful about what you are doing induction on and which
     other things need to be generalized... *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we sometimes
    need to relate boolean computations to statements in [Prop].  But
    performing this conversion as we did there can result in tedious
    proof scripts.  Consider the proof of the following theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = nil *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this sort of reasoning by defining an inductive
    proposition that yields a better case-analysis principle for [n =?
    m].  Instead of generating the assumption [(n =? m) = true], which
    usually requires some massaging before we can use it, this
    principle gives us right away the assumption we really need: [n =
    m].

    Following the terminology introduced in [Logic], we call this
    the "reflection principle for equality on numbers," and we say
    that the boolean [n =? m] is _reflected in_ the proposition [n =
    m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  It states that the property [P]
    _reflects_ (intuitively, is equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].

    To see this, notice that, by definition, the only way we can
    produce evidence for [reflect P true] is by showing [P] and then
    using the [ReflectT] constructor.  If we invert this statement,
    this means that we can extract evidence for [P] from a proof of
    [reflect P true].

    Similarly, the only way to show [reflect P false] is by tagging
    evidence for [~ P] with the [ReflectF] constructor. *)

(** To put this observation to work, we first prove that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can think of [reflect] as a variant of the usual "if and only
    if" connective; the advantage of [reflect] is that, by destructing
    a hypothesis or lemma of the form [reflect P b], we can perform
    case analysis on [b] while _at the same time_ generating
    appropriate hypothesis in the two branches ([P] in the first
    subgoal and [~ P] in the second). *)

(** Let's use [reflect] to produce a smoother proof of
    [filter_not_empty_In].

    We begin by recasting the [eqb_eq] lemma in terms of [reflect]: *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** The proof of [filter_not_empty_In] now goes as follows.  Notice
    how the calls to [destruct] and [rewrite] in the earlier proof of
    this theorem are combined here into a single call to
    [destruct]. *)

(** (To see this clearly, execute the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [EQnm | NEQnm].
    + (* n = m *)
      intros _. rewrite EQnm. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice)

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** This small example shows reflection giving us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters.

    This way of using [reflect] was popularized by _SSReflect_, a Coq
    library that has been used to formalize important results in
    mathematics, including the 4-color theorem and the Feit-Thompson
    theorem.  The name SSReflect stands for _small-scale reflection_,
    i.e., the pervasive use of reflection to streamline small proof
    steps by turning them into boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn)

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] has two occurrences of the element [1] but
    does not stutter.)  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* FILL IN HERE *)
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(*
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    First define what it means for one list to be a merge of two
    others.  Do this with an inductive relation, not a [Fixpoint].  *)

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
(* FILL IN HERE *)
.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  (* FILL IN HERE *) Admitted.

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* FILL IN HERE

    [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes)

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type} : list X -> Prop :=
(* FILL IN HERE *)
.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

Module RecallIn.
   Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
     match l with
     | [] => False
     | x' :: l' => x' = x \/ In A x l'
     end.
End RecallIn.

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* FILL IN HERE *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy and useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)
Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * ProofObjects: The Curry-Howard Correspondence *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

(** "Algorithms are the computational content of proofs."
    (Robert Harper) *)

(** We have seen that Coq has mechanisms both for _programming_,
    using inductive data types like [nat] or [list] and functions over
    these types, and for _proving_ properties of these programs, using
    inductive propositions (like [ev]), implication, universal
    quantification, and the like.  So far, we have mostly treated
    these mechanisms as if they were quite separate, and for many
    purposes this is a good way to think.  But we have also seen hints
    that Coq's programming and proving facilities are closely related.
    For example, the keyword [Inductive] is used to declare both data
    types and propositions, and [->] is used both to describe the type
    of functions on data and logical implication.  This is not just a
    syntactic accident!  In fact, programs and proofs in Coq are
    almost the same thing.  In this chapter we will study how this
    works.

    We have already seen the fundamental idea: provability in Coq is
    represented by concrete _evidence_.  When we construct the proof
    of a basic proposition, we are actually building a tree of
    evidence, which can be thought of as a data structure.

    If the proposition is an implication like [A -> B], then its proof
    will be an evidence _transformer_: a recipe for converting
    evidence for A into evidence for B.  So at a fundamental level,
    proofs are simply programs that manipulate evidence. *)

(** Question: If evidence is data, what are propositions themselves?

    Answer: They are types! *)

(** Look again at the formal definition of the [ev] property.

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
*)

(** Suppose we introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can say "is a proof of."  For example,
    the second line in the definition of [ev] declares that [ev_0 : ev
    0].  Instead of "[ev_0] has type [ev 0]," we can say that "[ev_0]
    is a proof of [ev 0]." *)

(** This pun between types and propositions -- between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for" -- is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation:

                 propositions  ~  types
                 proofs        ~  programs

    See [Wadler 2015] (in Bib.v) for a brief history and up-to-date
    exposition. *)

(** Many useful insights follow from this connection.  To begin with,
    it gives us a natural interpretation of the type of the [ev_SS]
    constructor: *)

Check ev_SS
  : forall n,
    ev n ->
    ev (S (S n)).

(** This can be read "[ev_SS] is a constructor that takes two
    arguments -- a number [n] and evidence for the proposition [ev
    n] -- and yields evidence for the proposition [ev (S (S n))]." *)

(** Now let's look again at a previous proof involving [ev].

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.
*)

(** As with ordinary data values and functions, we can use the [Print]
    command to see the _proof object_ that results from this proof
    script. *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
      : ev 4  *)

(** Indeed, we can also write down this proof object directly,
    without the need for a separate proof script: *)

Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.

(** The expression [ev_SS 2 (ev_SS 0 ev_0)] can be thought of as
    instantiating the parameterized constructor [ev_SS] with the
    specific arguments [2] and [0] plus the corresponding proof
    objects for its premises [ev 2] and [ev 0].  Alternatively, we can
    think of [ev_SS] as a primitive "evidence constructor" that, when
    applied to a particular number, wants to be further applied to
    evidence that this number is even; its type,

      forall n, ev n -> ev (S (S n)),

    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] expresses the fact that the constructor
    [nil] can be thought of as a function from types to empty lists
    with elements of that type. *)

(** We saw in the [Logic] chapter that we can use function
    application syntax to instantiate universally quantified variables
    in lemmas, as well as to supply evidence for assumptions that
    these lemmas impose.  For instance:

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.
*)

(* ################################################################# *)
(** * Proof Scripts *)

(** The _proof objects_ we've been discussing lie at the core of how
    Coq operates.  When Coq is following a proof script, what is
    happening internally is that it is gradually constructing a proof
    object -- a term whose type is the proposition being proved.  The
    tactics between [Proof] and [Qed] tell it how to build up a term
    of the required type.  To see this process in action, let's use
    the [Show Proof] command to display the current state of the proof
    tree at various points in the following tactic proof. *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(** At any given moment, Coq has constructed a term with a
    "hole" (indicated by [?Goal] here, and so on), and it knows what
    type of evidence is needed to fill this hole.

    Each hole corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    evidence we've built is stored in the global context under the name
    given in the [Theorem] command. *)

(** Tactic proofs are convenient, but they are not essential in Coq:
    in principle, we can always just construct the required evidence
    by hand. Then we can use [Definition] (rather than [Theorem]) to
    introduce a global name for this evidence. *)

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

(** **** Exercise: 2 stars, standard (eight_is_even)

    Give a tactic proof and a proof object showing that [ev 8]. *)

Theorem ev_8 : ev 8.
Proof.
  (* FILL IN HERE *) Admitted.

Definition ev_8' : ev 8
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ################################################################# *)
(** * Quantifiers, Implications, Functions *)

(** In Coq's computational universe (where data structures and
    programs live), there are two sorts of values that have arrows in
    their types: _constructors_ introduced by [Inductive]ly defined
    data types, and _functions_.

    Similarly, in Coq's logical universe (where we carry out proofs),
    there are two ways of giving evidence for an implication:
    constructors introduced by [Inductive]ly defined propositions,
    and... functions! *)

(** For example, consider this statement:

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.
*)

(** What is the proof object corresponding to [ev_plus4]? *)

(** We're looking for an expression whose _type_ is [forall n, ev n ->
    ev (4 + n)] -- that is, a _function_ that takes two arguments (one
    number and a piece of evidence) and returns a piece of evidence!

    Here it is: *)

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]," and that Coq treats [4 + n] and [S (S (S (S n)))]
    as synonyms. Another equivalent way to write this definition is: *)

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

(** When we view the proposition being proved by [ev_plus4] as a
    function type, one interesting point becomes apparent: The second
    argument's type, [ev n], mentions the _value_ of the first
    argument, [n].

    While such _dependent types_ are not found in most mainstream
    programming languages, they can be quite useful in programming
    too, as the flurry of activity in the functional programming
    community over the past couple of decades demonstrates. *)

(** Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a
    name to the type on the left-hand side of the arrow:

           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat          -> nat
*)

(** For example, consider this proposition: *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

(** A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    even.  But the name [E] for this evidence is not used in the rest
    of the statement of [ev_plus2], so it's a bit silly to bother
    making up a name for it.  We could write it like this instead,
    using the dummy identifier [_] in place of a real name: *)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

(** Or, equivalently, we can write it in a more familiar way: *)

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ################################################################# *)
(** * Programming with Tactics *)

(** If we can build proofs by giving explicit terms rather than
    executing tactic scripts, you may be wondering whether we can
    build _programs_ using tactics rather than by writing down
    explicit terms.

    Naturally, the answer is yes! *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)

(** Notice that we terminated the [Definition] with a [.] rather than
    with [:=] followed by a term.  This tells Coq to enter _proof
    scripting mode_ to build an object of type [nat -> nat].  Also, we
    terminate the proof with [Defined] rather than [Qed]; this makes
    the definition _transparent_ so that it can be used in computation
    like a normally-defined function.  ([Qed]-defined objects are
    opaque during computation.)

    This feature is mainly useful for writing functions with dependent
    types, which we won't explore much further in this book.  But it
    does illustrate the uniformity and orthogonality of the basic
    ideas in Coq. *)

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

(** Inductive definitions are powerful enough to express most of the
    logical connectives we have seen so far.  Indeed, only universal
    quantification (with implication as a special case) is built into
    Coq; all the others are defined inductively.

    Let's see how. *)

Module Props.

(* ================================================================= *)
(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for
    [P /\ Q] to consist of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** This similarity should clarify why [destruct] and [intros]
    patterns can be used on a conjunctive hypothesis.  Case analysis
    allows us to consider all possible ways in which [P /\ Q] was
    proved -- here just one (the [conj] constructor). *)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

(** Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor.  In particular,
    it works for [and]: *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(** **** Exercise: 2 stars, standard (conj_fact)

    Construct a proof object for the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** Disjunction *)

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunct: *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. *)

(** Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
  Show Proof.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

(** **** Exercise: 2 stars, standard (or_commut')

    Construct a proof object for the following proposition. *)

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

(** This probably needs a little unpacking.  The core definition is
    for a type former [ex] that can be used to build propositions of
    the form [ex P], where [P] itself is a _function_ from witness
    values in the type [A] to propositions.  The [ex_intro]
    constructor then offers a way of constructing evidence for [ex P],
    given a witness [x] and a proof of [P x].

    The notation in the standard library is a slight extension of
    the above, enabling syntactic forms such as [exists x y, P x y]. *)

(** The more familiar form [exists x, ev x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n) : Prop.

(** Here's how to define an explicit proof object involving [ex]: *)

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** **** Exercise: 2 stars, standard (ex_ev_Sn)

    Construct a proof object for the following proposition. *)

Definition ex_ev_Sn : ex (fun n => ev (S n))
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** To destruct existentials in a proof term we simply use match: *)
Definition dist_exists_or_term (X:Type) (P Q : X -> Prop) :
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x) :=
  fun H => match H with
           | ex_intro _ x Hx =>
               match Hx with
               | or_introl HPx => or_introl (ex_intro _ x HPx)
               | or_intror HQx => or_intror (ex_intro _ x HQx)
               end
           end.

(** **** Exercise: 2 stars, standard (ex_match)

    Construct a proof object for the following proposition: *)
Definition ex_match : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x -> Q x) ->
  (exists x, P x) -> (exists x, Q x)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** [True] and [False] *)

(** The inductive definition of the [True] proposition is simple: *)

Inductive True : Prop :=
  | I : True.

(** It has one constructor (so every proof of [True] is the same, so
    being given a proof of [True] is not informative.) *)

(** **** Exercise: 1 star, standard (p_implies_true)

    Construct a proof object for the following proposition. *)

Definition p_implies_true : forall P, P -> True
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** [False] is equally simple -- indeed, so simple it may look
    syntactically wrong at first glance! *)

Inductive False : Prop := .

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. For example, there is
    no way to complete the following definition such that it
    succeeds. *)

Fail
  Definition contra : False :=
  42.

(** But it is possible to destruct [False] by pattern matching. There can
    be no patterns that match it, since it has no constructors.  So
    the pattern match also is so simple it may look syntactically
    wrong at first glance. *)

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

(** Since there are no branches to evaluate, the [match] expression
    can be considered to have any type we want, including [0 = 1].
    Fortunately, it's impossible to ever cause the [match] to be
    evaluated, because we can never construct a value of type [False]
    to pass to the function. *)

(** **** Exercise: 1 star, standard (ex_falso_quodlibet')

    Construct a proof object for the following proposition. *)

Definition ex_falso_quodlibet' : forall P, False -> P
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

End Props.

(* ################################################################# *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  We can define
    it ourselves: *)

Module EqualityPlayground.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

(** The way to think about this definition (which is just a slight
    variant of the standard library's) is that, given a set [X], it
    defines a _family_ of propositions "[x] is equal to [y]," indexed
    by pairs of values ([x] and [y]) from [X].  There is just one way
    of constructing evidence for members of this family: applying the
    constructor [eq_refl] to a type [X] and a single value [x : X],
    which yields evidence that [x] is equal to [x].

    Other types of the form [eq x y] where [x] and [y] are not the
    same are thus uninhabited. *)

(** We can use [eq_refl] to construct evidence that, for example, [2 =
    2].  Can we also use it to construct evidence that [1 + 1 = 2]?
    Yes, we can.  Indeed, it is the very same piece of evidence!

    The reason is that Coq treats as "the same" any two terms that are
    _convertible_ according to a simple set of computation rules.

    These rules, which are similar to those used by [Compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.  *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

(** The [reflexivity] tactic that we have used to prove
    equalities up to now is essentially just shorthand for [apply
    eq_refl].

    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).

    But you can see them directly at work in the following explicit
    proof objects: *)

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].

(** We can also pattern-match on an equality proof: *)
Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

(** By pattern-matching against [n1 == n2], we obtain a term [n]
    that replaces [n1] and [n2] in the type we have to produce, so
    instead of [(S n1) == (S n2)], we now have to produce something
    of type [(S n) == (S n)], which we establish by [eq_refl (S n)]. *)

(** A tactic-based proof runs into some difficulties if we try to use
    our usual repertoire of tactics, such as [rewrite] and
    [reflexivity]. Those work with *setoid* relations that Coq knows
    about, such as [=], but not our [==]. We could prove to Coq that
    [==] is a setoid, but a simpler way is to use [destruct] and
    [apply] instead. *)

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq. (* doesn't work for _our_ == relation *)
  destruct Heq as [n]. (* n1 and n2 replaced by n in the goal! *)
  Fail reflexivity. (* doesn't work for _our_ == relation *)
  apply eq_refl.
Qed.

(** **** Exercise: 2 stars, standard (eq_cons)

    Construct the proof object for the following theorem. Use pattern
    matching on the equality hypotheses. *)

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (equality__leibniz_equality)

    The inductive definition of equality implies _Leibniz equality_:
    what we mean when we say "[x] and [y] are equal" is that every
    property on [P] that is true of [x] is also true of [y]. Prove
    that. *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (equality__leibniz_equality_term)

    Construct the proof object for the previous exercise.  All it
    requires is anonymous functions and pattern-matching; the large
    proof term constructed by tactics in the previous exercise is
    needessly complicated. Hint: pattern-match as soon as possible. *)
Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (leibniz_equality__equality)

    Show that, in fact, the inductive definition of equality is
    _equivalent_ to Leibniz equality.  Hint: the proof is quite short;
    about all you need to do is to invent a clever property [P] to
    instantiate the antecedent.*)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End EqualityPlayground.

(* ================================================================= *)
(** ** Inversion, Again *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves.

    In general, the [inversion] tactic...

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,

      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are
    two constructors, so two subgoals get generated.  The
    conclusion (result type) of the constructor ([P \/ Q]) doesn't
    place any restrictions on the form of [P] or [Q], so we don't get
    any extra equalities in the context of the subgoal. *)

(** _Example_: If we invert a hypothesis built with [and], there is
    only one constructor, so only one subgoal gets generated.  Again,
    the conclusion (result type) of the constructor ([P /\ Q]) doesn't
    place any restrictions on the form of [P] or [Q], so we don't get
    any extra equalities in the context of the subgoal.  The
    constructor does have two arguments, though, and these can be seen
    in the context in the subgoal. *)

(** _Example_: If we invert a hypothesis built with [eq], there is
    again only one constructor, so only one subgoal gets generated.
    Now, though, the form of the [eq_refl] constructor does give us
    some extra information: it tells us that the two arguments to [eq]
    must be the same!  The [inversion] tactic adds this fact to the
    context. *)

(* ################################################################# *)
(** * Coq's Trusted Computing Base *)

(** One question that arises with any automated proof assistant
    is "why should we trust it?" -- i.e., what if there is a bug in
    the implementation that renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on. *)

(** There are a few additional wrinkles:

    First, since Coq types can themselves be expressions, the checker
    must normalize these (by using the computation rules) before
    comparing them.

    Second, the checker must make sure that [match] expressions are
    _exhaustive_.  That is, there must be an arm for every possible
    constructor.  To see why, consider the following alleged proof
    object: *)

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.

(** All the types here match correctly, but the [match] only
    considers one of the possible constructors for [or].  Coq's
    exhaustiveness check will reject this definition.

    Third, the checker must make sure that each recursive function
    terminates.  It does this using a syntactic check to make sure
    that each recursive call is on a subexpression of the original
    argument.  To see why this is essential, consider this alleged
    proof: *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

(** Recursive function [infinite_loop] purports to return a
    value of any type [X] that you would like.  (The [struct]
    annotation on the function tells Coq that it recurses on argument
    [n], not [X].)  Were Coq to allow [infinite_loop], then [falso]
    would be definable, thus giving evidence for [False].  So Coq rejects
    [infinite_loop]. *)

(** Note that the soundness of Coq depends only on the
    correctness of this typechecking engine, not on the tactic
    machinery.  If there is a bug in a tactic implementation (and this
    certainly does happen!), that tactic might construct an invalid
    proof term.  But when you type [Qed], Coq checks the term for
    validity from scratch.  Only theorems whose proofs pass the
    type-checker can be used in further proof developments.  *)

(* ################################################################# *)
(** * More Exercises *)

(** Most of the following theorems were already proved with tactics in
    [Logic].  Now construct the proof objects for them
    directly. *)

(** **** Exercise: 2 stars, standard (and_assoc) *)
Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (or_distributes_over_and) *)
Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (negations) *)
Definition double_neg : forall P : Prop,
    P -> ~~P
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition de_morgan_not_or : forall P Q : Prop,
    ~ (P \/ Q) -> ~P /\ ~Q
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (currying) *)
Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R))
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof Irrelevance (Advanced) *)

(** In [Logic] we saw that functional extensionality could be
    added to Coq. A similar notion about propositions can also
    be defined (and added as an axiom, if desired): *)

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(** Propositional extensionality asserts that if two propositions are
    equivalent -- i.e., each implies the other -- then they are in
    fact equal. The _proof objects_ for the propositions might be
    syntactically different terms. But propositional extensionality
    overlooks that, just as functional extensionality overlooks the
    syntactic differences between functions. *)

(** **** Exercise: 1 star, advanced (pe_implies_or_eq)

    Prove the following consequence of propositional extensionality. *)

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, advanced (pe_implies_true_eq)

    Prove that if a proposition [P] is provable, then it is equal to
    [True] -- as a consequence of propositional extensionality. *)

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (pe_implies_pi)

    Acknowledgment: this theorem and its proof technique are inspired
    by Gert Smolka's manuscript Modeling and Proving in Computational
    Type Theory Using the Coq Proof Assistant, 2021. *)

(** Another, perhaps surprising, consequence of propositional
    extensionality is that it implies _proof irrelevance_, which
    asserts that all proof objects for a proposition are equal.*)

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

(** Prove that fact. Use [pe_implies_true_eq] to establish that the
    proposition [P] in [proof_irrelevance] is equal to [True]. Leverage
    that equality to establish that both proof objects [pf1] and
    [pf2] must be just [I]. *)

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* 2025-04-02 17:45 *)
