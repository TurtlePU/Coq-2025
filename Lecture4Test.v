Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From Lectures Require Import Lecture4.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From Lectures Require Import Lecture4.
Import Check.

Goal True.

idtac "-------------------  In_map_iff  --------------------".
idtac " ".

idtac "#> In_map_iff".
idtac "Possible points: 2".
check_type @In_map_iff (
(forall (A B : Type) (f : A -> B) (l : list A) (y : B),
 @In B y (@map A B f l) <-> (exists x : A, f x = y /\ @In A x l))).
idtac "Assumptions:".
Abort.
Print Assumptions In_map_iff.
Goal True.
idtac " ".

idtac "-------------------  In_app_iff  --------------------".
idtac " ".

idtac "#> In_app_iff".
idtac "Possible points: 2".
check_type @In_app_iff (
(forall (A : Type) (l l' : list A) (a : A),
 @In A a (l ++ l') <-> @In A a l \/ @In A a l')).
idtac "Assumptions:".
Abort.
Print Assumptions In_app_iff.
Goal True.
idtac " ".

idtac "-------------------  All  --------------------".
idtac " ".

idtac "#> All_In".
idtac "Possible points: 3".
check_type @All_In (
(forall (T : Type) (P : T -> Prop) (l : list T),
 (forall x : T, @In T x l -> P x) <-> @All T P l)).
idtac "Assumptions:".
Abort.
Print Assumptions All_In.
Goal True.
idtac " ".

idtac "-------------------  even_double_conv  --------------------".
idtac " ".

idtac "#> even_double_conv".
idtac "Possible points: 3".
check_type @even_double_conv (
(forall n : nat,
 exists k : nat, n = (if even n then double k else S (double k)))).
idtac "Assumptions:".
Abort.
Print Assumptions even_double_conv.
Goal True.
idtac " ".

idtac "-------------------  logical_connectives  --------------------".
idtac " ".

idtac "#> andb_true_iff".
idtac "Possible points: 1".
check_type @andb_true_iff (
(forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true)).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_iff.
Goal True.
idtac " ".

idtac "#> orb_true_iff".
idtac "Possible points: 1".
check_type @orb_true_iff (
(forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true)).
idtac "Assumptions:".
Abort.
Print Assumptions orb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  eqb_neq  --------------------".
idtac " ".

idtac "#> eqb_neq".
idtac "Possible points: 1".
check_type @eqb_neq ((forall x y : nat, (x =? y) = false <-> x <> y)).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_neq.
Goal True.
idtac " ".

idtac "-------------------  eqb_list  --------------------".
idtac " ".

idtac "#> eqb_list_true_iff".
idtac "Possible points: 3".
check_type @eqb_list_true_iff (
(forall (A : Type) (eqb : A -> A -> bool),
 (forall a1 a2 : A, eqb a1 a2 = true <-> a1 = a2) ->
 forall l1 l2 : list A, @eqb_list A eqb l1 l2 = true <-> l1 = l2)).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_list_true_iff.
Goal True.
idtac " ".

idtac "-------------------  All_forallb  --------------------".
idtac " ".

idtac "#> forallb_true_iff".
idtac "Possible points: 2".
check_type @forallb_true_iff (
(forall (X : Type) (test : X -> bool) (l : list X),
 @forallb X test l = true <-> @All X (fun x : X => test x = true) l)).
idtac "Assumptions:".
Abort.
Print Assumptions forallb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  tr_rev_correct  --------------------".
idtac " ".

idtac "#> tr_rev_correct".
idtac "Possible points: 6".
check_type @tr_rev_correct ((forall X : Type, @tr_rev X = @rev X)).
idtac "Assumptions:".
Abort.
Print Assumptions tr_rev_correct.
Goal True.
idtac " ".

idtac "-------------------  excluded_middle_irrefutable  --------------------".
idtac " ".

idtac "#> excluded_middle_irrefutable".
idtac "Possible points: 3".
check_type @excluded_middle_irrefutable ((forall P : Prop, ~ ~ (P \/ ~ P))).
idtac "Assumptions:".
Abort.
Print Assumptions excluded_middle_irrefutable.
Goal True.
idtac " ".

idtac "-------------------  not_exists_dist  --------------------".
idtac " ".

idtac "#> not_exists_dist".
idtac "Advanced".
idtac "Possible points: 3".
check_type @not_exists_dist (
(excluded_middle ->
 forall (X : Type) (P : X -> Prop),
 ~ (exists x : X, ~ P x) -> forall x : X, P x)).
idtac "Assumptions:".
Abort.
Print Assumptions not_exists_dist.
Goal True.
idtac " ".

idtac "-------------------  ev_double  --------------------".
idtac " ".

idtac "#> ev_double".
idtac "Possible points: 1".
check_type @ev_double ((forall n : nat, ev (double n))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_double.
Goal True.
idtac " ".

idtac "-------------------  Perm3  --------------------".
idtac " ".

idtac "#> Perm3_ex1".
idtac "Possible points: 0.5".
check_type @Perm3_ex1 ((@Perm3 nat [1; 2; 3] [2; 3; 1])).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_ex1.
Goal True.
idtac " ".

idtac "#> Perm3_refl".
idtac "Possible points: 0.5".
check_type @Perm3_refl ((forall (X : Type) (a b c : X), @Perm3 X [a; b; c] [a; b; c])).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_refl.
Goal True.
idtac " ".

idtac "-------------------  le_inversion  --------------------".
idtac " ".

idtac "#> le_inversion".
idtac "Possible points: 1".
check_type @le_inversion (
(forall n m : nat, n <= m -> n = m \/ (exists m' : nat, m = S m' /\ n <= m'))).
idtac "Assumptions:".
Abort.
Print Assumptions le_inversion.
Goal True.
idtac " ".

idtac "-------------------  inversion_practice  --------------------".
idtac " ".

idtac "#> SSSSev__even".
idtac "Possible points: 1".
check_type @SSSSev__even ((forall n : nat, ev (S (S (S (S n)))) -> ev n)).
idtac "Assumptions:".
Abort.
Print Assumptions SSSSev__even.
Goal True.
idtac " ".

idtac "-------------------  ev5_nonsense  --------------------".
idtac " ".

idtac "#> ev5_nonsense".
idtac "Possible points: 1".
check_type @ev5_nonsense ((ev 5 -> 2 + 2 = 9)).
idtac "Assumptions:".
Abort.
Print Assumptions ev5_nonsense.
Goal True.
idtac " ".

idtac "-------------------  ev_sum  --------------------".
idtac " ".

idtac "#> ev_sum".
idtac "Possible points: 2".
check_type @ev_sum ((forall n m : nat, ev n -> ev m -> ev (n + m))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_sum.
Goal True.
idtac " ".

idtac "-------------------  ev_ev__ev  --------------------".
idtac " ".

idtac "#> ev_ev__ev".
idtac "Advanced".
idtac "Possible points: 3".
check_type @ev_ev__ev ((forall n m : nat, ev (n + m) -> ev n -> ev m)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_ev__ev.
Goal True.
idtac " ".

idtac "-------------------  Perm3_In  --------------------".
idtac " ".

idtac "#> Perm3_In".
idtac "Possible points: 2".
check_type @Perm3_In (
(forall (X : Type) (x : X) (l1 l2 : list X),
 @Perm3 X l1 l2 -> @In X x l1 -> @In X x l2)).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_In.
Goal True.
idtac " ".

idtac "-------------------  le_facts  --------------------".
idtac " ".

idtac "#> le_trans".
idtac "Possible points: 0.5".
check_type @le_trans ((forall m n o : nat, m <= n -> n <= o -> m <= o)).
idtac "Assumptions:".
Abort.
Print Assumptions le_trans.
Goal True.
idtac " ".

idtac "#> O_le_n".
idtac "Possible points: 0.5".
check_type @O_le_n ((forall n : nat, 0 <= n)).
idtac "Assumptions:".
Abort.
Print Assumptions O_le_n.
Goal True.
idtac " ".

idtac "#> n_le_m__Sn_le_Sm".
idtac "Possible points: 0.5".
check_type @n_le_m__Sn_le_Sm ((forall n m : nat, n <= m -> S n <= S m)).
idtac "Assumptions:".
Abort.
Print Assumptions n_le_m__Sn_le_Sm.
Goal True.
idtac " ".

idtac "#> Sn_le_Sm__n_le_m".
idtac "Possible points: 1".
check_type @Sn_le_Sm__n_le_m ((forall n m : nat, S n <= S m -> n <= m)).
idtac "Assumptions:".
Abort.
Print Assumptions Sn_le_Sm__n_le_m.
Goal True.
idtac " ".

idtac "#> le_plus_l".
idtac "Possible points: 0.5".
check_type @le_plus_l ((forall a b : nat, a <= a + b)).
idtac "Assumptions:".
Abort.
Print Assumptions le_plus_l.
Goal True.
idtac " ".

idtac "-------------------  plus_le_facts1  --------------------".
idtac " ".

idtac "#> plus_le".
idtac "Possible points: 1".
check_type @plus_le ((forall n1 n2 m : nat, n1 + n2 <= m -> n1 <= m /\ n2 <= m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le.
Goal True.
idtac " ".

idtac "#> plus_le_cases".
idtac "Possible points: 1".
check_type @plus_le_cases ((forall n m p q : nat, n + m <= p + q -> n <= p \/ m <= q)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_cases.
Goal True.
idtac " ".

idtac "-------------------  plus_le_facts2  --------------------".
idtac " ".

idtac "#> plus_le_compat_l".
idtac "Possible points: 0.5".
check_type @plus_le_compat_l ((forall n m p : nat, n <= m -> p + n <= p + m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_compat_l.
Goal True.
idtac " ".

idtac "#> plus_le_compat_r".
idtac "Possible points: 0.5".
check_type @plus_le_compat_r ((forall n m p : nat, n <= m -> n + p <= m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_compat_r.
Goal True.
idtac " ".

idtac "#> le_plus_trans".
idtac "Possible points: 1".
check_type @le_plus_trans ((forall n m p : nat, n <= m -> n <= m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions le_plus_trans.
Goal True.
idtac " ".

idtac "-------------------  R_provability  --------------------".
idtac " ".

idtac "#> Manually graded: R.R_provability".
idtac "Possible points: 3".
print_manual_grade R.manual_grade_for_R_provability.
idtac " ".

idtac "-------------------  subsequence  --------------------".
idtac " ".

idtac "#> subseq_refl".
idtac "Advanced".
idtac "Possible points: 1".
check_type @subseq_refl ((forall l : list nat, subseq l l)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_refl.
Goal True.
idtac " ".

idtac "#> subseq_app".
idtac "Advanced".
idtac "Possible points: 2".
check_type @subseq_app (
(forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l1 (l2 ++ l3))).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_app.
Goal True.
idtac " ".

idtac "#> subseq_trans".
idtac "Advanced".
idtac "Possible points: 3".
check_type @subseq_trans (
(forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_trans.
Goal True.
idtac " ".

idtac "-------------------  reflect_iff  --------------------".
idtac " ".

idtac "#> reflect_iff".
idtac "Possible points: 2".
check_type @reflect_iff ((forall (P : Prop) (b : bool), reflect P b -> P <-> b = true)).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_iff.
Goal True.
idtac " ".

idtac "-------------------  eqbP_practice  --------------------".
idtac " ".

idtac "#> eqbP_practice".
idtac "Possible points: 3".
check_type @eqbP_practice (
(forall (n : nat) (l : list nat), count n l = 0 -> ~ @In nat n l)).
idtac "Assumptions:".
Abort.
Print Assumptions eqbP_practice.
Goal True.
idtac " ".

idtac "-------------------  nostutter_defn  --------------------".
idtac " ".

idtac "#> Manually graded: nostutter".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_nostutter.
idtac " ".

idtac "-------------------  filter_challenge  --------------------".
idtac " ".

idtac "#> merge_filter".
idtac "Advanced".
idtac "Possible points: 6".
check_type @merge_filter (
(forall (X : Set) (test : X -> bool) (l l1 l2 : list X),
 @merge X l1 l2 l ->
 @All X (fun n : X => test n = true) l1 ->
 @All X (fun n : X => test n = false) l2 -> @filter X test l = l1)).
idtac "Assumptions:".
Abort.
Print Assumptions merge_filter.
Goal True.
idtac " ".

idtac "-------------------  eight_is_even  --------------------".
idtac " ".

idtac "#> ev_8".
idtac "Possible points: 1".
check_type @ev_8 ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8.
Goal True.
idtac " ".

idtac "#> ev_8'".
idtac "Possible points: 1".
check_type @ev_8' ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8'.
Goal True.
idtac " ".

idtac "-------------------  conj_fact  --------------------".
idtac " ".

idtac "#> Props.conj_fact".
idtac "Possible points: 2".
check_type @Props.conj_fact ((forall P Q R : Prop, P /\ Q -> Q /\ R -> P /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.conj_fact.
Goal True.
idtac " ".

idtac "-------------------  or_commut'  --------------------".
idtac " ".

idtac "#> Props.or_commut'".
idtac "Possible points: 2".
check_type @Props.or_commut' ((forall P Q : Prop, P \/ Q -> Q \/ P)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.or_commut'.
Goal True.
idtac " ".

idtac "-------------------  ex_ev_Sn  --------------------".
idtac " ".

idtac "#> Props.ex_ev_Sn".
idtac "Possible points: 2".
check_type @Props.ex_ev_Sn ((exists n : nat, ev (S n))).
idtac "Assumptions:".
Abort.
Print Assumptions Props.ex_ev_Sn.
Goal True.
idtac " ".

idtac "-------------------  ex_match  --------------------".
idtac " ".

idtac "#> Props.ex_match".
idtac "Possible points: 2".
check_type @Props.ex_match (
(forall (A : Type) (P Q : A -> Prop),
 (forall x : A, P x -> Q x) -> (exists x : A, P x) -> exists x : A, Q x)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.ex_match.
Goal True.
idtac " ".

idtac "-------------------  p_implies_true  --------------------".
idtac " ".

idtac "#> Props.p_implies_true".
idtac "Possible points: 1".
check_type @Props.p_implies_true ((forall P : Type, P -> Props.True)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.p_implies_true.
Goal True.
idtac " ".

idtac "-------------------  ex_falso_quodlibet'  --------------------".
idtac " ".

idtac "#> Props.ex_falso_quodlibet'".
idtac "Possible points: 1".
check_type @Props.ex_falso_quodlibet' ((forall P : Type, Props.False -> P)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.ex_falso_quodlibet'.
Goal True.
idtac " ".

idtac "-------------------  eq_cons  --------------------".
idtac " ".

idtac "#> EqualityPlayground.eq_cons".
idtac "Possible points: 2".
check_type @EqualityPlayground.eq_cons (
(forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
 @EqualityPlayground.eq X h1 h2 ->
 @EqualityPlayground.eq (list X) t1 t2 ->
 @EqualityPlayground.eq (list X) (h1 :: t1) (h2 :: t2))).
idtac "Assumptions:".
Abort.
Print Assumptions EqualityPlayground.eq_cons.
Goal True.
idtac " ".

idtac "-------------------  equality__leibniz_equality  --------------------".
idtac " ".

idtac "#> EqualityPlayground.equality__leibniz_equality".
idtac "Possible points: 2".
check_type @EqualityPlayground.equality__leibniz_equality (
(forall (X : Type) (x y : X),
 @EqualityPlayground.eq X x y -> forall P : X -> Prop, P x -> P y)).
idtac "Assumptions:".
Abort.
Print Assumptions EqualityPlayground.equality__leibniz_equality.
Goal True.
idtac " ".

idtac "-------------------  equality__leibniz_equality_term  --------------------".
idtac " ".

idtac "#> EqualityPlayground.equality__leibniz_equality_term".
idtac "Possible points: 2".
check_type @EqualityPlayground.equality__leibniz_equality_term (
(forall (X : Type) (x y : X),
 @EqualityPlayground.eq X x y -> forall P : X -> Prop, P x -> P y)).
idtac "Assumptions:".
Abort.
Print Assumptions EqualityPlayground.equality__leibniz_equality_term.
Goal True.
idtac " ".

idtac "-------------------  and_assoc  --------------------".
idtac " ".

idtac "#> and_assoc".
idtac "Possible points: 2".
check_type @and_assoc ((forall P Q R : Prop, P /\ Q /\ R -> (P /\ Q) /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc.
Goal True.
idtac " ".

idtac "-------------------  or_distributes_over_and  --------------------".
idtac " ".

idtac "#> or_distributes_over_and".
idtac "Possible points: 3".
check_type @or_distributes_over_and (
(forall P Q R : Prop, P \/ Q /\ R <-> (P \/ Q) /\ (P \/ R))).
idtac "Assumptions:".
Abort.
Print Assumptions or_distributes_over_and.
Goal True.
idtac " ".

idtac "-------------------  negations  --------------------".
idtac " ".

idtac "#> double_neg".
idtac "Possible points: 1".
check_type @double_neg ((forall P : Prop, P -> ~ ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions double_neg.
Goal True.
idtac " ".

idtac "#> contradiction_implies_anything".
idtac "Possible points: 1".
check_type @contradiction_implies_anything ((forall P Q : Prop, P /\ ~ P -> Q)).
idtac "Assumptions:".
Abort.
Print Assumptions contradiction_implies_anything.
Goal True.
idtac " ".

idtac "#> de_morgan_not_or".
idtac "Possible points: 1".
check_type @de_morgan_not_or ((forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q)).
idtac "Assumptions:".
Abort.
Print Assumptions de_morgan_not_or.
Goal True.
idtac " ".

idtac "-------------------  currying  --------------------".
idtac " ".

idtac "#> curry".
idtac "Possible points: 1".
check_type @curry ((forall P Q R : Prop, (P /\ Q -> R) -> P -> Q -> R)).
idtac "Assumptions:".
Abort.
Print Assumptions curry.
Goal True.
idtac " ".

idtac "#> uncurry".
idtac "Possible points: 1".
check_type @uncurry ((forall P Q R : Prop, (P -> Q -> R) -> P /\ Q -> R)).
idtac "Assumptions:".
Abort.
Print Assumptions uncurry.
Goal True.
idtac " ".

idtac "-------------------  pe_implies_or_eq  --------------------".
idtac " ".

idtac "#> pe_implies_or_eq".
idtac "Advanced".
idtac "Possible points: 1".
check_type @pe_implies_or_eq (
(propositional_extensionality -> forall P Q : Prop, (P \/ Q) = (Q \/ P))).
idtac "Assumptions:".
Abort.
Print Assumptions pe_implies_or_eq.
Goal True.
idtac " ".

idtac "-------------------  pe_implies_true_eq  --------------------".
idtac " ".

idtac "#> pe_implies_true_eq".
idtac "Advanced".
idtac "Possible points: 1".
check_type @pe_implies_true_eq (
(propositional_extensionality -> forall P : Prop, P -> True = P)).
idtac "Assumptions:".
Abort.
Print Assumptions pe_implies_true_eq.
Goal True.
idtac " ".

idtac "-------------------  pe_implies_pi  --------------------".
idtac " ".

idtac "#> pe_implies_pi".
idtac "Advanced".
idtac "Possible points: 3".
check_type @pe_implies_pi ((propositional_extensionality -> proof_irrelevance)).
idtac "Assumptions:".
Abort.
Print Assumptions pe_implies_pi.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 82".
idtac "Max points - advanced: 105".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "plus_le".
idtac "le_trans".
idtac "le_plus_l".
idtac "add_le_cases".
idtac "Sn_le_Sm__n_le_m".
idtac "O_le_n".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- In_map_iff ---------".
Print Assumptions In_map_iff.
idtac "---------- In_app_iff ---------".
Print Assumptions In_app_iff.
idtac "---------- All_In ---------".
Print Assumptions All_In.
idtac "---------- even_double_conv ---------".
Print Assumptions even_double_conv.
idtac "---------- andb_true_iff ---------".
Print Assumptions andb_true_iff.
idtac "---------- orb_true_iff ---------".
Print Assumptions orb_true_iff.
idtac "---------- eqb_neq ---------".
Print Assumptions eqb_neq.
idtac "---------- eqb_list_true_iff ---------".
Print Assumptions eqb_list_true_iff.
idtac "---------- forallb_true_iff ---------".
Print Assumptions forallb_true_iff.
idtac "---------- tr_rev_correct ---------".
Print Assumptions tr_rev_correct.
idtac "---------- excluded_middle_irrefutable ---------".
Print Assumptions excluded_middle_irrefutable.
idtac "---------- ev_double ---------".
Print Assumptions ev_double.
idtac "---------- Perm3_ex1 ---------".
Print Assumptions Perm3_ex1.
idtac "---------- Perm3_refl ---------".
Print Assumptions Perm3_refl.
idtac "---------- le_inversion ---------".
Print Assumptions le_inversion.
idtac "---------- SSSSev__even ---------".
Print Assumptions SSSSev__even.
idtac "---------- ev5_nonsense ---------".
Print Assumptions ev5_nonsense.
idtac "---------- ev_sum ---------".
Print Assumptions ev_sum.
idtac "---------- Perm3_In ---------".
Print Assumptions Perm3_In.
idtac "---------- le_trans ---------".
Print Assumptions le_trans.
idtac "---------- O_le_n ---------".
Print Assumptions O_le_n.
idtac "---------- n_le_m__Sn_le_Sm ---------".
Print Assumptions n_le_m__Sn_le_Sm.
idtac "---------- Sn_le_Sm__n_le_m ---------".
Print Assumptions Sn_le_Sm__n_le_m.
idtac "---------- le_plus_l ---------".
Print Assumptions le_plus_l.
idtac "---------- plus_le ---------".
Print Assumptions plus_le.
idtac "---------- plus_le_cases ---------".
Print Assumptions plus_le_cases.
idtac "---------- plus_le_compat_l ---------".
Print Assumptions plus_le_compat_l.
idtac "---------- plus_le_compat_r ---------".
Print Assumptions plus_le_compat_r.
idtac "---------- le_plus_trans ---------".
Print Assumptions le_plus_trans.
idtac "---------- R_provability ---------".
idtac "MANUAL".
idtac "---------- reflect_iff ---------".
Print Assumptions reflect_iff.
idtac "---------- eqbP_practice ---------".
Print Assumptions eqbP_practice.
idtac "---------- nostutter ---------".
idtac "MANUAL".
idtac "---------- ev_8 ---------".
Print Assumptions ev_8.
idtac "---------- ev_8' ---------".
Print Assumptions ev_8'.
idtac "---------- Props.conj_fact ---------".
Print Assumptions Props.conj_fact.
idtac "---------- Props.or_commut' ---------".
Print Assumptions Props.or_commut'.
idtac "---------- Props.ex_ev_Sn ---------".
Print Assumptions Props.ex_ev_Sn.
idtac "---------- Props.ex_match ---------".
Print Assumptions Props.ex_match.
idtac "---------- Props.p_implies_true ---------".
Print Assumptions Props.p_implies_true.
idtac "---------- Props.ex_falso_quodlibet' ---------".
Print Assumptions Props.ex_falso_quodlibet'.
idtac "---------- EqualityPlayground.eq_cons ---------".
Print Assumptions EqualityPlayground.eq_cons.
idtac "---------- EqualityPlayground.equality__leibniz_equality ---------".
Print Assumptions EqualityPlayground.equality__leibniz_equality.
idtac "---------- EqualityPlayground.equality__leibniz_equality_term ---------".
Print Assumptions EqualityPlayground.equality__leibniz_equality_term.
idtac "---------- and_assoc ---------".
Print Assumptions and_assoc.
idtac "---------- or_distributes_over_and ---------".
Print Assumptions or_distributes_over_and.
idtac "---------- double_neg ---------".
Print Assumptions double_neg.
idtac "---------- contradiction_implies_anything ---------".
Print Assumptions contradiction_implies_anything.
idtac "---------- de_morgan_not_or ---------".
Print Assumptions de_morgan_not_or.
idtac "---------- curry ---------".
Print Assumptions curry.
idtac "---------- uncurry ---------".
Print Assumptions uncurry.
idtac "".
idtac "********** Advanced **********".
idtac "---------- not_exists_dist ---------".
Print Assumptions not_exists_dist.
idtac "---------- ev_ev__ev ---------".
Print Assumptions ev_ev__ev.
idtac "---------- subseq_refl ---------".
Print Assumptions subseq_refl.
idtac "---------- subseq_app ---------".
Print Assumptions subseq_app.
idtac "---------- subseq_trans ---------".
Print Assumptions subseq_trans.
idtac "---------- merge_filter ---------".
Print Assumptions merge_filter.
idtac "---------- pe_implies_or_eq ---------".
Print Assumptions pe_implies_or_eq.
idtac "---------- pe_implies_true_eq ---------".
Print Assumptions pe_implies_true_eq.
idtac "---------- pe_implies_pi ---------".
Print Assumptions pe_implies_pi.
Abort.

(* 2025-04-02 17:45 *)
