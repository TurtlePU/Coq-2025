Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From Lectures Require Import Lecture2.

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

From Lectures Require Import Lecture2.
Import Check.

Goal True.

idtac "-------------------  snd_fst_is_swap  --------------------".
idtac " ".

idtac "#> NatList.snd_fst_is_swap".
idtac "Possible points: 1".
check_type @NatList.snd_fst_is_swap (
(forall p : NatList.natprod,
 NatList.pair (NatList.snd p) (NatList.fst p) = NatList.swap_pair p)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.snd_fst_is_swap.
Goal True.
idtac " ".

idtac "-------------------  list_funs  --------------------".
idtac " ".

idtac "#> NatList.test_nonzeros".
idtac "Possible points: 0.5".
check_type @NatList.test_nonzeros (
(NatList.nonzeros
   (NatList.cons 0
      (NatList.cons 1
         (NatList.cons 0
            (NatList.cons 2
               (NatList.cons 3 (NatList.cons 0 (NatList.cons 0 NatList.nil))))))) =
 NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_nonzeros.
Goal True.
idtac " ".

idtac "#> NatList.test_oddmembers".
idtac "Possible points: 0.5".
check_type @NatList.test_oddmembers (
(NatList.oddmembers
   (NatList.cons 0
      (NatList.cons 1
         (NatList.cons 0
            (NatList.cons 2
               (NatList.cons 3 (NatList.cons 0 (NatList.cons 0 NatList.nil))))))) =
 NatList.cons 1 (NatList.cons 3 NatList.nil))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_oddmembers.
Goal True.
idtac " ".

idtac "#> NatList.test_countoddmembers2".
idtac "Possible points: 0.5".
check_type @NatList.test_countoddmembers2 (
(NatList.countoddmembers
   (NatList.cons 0 (NatList.cons 2 (NatList.cons 4 NatList.nil))) = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_countoddmembers2.
Goal True.
idtac " ".

idtac "#> NatList.test_countoddmembers3".
idtac "Possible points: 0.5".
check_type @NatList.test_countoddmembers3 ((NatList.countoddmembers NatList.nil = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_countoddmembers3.
Goal True.
idtac " ".

idtac "-------------------  alternate  --------------------".
idtac " ".

idtac "#> NatList.test_alternate1".
idtac "Advanced".
idtac "Possible points: 1".
check_type @NatList.test_alternate1 (
(NatList.alternate
   (NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))
   (NatList.cons 4 (NatList.cons 5 (NatList.cons 6 NatList.nil))) =
 NatList.cons 1
   (NatList.cons 4
      (NatList.cons 2
         (NatList.cons 5 (NatList.cons 3 (NatList.cons 6 NatList.nil))))))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate1.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate2".
idtac "Advanced".
idtac "Possible points: 1".
check_type @NatList.test_alternate2 (
(NatList.alternate (NatList.cons 1 NatList.nil)
   (NatList.cons 4 (NatList.cons 5 (NatList.cons 6 NatList.nil))) =
 NatList.cons 1
   (NatList.cons 4 (NatList.cons 5 (NatList.cons 6 NatList.nil))))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate2.
Goal True.
idtac " ".

idtac "#> NatList.test_alternate4".
idtac "Advanced".
idtac "Possible points: 1".
check_type @NatList.test_alternate4 (
(NatList.alternate NatList.nil
   (NatList.cons 20 (NatList.cons 30 NatList.nil)) =
 NatList.cons 20 (NatList.cons 30 NatList.nil))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_alternate4.
Goal True.
idtac " ".

idtac "-------------------  bag_functions  --------------------".
idtac " ".

idtac "#> NatList.test_count2".
idtac "Possible points: 0.5".
check_type @NatList.test_count2 (
(NatList.count 6
   (NatList.cons 1
      (NatList.cons 2
         (NatList.cons 3
            (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))))) =
 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_count2.
Goal True.
idtac " ".

idtac "#> NatList.test_sum1".
idtac "Possible points: 0.5".
check_type @NatList.test_sum1 (
(NatList.count 1
   (NatList.sum
      (NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil)))
      (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))) = 3)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_sum1.
Goal True.
idtac " ".

idtac "#> NatList.test_add1".
idtac "Possible points: 0.5".
check_type @NatList.test_add1 (
(NatList.count 1
   (NatList.add 1
      (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))) = 3)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_add1.
Goal True.
idtac " ".

idtac "#> NatList.test_add2".
idtac "Possible points: 0.5".
check_type @NatList.test_add2 (
(NatList.count 5
   (NatList.add 1
      (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil)))) = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_add2.
Goal True.
idtac " ".

idtac "#> NatList.test_member1".
idtac "Possible points: 0.5".
check_type @NatList.test_member1 (
(NatList.member 1
   (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil))) = true)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_member1.
Goal True.
idtac " ".

idtac "#> NatList.test_member2".
idtac "Possible points: 0.5".
check_type @NatList.test_member2 (
(NatList.member 2
   (NatList.cons 1 (NatList.cons 4 (NatList.cons 1 NatList.nil))) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_member2.
Goal True.
idtac " ".

idtac "-------------------  add_inc_count  --------------------".
idtac " ".

idtac "#> Manually graded: NatList.add_inc_count".
idtac "Possible points: 2".
print_manual_grade NatList.manual_grade_for_add_inc_count.
idtac " ".

idtac "-------------------  list_exercises  --------------------".
idtac " ".

idtac "#> NatList.app_nil_r".
idtac "Possible points: 0.5".
check_type @NatList.app_nil_r (
(forall l : NatList.natlist, NatList.app l NatList.nil = l)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.app_nil_r.
Goal True.
idtac " ".

idtac "#> NatList.rev_app_distr".
idtac "Possible points: 0.5".
check_type @NatList.rev_app_distr (
(forall l1 l2 : NatList.natlist,
 NatList.rev (NatList.app l1 l2) =
 NatList.app (NatList.rev l2) (NatList.rev l1))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.rev_app_distr.
Goal True.
idtac " ".

idtac "#> NatList.rev_involutive".
idtac "Possible points: 0.5".
check_type @NatList.rev_involutive (
(forall l : NatList.natlist, NatList.rev (NatList.rev l) = l)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.rev_involutive.
Goal True.
idtac " ".

idtac "#> NatList.app_assoc4".
idtac "Possible points: 0.5".
check_type @NatList.app_assoc4 (
(forall l1 l2 l3 l4 : NatList.natlist,
 NatList.app l1 (NatList.app l2 (NatList.app l3 l4)) =
 NatList.app (NatList.app (NatList.app l1 l2) l3) l4)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.app_assoc4.
Goal True.
idtac " ".

idtac "#> NatList.nonzeros_app".
idtac "Possible points: 1".
check_type @NatList.nonzeros_app (
(forall l1 l2 : NatList.natlist,
 NatList.nonzeros (NatList.app l1 l2) =
 NatList.app (NatList.nonzeros l1) (NatList.nonzeros l2))).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.nonzeros_app.
Goal True.
idtac " ".

idtac "-------------------  eqblist  --------------------".
idtac " ".

idtac "#> NatList.eqblist_refl".
idtac "Possible points: 2".
check_type @NatList.eqblist_refl (
(forall l : NatList.natlist, true = NatList.eqblist l l)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.eqblist_refl.
Goal True.
idtac " ".

idtac "-------------------  count_member_nonzero  --------------------".
idtac " ".

idtac "#> NatList.count_member_nonzero".
idtac "Possible points: 1".
check_type @NatList.count_member_nonzero (
(forall s : NatList.bag, (1 <=? NatList.count 1 (NatList.cons 1 s)) = true)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.count_member_nonzero.
Goal True.
idtac " ".

idtac "-------------------  remove_does_not_increase_count  --------------------".
idtac " ".

idtac "#> NatList.remove_does_not_increase_count".
idtac "Advanced".
idtac "Possible points: 3".
check_type @NatList.remove_does_not_increase_count (
(forall s : NatList.bag,
 (NatList.count 0 (NatList.remove_one 0 s) <=? NatList.count 0 s) = true)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.remove_does_not_increase_count.
Goal True.
idtac " ".

idtac "-------------------  involution_injective  --------------------".
idtac " ".

idtac "#> NatList.involution_injective".
idtac "Advanced".
idtac "Possible points: 3".
check_type @NatList.involution_injective (
(forall f : nat -> nat,
 (forall n : nat, n = f (f n)) -> forall n1 n2 : nat, f n1 = f n2 -> n1 = n2)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.involution_injective.
Goal True.
idtac " ".

idtac "-------------------  rev_injective  --------------------".
idtac " ".

idtac "#> NatList.rev_injective".
idtac "Advanced".
idtac "Possible points: 2".
check_type @NatList.rev_injective (
(forall l1 l2 : NatList.natlist, NatList.rev l1 = NatList.rev l2 -> l1 = l2)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.rev_injective.
Goal True.
idtac " ".

idtac "-------------------  hd_error  --------------------".
idtac " ".

idtac "#> NatList.test_hd_error1".
idtac "Possible points: 1".
check_type @NatList.test_hd_error1 ((NatList.hd_error NatList.nil = NatList.None)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_hd_error1.
Goal True.
idtac " ".

idtac "#> NatList.test_hd_error2".
idtac "Possible points: 1".
check_type @NatList.test_hd_error2 (
(NatList.hd_error (NatList.cons 1 NatList.nil) = NatList.Some 1)).
idtac "Assumptions:".
Abort.
Print Assumptions NatList.test_hd_error2.
Goal True.
idtac " ".

idtac "-------------------  eqb_id_refl  --------------------".
idtac " ".

idtac "#> eqb_id_refl".
idtac "Possible points: 1".
check_type @eqb_id_refl ((forall x : id, eqb_id x x = true)).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_id_refl.
Goal True.
idtac " ".

idtac "-------------------  update_eq  --------------------".
idtac " ".

idtac "#> PartialMap.update_eq".
idtac "Possible points: 1".
check_type @PartialMap.update_eq (
(forall (d : PartialMap.partial_map) (x : id) (v : nat),
 PartialMap.find x (PartialMap.update d x v) = NatList.Some v)).
idtac "Assumptions:".
Abort.
Print Assumptions PartialMap.update_eq.
Goal True.
idtac " ".

idtac "-------------------  update_neq  --------------------".
idtac " ".

idtac "#> PartialMap.update_neq".
idtac "Possible points: 1".
check_type @PartialMap.update_neq (
(forall (d : PartialMap.partial_map) (x y : id) (o : nat),
 eqb_id x y = false ->
 PartialMap.find x (PartialMap.update d y o) = PartialMap.find x d)).
idtac "Assumptions:".
Abort.
Print Assumptions PartialMap.update_neq.
Goal True.
idtac " ".

idtac "-------------------  poly_exercises  --------------------".
idtac " ".

idtac "#> app_nil_r".
idtac "Possible points: 0.5".
check_type @app_nil_r ((forall (X : Type) (l : list X), l ++ [ ] = l)).
idtac "Assumptions:".
Abort.
Print Assumptions app_nil_r.
Goal True.
idtac " ".

idtac "#> app_assoc".
idtac "Possible points: 1".
check_type @app_assoc ((forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n)).
idtac "Assumptions:".
Abort.
Print Assumptions app_assoc.
Goal True.
idtac " ".

idtac "#> app_length".
idtac "Possible points: 0.5".
check_type @app_length (
(forall (X : Type) (l1 l2 : list X),
 @length X (l1 ++ l2) = @length X l1 + @length X l2)).
idtac "Assumptions:".
Abort.
Print Assumptions app_length.
Goal True.
idtac " ".

idtac "-------------------  more_poly_exercises  --------------------".
idtac " ".

idtac "#> rev_app_distr".
idtac "Possible points: 1".
check_type @rev_app_distr (
(forall (X : Type) (l1 l2 : list X),
 @rev X (l1 ++ l2) = @rev X l2 ++ @rev X l1)).
idtac "Assumptions:".
Abort.
Print Assumptions rev_app_distr.
Goal True.
idtac " ".

idtac "#> rev_involutive".
idtac "Possible points: 1".
check_type @rev_involutive ((forall (X : Type) (l : list X), @rev X (@rev X l) = l)).
idtac "Assumptions:".
Abort.
Print Assumptions rev_involutive.
Goal True.
idtac " ".

idtac "-------------------  split  --------------------".
idtac " ".

idtac "#> split".
idtac "Possible points: 1".
check_type @split ((forall X Y : Type, list (X * Y) -> list X * list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions split.
Goal True.
idtac " ".

idtac "#> test_split".
idtac "Possible points: 1".
check_type @test_split (
(@split nat bool [(1, false); (2, false)] = ([1; 2], [false; false]))).
idtac "Assumptions:".
Abort.
Print Assumptions test_split.
Goal True.
idtac " ".

idtac "-------------------  filter_even_gt7  --------------------".
idtac " ".

idtac "#> test_filter_even_gt7_1".
idtac "Possible points: 1".
check_type @test_filter_even_gt7_1 (
(filter_even_gt7 [1; 2; 6; 9; 10; 3; 12; 8] = [10; 12; 8])).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_1.
Goal True.
idtac " ".

idtac "#> test_filter_even_gt7_2".
idtac "Possible points: 1".
check_type @test_filter_even_gt7_2 ((filter_even_gt7 [5; 2; 6; 19; 129] = [ ])).
idtac "Assumptions:".
Abort.
Print Assumptions test_filter_even_gt7_2.
Goal True.
idtac " ".

idtac "-------------------  partition  --------------------".
idtac " ".

idtac "#> partition".
idtac "Possible points: 1".
check_type @partition ((forall X : Type, (X -> bool) -> list X -> list X * list X)).
idtac "Assumptions:".
Abort.
Print Assumptions partition.
Goal True.
idtac " ".

idtac "#> test_partition1".
idtac "Possible points: 1".
check_type @test_partition1 ((@partition nat odd [1; 2; 3; 4; 5] = ([1; 3; 5], [2; 4]))).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition1.
Goal True.
idtac " ".

idtac "#> test_partition2".
idtac "Possible points: 1".
check_type @test_partition2 (
(@partition nat (fun _ : nat => false) [5; 9; 0] = ([ ], [5; 9; 0]))).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition2.
Goal True.
idtac " ".

idtac "-------------------  map_rev  --------------------".
idtac " ".

idtac "#> map_rev".
idtac "Possible points: 3".
check_type @map_rev (
(forall (X Y : Type) (f : X -> Y) (l : list X),
 @map X Y f (@rev X l) = @rev Y (@map X Y f l))).
idtac "Assumptions:".
Abort.
Print Assumptions map_rev.
Goal True.
idtac " ".

idtac "-------------------  flat_map  --------------------".
idtac " ".

idtac "#> flat_map".
idtac "Possible points: 1".
check_type @flat_map ((forall X Y : Type, (X -> list Y) -> list X -> list Y)).
idtac "Assumptions:".
Abort.
Print Assumptions flat_map.
Goal True.
idtac " ".

idtac "#> test_flat_map1".
idtac "Possible points: 1".
check_type @test_flat_map1 (
(@flat_map nat nat (fun n : nat => [n; n; n]) [1; 5; 4] =
 [1; 1; 1; 5; 5; 5; 4; 4; 4])).
idtac "Assumptions:".
Abort.
Print Assumptions test_flat_map1.
Goal True.
idtac " ".

idtac "-------------------  fold_length  --------------------".
idtac " ".

idtac "#> Exercises.fold_length_correct".
idtac "Possible points: 2".
check_type @Exercises.fold_length_correct (
(forall (X : Type) (l : list X), @Exercises.fold_length X l = @length X l)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.fold_length_correct.
Goal True.
idtac " ".

idtac "-------------------  fold_map  --------------------".
idtac " ".

idtac "#> Manually graded: Exercises.fold_map".
idtac "Possible points: 3".
print_manual_grade Exercises.manual_grade_for_fold_map.
idtac " ".

idtac "-------------------  currying  --------------------".
idtac " ".

idtac "#> Exercises.uncurry_curry".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.uncurry_curry (
(forall (X Y Z : Type) (f : X -> Y -> Z) (x : X) (y : Y),
 @Exercises.prod_curry X Y Z (@Exercises.prod_uncurry X Y Z f) x y = f x y)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.uncurry_curry.
Goal True.
idtac " ".

idtac "#> Exercises.curry_uncurry".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.curry_uncurry (
(forall (X Y Z : Type) (f : X * Y -> Z) (p : X * Y),
 @Exercises.prod_uncurry X Y Z (@Exercises.prod_curry X Y Z f) p = f p)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.curry_uncurry.
Goal True.
idtac " ".

idtac "-------------------  nth_error_informal  --------------------".
idtac " ".

idtac "#> Manually graded: Exercises.informal_proof".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade Exercises.manual_grade_for_informal_proof.
idtac " ".

idtac "-------------------  church_scc  --------------------".
idtac " ".

idtac "#> Exercises.Church.scc_2".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.scc_2 (
(Exercises.Church.scc Exercises.Church.one = Exercises.Church.two)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.scc_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.scc_3".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.scc_3 (
(Exercises.Church.scc Exercises.Church.two = Exercises.Church.three)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.scc_3.
Goal True.
idtac " ".

idtac "-------------------  church_plus  --------------------".
idtac " ".

idtac "#> Exercises.Church.plus_1".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.plus_1 (
(Exercises.Church.plus Exercises.Church.zero Exercises.Church.one =
 Exercises.Church.one)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.plus_1.
Goal True.
idtac " ".

idtac "#> Exercises.Church.plus_2".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.plus_2 (
(Exercises.Church.plus Exercises.Church.two Exercises.Church.three =
 Exercises.Church.plus Exercises.Church.three Exercises.Church.two)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.plus_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.plus_3".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.plus_3 (
(Exercises.Church.plus
   (Exercises.Church.plus Exercises.Church.two Exercises.Church.two)
   Exercises.Church.three =
 Exercises.Church.plus Exercises.Church.one
   (Exercises.Church.plus Exercises.Church.three Exercises.Church.three))).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.plus_3.
Goal True.
idtac " ".

idtac "-------------------  church_mult  --------------------".
idtac " ".

idtac "#> Exercises.Church.mult_1".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.mult_1 (
(Exercises.Church.mult Exercises.Church.one Exercises.Church.one =
 Exercises.Church.one)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.mult_1.
Goal True.
idtac " ".

idtac "#> Exercises.Church.mult_2".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.mult_2 (
(Exercises.Church.mult Exercises.Church.zero
   (Exercises.Church.plus Exercises.Church.three Exercises.Church.three) =
 Exercises.Church.zero)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.mult_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.mult_3".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.mult_3 (
(Exercises.Church.mult Exercises.Church.two Exercises.Church.three =
 Exercises.Church.plus Exercises.Church.three Exercises.Church.three)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.mult_3.
Goal True.
idtac " ".

idtac "-------------------  church_exp  --------------------".
idtac " ".

idtac "#> Exercises.Church.exp_1".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.exp_1 (
(Exercises.Church.exp Exercises.Church.two Exercises.Church.two =
 Exercises.Church.plus Exercises.Church.two Exercises.Church.two)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.exp_1.
Goal True.
idtac " ".

idtac "#> Exercises.Church.exp_2".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.exp_2 (
(Exercises.Church.exp Exercises.Church.three Exercises.Church.zero =
 Exercises.Church.one)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.exp_2.
Goal True.
idtac " ".

idtac "#> Exercises.Church.exp_3".
idtac "Advanced".
idtac "Possible points: 1".
check_type @Exercises.Church.exp_3 (
(Exercises.Church.exp Exercises.Church.three Exercises.Church.two =
 Exercises.Church.plus
   (Exercises.Church.mult Exercises.Church.two
      (Exercises.Church.mult Exercises.Church.two Exercises.Church.two))
   Exercises.Church.one)).
idtac "Assumptions:".
Abort.
Print Assumptions Exercises.Church.exp_3.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 40".
idtac "Max points - advanced: 66".
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
idtac "---------- NatList.snd_fst_is_swap ---------".
Print Assumptions NatList.snd_fst_is_swap.
idtac "---------- NatList.test_nonzeros ---------".
Print Assumptions NatList.test_nonzeros.
idtac "---------- NatList.test_oddmembers ---------".
Print Assumptions NatList.test_oddmembers.
idtac "---------- NatList.test_countoddmembers2 ---------".
Print Assumptions NatList.test_countoddmembers2.
idtac "---------- NatList.test_countoddmembers3 ---------".
Print Assumptions NatList.test_countoddmembers3.
idtac "---------- NatList.test_count2 ---------".
Print Assumptions NatList.test_count2.
idtac "---------- NatList.test_sum1 ---------".
Print Assumptions NatList.test_sum1.
idtac "---------- NatList.test_add1 ---------".
Print Assumptions NatList.test_add1.
idtac "---------- NatList.test_add2 ---------".
Print Assumptions NatList.test_add2.
idtac "---------- NatList.test_member1 ---------".
Print Assumptions NatList.test_member1.
idtac "---------- NatList.test_member2 ---------".
Print Assumptions NatList.test_member2.
idtac "---------- add_inc_count ---------".
idtac "MANUAL".
idtac "---------- NatList.app_nil_r ---------".
Print Assumptions NatList.app_nil_r.
idtac "---------- NatList.rev_app_distr ---------".
Print Assumptions NatList.rev_app_distr.
idtac "---------- NatList.rev_involutive ---------".
Print Assumptions NatList.rev_involutive.
idtac "---------- NatList.app_assoc4 ---------".
Print Assumptions NatList.app_assoc4.
idtac "---------- NatList.nonzeros_app ---------".
Print Assumptions NatList.nonzeros_app.
idtac "---------- NatList.eqblist_refl ---------".
Print Assumptions NatList.eqblist_refl.
idtac "---------- NatList.count_member_nonzero ---------".
Print Assumptions NatList.count_member_nonzero.
idtac "---------- NatList.test_hd_error1 ---------".
Print Assumptions NatList.test_hd_error1.
idtac "---------- NatList.test_hd_error2 ---------".
Print Assumptions NatList.test_hd_error2.
idtac "---------- eqb_id_refl ---------".
Print Assumptions eqb_id_refl.
idtac "---------- PartialMap.update_eq ---------".
Print Assumptions PartialMap.update_eq.
idtac "---------- PartialMap.update_neq ---------".
Print Assumptions PartialMap.update_neq.
idtac "---------- app_nil_r ---------".
Print Assumptions app_nil_r.
idtac "---------- app_assoc ---------".
Print Assumptions app_assoc.
idtac "---------- app_length ---------".
Print Assumptions app_length.
idtac "---------- rev_app_distr ---------".
Print Assumptions rev_app_distr.
idtac "---------- rev_involutive ---------".
Print Assumptions rev_involutive.
idtac "---------- split ---------".
Print Assumptions split.
idtac "---------- test_split ---------".
Print Assumptions test_split.
idtac "---------- test_filter_even_gt7_1 ---------".
Print Assumptions test_filter_even_gt7_1.
idtac "---------- test_filter_even_gt7_2 ---------".
Print Assumptions test_filter_even_gt7_2.
idtac "---------- partition ---------".
Print Assumptions partition.
idtac "---------- test_partition1 ---------".
Print Assumptions test_partition1.
idtac "---------- test_partition2 ---------".
Print Assumptions test_partition2.
idtac "---------- map_rev ---------".
Print Assumptions map_rev.
idtac "---------- flat_map ---------".
Print Assumptions flat_map.
idtac "---------- test_flat_map1 ---------".
Print Assumptions test_flat_map1.
idtac "---------- Exercises.fold_length_correct ---------".
Print Assumptions Exercises.fold_length_correct.
idtac "---------- fold_map ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- NatList.test_alternate1 ---------".
Print Assumptions NatList.test_alternate1.
idtac "---------- NatList.test_alternate2 ---------".
Print Assumptions NatList.test_alternate2.
idtac "---------- NatList.test_alternate4 ---------".
Print Assumptions NatList.test_alternate4.
idtac "---------- NatList.remove_does_not_increase_count ---------".
Print Assumptions NatList.remove_does_not_increase_count.
idtac "---------- NatList.involution_injective ---------".
Print Assumptions NatList.involution_injective.
idtac "---------- NatList.rev_injective ---------".
Print Assumptions NatList.rev_injective.
idtac "---------- Exercises.uncurry_curry ---------".
Print Assumptions Exercises.uncurry_curry.
idtac "---------- Exercises.curry_uncurry ---------".
Print Assumptions Exercises.curry_uncurry.
idtac "---------- informal_proof ---------".
idtac "MANUAL".
idtac "---------- Exercises.Church.scc_2 ---------".
Print Assumptions Exercises.Church.scc_2.
idtac "---------- Exercises.Church.scc_3 ---------".
Print Assumptions Exercises.Church.scc_3.
idtac "---------- Exercises.Church.plus_1 ---------".
Print Assumptions Exercises.Church.plus_1.
idtac "---------- Exercises.Church.plus_2 ---------".
Print Assumptions Exercises.Church.plus_2.
idtac "---------- Exercises.Church.plus_3 ---------".
Print Assumptions Exercises.Church.plus_3.
idtac "---------- Exercises.Church.mult_1 ---------".
Print Assumptions Exercises.Church.mult_1.
idtac "---------- Exercises.Church.mult_2 ---------".
Print Assumptions Exercises.Church.mult_2.
idtac "---------- Exercises.Church.mult_3 ---------".
Print Assumptions Exercises.Church.mult_3.
idtac "---------- Exercises.Church.exp_1 ---------".
Print Assumptions Exercises.Church.exp_1.
idtac "---------- Exercises.Church.exp_2 ---------".
Print Assumptions Exercises.Church.exp_2.
idtac "---------- Exercises.Church.exp_3 ---------".
Print Assumptions Exercises.Church.exp_3.
Abort.

(* 2025-03-19 13:21 *)
