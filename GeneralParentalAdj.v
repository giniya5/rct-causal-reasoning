From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
Require Import Reals.
From infotheo.probability Require Import proba fdist. (* fsdist jfdist_cond. *)
Require Import List.
Import ListNotations.
From mathcomp Require Import reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require Import unstable mathcomp_extra reals exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import Classical.
Require Import Field.
Require Import Lia.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section ParentalAdjustmentFormula.

Context {R : realType}.
Variables (U : finType).
    (* Set of all unobserved terms -- tuple *)
Variables (outcomesH : finType).
    (* Outcomes of node H *)
Variables (outcomesT : finType).
    (* Outcomes of node T *)
Variables (outcomesPaT : finType).
    (* Outcomes of nodes parents(T) -- tuple *)
Variables (outcomesZ : finType).
    (* Outcomes of nodes Z, those used for backdoor 
        criterion -- tuple *)
Variables (outcomesE : finType).
    (* Outcomes of node E, which is all nodes in the graph 
      except for T, H, paT -- tuple *)
Variable P : R.-fdist (U).

Variable H : {RV P -> outcomesH}.
    (* Variable being measured *)
Variable T : {RV P -> outcomesT}.
    (* Variable being intervened/conditioned on *)
Variable paT : {RV P -> outcomesPaT}.
    (* Set of parents of variable T *)
Variable Z : {RV P -> outcomesZ}.
    (* Set Z that satisfies the backdoor criterion with T->H.
      Note that Z overlaps with E and paT. *)
Variable E : {RV P -> outcomesE}.
    (* Set E, which is all variables in the graph except for 
      T, H and paT. *)
(* Realtionships in the graph:
    paT_i -> T, T -> H, H ... Z_i ... -> T *)

(* All of the node functions under intervention. Take a value
  of type outcomesT, the interventional value of T=t, and
  output a RV. (Tinterv is defined but did not end up getting 
  used, and would be 1 if T=t, 0 if T!=t. So could be 
  explicitly defined instead of just being a variable.)*)
Variable Hinterv : outcomesT -> {RV P -> outcomesH}.
Variable Tinterv : outcomesT -> {RV P -> outcomesT}.
Variable paTinterv : outcomesT -> {RV P -> outcomesPaT}.
Variable Zinterv : outcomesT -> {RV P -> outcomesZ}.
Variable Einterv : outcomesT -> {RV P -> outcomesE}.

(* Let Tinterv (t: outcomesT) : {RV P -> outcomesT} :=
  fun t => 
  match t  *)


(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                        SECTION : MATH LEMMAS 
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

Lemma mult_both_sides_r: forall (a b c : R),
  a = b ->
  a * c = b * c.
Proof.
  intros.
  (* eapply eqr_divrMr. *)
Admitted.

Lemma mult_both_sides_l: forall (a b c : R),
  a = b ->
  c * a = c * b.
Proof.
Admitted.

Lemma mult_div: forall (a b: R),
  b != 0 ->
  a * b / b = a.
Proof.
  intros.
  apply esym.
  rewrite <- GRing.mulrA.
  rewrite GRing.mulfV.
  rewrite GRing.mulr1.
  reflexivity.
  assumption.
Qed.

Lemma div_mult: forall (a b: R),
  b != 0 ->
  a / b * b = a.
Proof.
  intros.
  apply esym.
  eapply eqr_divrMr.
  assumption.
  reflexivity.
Qed.

Lemma mult_in_middle: forall (a b c : R),
  b != 0 ->
  a / b * ( b / c ) = a / c.
Proof.
  move=> a b c hb.
  Check GRing.mulrA.
  rewrite GRing.mulrA.
  rewrite GRing.divfK.
  reflexivity.
  assumption.
Qed.

Lemma mult_zero_right: forall (a : R),
  a * 0 = 0.
Proof.
  intros.
  rewrite GRing.mulr0.
  reflexivity.
Qed.

Lemma mult_zero_left: forall (a : R),
  0 * a = 0.
Proof.
  intros.
  rewrite GRing.mul0r.
  reflexivity.
Qed.

Lemma div_div: forall (a b c : R),
  b != 0 ->
  c != 0 -> 
  a / (b / c) = a / b * c.
Proof.
  intros.
  (* rewrite GRing.divrA. *)
Admitted.

Lemma div_both_sides: forall (a b c : R),
  c != 0 ->
  a = b ->
  a / c = b / c.
Proof.
  intros.
  Check GRing.mulfV.
Admitted.

Lemma zero_div_zero: forall (a : R),
  a != 0 ->
  0 / a = 0.
Proof.
Admitted.

Lemma false_cant_be:
  (0 : R) != 0 ->
  ~~true.
Proof.
Admitted.

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                  SECTION : SIMPLE PROBABILITY LEMMAS 
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

Lemma cpr_eq0_denom: forall {TA TD: finType}
  (X : {RV P -> TA}) (Y: {RV P -> TD}) a b,
  `Pr[Y = b] = 0 ->
  `Pr[X = a | Y = b] = 0.
Proof.
  intros.
  rewrite cPr_eq_finType.
  apply cPr_eq0P.
  rewrite setIC. 
  apply Pr_domin_setI.
  rewrite <- cpr_eq_unit_RV in H0.
  rewrite cPr_eq_finType in H0.
  apply cPr_eq0P in H0.
  assert (Y @^-1: [set b] :&: unit_RV P @^-1: [set tt] = Y @^-1: [set b]).
    simpl.
    apply/setP => u.
    rewrite !inE.
    destruct (Y u == b).
    simpl.
    unfold unit_RV.
    rewrite eq_refl.
    reflexivity.
    simpl.
    reflexivity.
  rewrite <- H0.
  rewrite H1.
  reflexivity.
Qed.

Lemma rearrange_cond: forall {A B C : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) w x y,
  `Pr[ W = w | [% X, Y] = (x, y)] = `Pr[ W = w | [% Y, X] = (y, x)].
Proof.
  intros.
  rewrite !cpr_eqE.
  rewrite -> pfwd1_pairC with (TY := X) (TX := Y).
  unfold swap.
  simpl.
  rewrite pfwd1_pairA.
  rewrite pfwd1_pairAC.
  rewrite <- pfwd1_pairA.
  reflexivity.
Qed.

Lemma pair_to_single_non_zero: forall {A B : finType} (X : {RV P -> A}) 
  (Y : {RV P -> B}) x y,
  `Pr[ [% X, Y] = (x, y) ] != 0 ->
  `Pr[ X = x ] != 0.
Proof.
  intros.
  Check pfwd1_domin_RV2.
  have [Hzero | Hnonzero] := boolP (`Pr[X = x] == 0).
  move/eqP: Hzero => Hzero.
  apply pfwd1_domin_RV2 with (TX := X) (TY := Y) (b := y) in Hzero.
  rewrite Hzero in H0.

  exfalso.
  (* apply H0.
  reflexivity.

  Search ( _ != _ ).
  rewrite <- contra.Internals.eqType_neqP in H0. *)
  admit.

  exact is_true_true.
Admitted.

Lemma indep_to_equality: forall {A B C : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) x y w,
  X _|_ Y | W ->
  `Pr[ [% Y, W] = (y, w) ] != 0 ->
  `Pr[ X=x | W=w ] = `Pr[ X=x | [% W, Y] = (w,y)]. 
Proof.
  intros.
  rewrite rearrange_cond.
  rewrite cinde_alt.
  reflexivity.
  assumption.
  assumption.
Qed.

(* Needed for infotheo libaray's total_prob and total_prob_cond lemmas *)
Lemma disjoint_true: forall {C: finType} (W : {RV (P) -> C}), 
  (forall i j : C,
  i != j ->
  [disjoint finset (T:=U) (preim W (pred1 i)) & finset (T:=U) (preim W (pred1 j))]).
Proof.
  intros.
  (* Check setI_eq0. *)
  rewrite <- setI_eq0.
  rewrite eqEsubset.
  rewrite sub0set.
  (* Search ( _ && true). *)
  rewrite Bool.andb_true_r.
  apply/subsetP => y.
  rewrite in_set0.
  rewrite inE.
  rewrite !in_set.
  simpl.
  intros.
  move/andP in H1.
  inversion H1.
  move/eqP in H2.
  move/eqP in H3.
  rewrite <- H2 in H0.
  rewrite <- H3 in H0.
  rewrite eqxx in H0.
  exact H0.
Qed.

(* Needed for infotheo libaray's total_prob and total_prob_cond lemmas *)
Lemma cover_true: forall {C: finType} (W : {RV (P) -> C}),
  cover [set finset (T:=U) (preim W (pred1 i)) | i : C] = [set: U].
Proof.
  intros.
  apply/setP=> y. 
  rewrite inE.
  apply/bigcupP.
  exists ((finset (T:=U) (preim W (pred1 (W y))))).
  apply/imsetP.
  exists (W y).
  rewrite inE.
  reflexivity.
  reflexivity.
  
  rewrite inE.
  rewrite /=.
  apply eqxx.
Qed.

Lemma total_prob': forall {A C : finType} (X : {RV P -> A})
  (W : {RV P -> C}) x,
  `Pr[ X = x ] = \sum_(u in C) `Pr[ [% X, W] = (x, u) ].
Proof.
  intros.
  Check total_prob.
  rewrite pfwd1E.
  rewrite -> total_prob with (I := C)
      (F := (fun i => (finset (T:=U) (preim W (pred1 i))))).
  apply eq_bigr => u _.
  unfold RV2.
  rewrite pfwd1E.
  assert ((finset (T:=U) (preim X (pred1 x)) :&: finset (T:=U) (preim W (pred1 u))) = 
      (finset (T:=U) (preim (fun x0 : U => (X x0, W x0)) (pred1 (x, u))))).
    apply/setP => t.
    rewrite !inE.
    apply xpair_eqE.
  rewrite H0.
  reflexivity.

  apply disjoint_true.
  apply cover_true.
Qed.

Lemma marginalize: forall {A C : finType} (X : {RV P -> A})
  (W : {RV P -> C}) x,
  `Pr[ X = x ] = \sum_(u in C) 
      `Pr[ X = x | W = u ] * `Pr[ W = u ].
Proof.
  intros.
  (* Check total_prob_cond. *)
  rewrite pfwd1E.
  rewrite -> total_prob_cond with (I := C) 
      (F := (fun i => (finset (T:=U) (preim W (pred1 i))))).
  apply eq_bigr => u _.
  rewrite <- pfwd1E.
  rewrite <- cPr_eq_def.
  reflexivity.
  apply disjoint_true.
  apply cover_true.
Qed.

Lemma marginalize_cond: forall {A B C : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) x y,
  `Pr[ X=x | Y=y ] = \sum_(u in C) 
      `Pr[ X=x | [% Y, W] = (y, u) ] * `Pr[ W=u | Y = y ].
Proof.
  intros.

  have [Hzero | Hnonzero] := boolP (`Pr[Y = y] == 0).
    move/eqP: Hzero => Hzero.
    rewrite !cpr_eq0_denom; try assumption.
    under eq_bigr => u _.
      rewrite !cpr_eq0_denom; try assumption; cycle 1.
      apply pfwd1_domin_RV2.
      assumption.
      rewrite mult_zero_right.
      over.
    simpl.
    rewrite big1; intros; reflexivity.

  rewrite cpr_eqE.

  assert (\sum_(u in C) `Pr[ X = x | [% Y, W] = (y, u) ] * `Pr[ W = u | Y = y ]
        = \sum_(u in C) `Pr[ [% X, [% Y, W]] = (x, (y, u)) ] / `Pr[ Y = y ]).
    apply eq_bigr => u _.
    case: (boolP (`Pr[ [% W, Y] = (u, y) ] == 0)).
      intros.
      move /eqP in p.
      rewrite pfwd1_pairC in p. unfold swap in p. simpl in p.
      rewrite -> cpr_eq0_denom with (Y := [% Y, W]); try assumption.
      rewrite mult_zero_left.
      rewrite -> pfwd1_domin_RV1 with (TX := X) (a := x); try assumption.
      rewrite zero_div_zero; try assumption.
      reflexivity.

    intros.
    rewrite !cpr_eqE.
    rewrite -> pfwd1_pairC with (TY := Y) (TX := W).
    unfold swap.
    simpl.
    rewrite mult_in_middle; try assumption.
    reflexivity.

  rewrite H0.

  (* under eq_bigr => u _.
    case: (boolP (`Pr[ [% W, Y] = (u, y) ] == 0)).
      intros.
      move /eqP in p.
      rewrite -> cpr_eq0_denom with (Y := [% Y, W]).
      rewrite mult_zero_left.
      pose proof (zero_div_zero `Pr[ Y = y ] Hnonzero).
      assert (0 = `Pr[ [% X, [% Y, W]] = (x, (y, u))] / `Pr[ Y = y ]). admit.
      (* rewrite <- H1. *)
      admit.
      rewrite pfwd1_pairC.
      assumption.

      intros.
    (* have [Hz | Hnz] := boolP (`Pr[[% Y, W] = (y, u) ] == 0).
    move/eqP: Hz => Hz.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_zero_right.
    over.
    admit. *)
      rewrite !cpr_eqE.
      rewrite -> pfwd1_pairC with (TY := Y) (TX := W).
      unfold swap.
      simpl.
      rewrite mult_in_middle; try assumption.
      over.
  (* Check big_enum. *)
  simpl. *)
  rewrite <- big_enum with (A := C) (F := (fun u => `Pr[ [% X, [% Y, W]] = (x, (y, u)) ] / `Pr[ Y = y ])).
  simpl.
  (* Check big_distrl. *)
  rewrite <- big_distrl with (r := enum C)
      (F := (fun u => `Pr[ [% X, [% Y, W]] = (x, (y, u)) ])).
  simpl.
  rewrite big_enum.
  simpl.
  rewrite eqr_divrMr; try assumption.
  rewrite div_mult; try assumption.
  rewrite -> total_prob' with (X := ([% X, Y])) (W := W).
  apply eq_bigr => w _.
  rewrite pfwd1_pairA.
  reflexivity.
Qed.

Lemma rearrange_brackets: forall {A B C D : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}) v w x y,
  `Pr[ W = w | [% X, [% Y, V]] = (x, (y, v))] = 
      `Pr[ W = w | [% [%X, Y], V] = ((x, y), v)].
Proof.
  intros.

  case: (boolP (`Pr[ [% X, Y, V] = (x, y, v) ] == 0)).
    intros.
    move /eqP in p.
    rewrite cpr_eq0_denom.
    rewrite cpr_eq0_denom.
    reflexivity.
    exact p.
    rewrite pfwd1_pairA.
    exact p.

  intros.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite pfwd1_pairA.
  apply div_both_sides; try assumption.
  rewrite pfwd1_pairA.
  rewrite pfwd1_pairA.
  
  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a0 == x).
    case Hv : (V a0 == v).
      case Hy : (Y a0 == y).
        case Hw : (W a0 == w).
        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        rewrite !andbF.
        reflexivity.

        simpl.
        rewrite !andbF.
        reflexivity.

        simpl.
        rewrite !andbF.
        reflexivity.
Qed.

Lemma pair_to_single_non_zero_right: forall {A B : finType} 
  (X : {RV P -> A}) (Y : {RV P -> B}) x y,
  `Pr[ [% X, Y] = (x, y) ] != 0 ->
  `Pr[ Y = y ] != 0.
Proof.
  intros.
  have [Hzero | Hnonzero] := boolP (`Pr[Y = y] == 0).
    move/eqP: Hzero => Hz'.
    rewrite pfwd1_domin_RV1 in H0.
      apply false_cant_be; assumption.
      assumption.
    
    exact is_true_true.
Qed.

Lemma pair_to_single_non_zero_left: forall {A B : finType} 
  (X : {RV P -> A}) (Y : {RV P -> B}) x y,
  `Pr[ [% X, Y] = (x, y) ] != 0 ->
  `Pr[ X = x ] != 0.
Proof.
  intros.
  rewrite pfwd1_pairC in H0.
  unfold swap in H0. simpl in H0.
  eapply pair_to_single_non_zero_right.
  exact H0.
Qed.

Lemma pfwd1_pairA_cond: forall {TA TB TC TD : finType} {TX : {RV P -> TA}} 
  {TY : {RV P -> TB}} {TZ : {RV P -> TC}} {TW : {RV P -> TD}} {a b c d},
  `Pr[ [% TX, [% TY, TZ]] = (a, (b, c)) | TW = d ] =
  `Pr[ [% TX, TY, TZ] = (a, b, c) | TW = d].
Proof.
  intros.
  case: (boolP (`Pr[ TW = d ] == 0)).
    intros.
    move /eqP in p.
    rewrite cpr_eq0_denom.
    rewrite cpr_eq0_denom.
    reflexivity.
    exact p.
    exact p.

  intros.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  apply div_both_sides; try assumption.
  
  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (TX a0 == a).
    case Hv : (TY a0 == b).
      case Hy : (TZ a0 == c).
        case Hw : (TW a0 == d).
        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        reflexivity.
Qed.

Lemma remove_redundant_cond_term: forall  {A B D : finType} 
  (X : {RV P -> A}) (Y : {RV P -> B}) (V : {RV P -> D}) x y v,
  `Pr[ [% X, V] = (x, v) | [% Y, V] = (y, v)]
  = `Pr[ X = x | [% Y, V] = (y, v)].
Proof.
  intros.
  destruct (classic (`Pr[ [% Y, V] = (y, v) ] == 0)).
    move /eqP in H0.
    rewrite cpr_eq0_denom; try assumption.
    rewrite cpr_eq0_denom; try assumption.
    reflexivity.

  rewrite cpr_eqE.
  rewrite cpr_eqE.
  apply div_both_sides with (c := `Pr[ [% Y, V] = (y, v) ]); try assumption.
    apply /negP.
    assumption.
  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a0 == x).
    case Hv : (V a0 == v).
      case Hy : (Y a0 == y).
        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        rewrite andbF.
        reflexivity.

        simpl.
        reflexivity.
Qed.

Lemma cond_term_makes_impossible: forall  {A B D : finType} 
  (X : {RV P -> A}) (Y : {RV P -> B}) (V : {RV P -> D}) x y v1 v2,
  v1 != v2 ->
  `Pr[ [% X, V] = (x, v1) | [% Y, V] = (y, v2)] = 0.
Proof.
  intros.
  destruct (classic (`Pr[ [% Y, V] = (y, v2) ] == 0)).
    move /eqP in H1.
    rewrite cpr_eq0_denom; try assumption. 
    reflexivity.

  rewrite cpr_eqE.
  assert (`Pr[ [% X, V, [% Y, V]] = (x, v1, (y, v2)) ] = 0).
  rewrite pfwd1E.
  rewrite /Pr.
  under eq_bigl => a.

  (* rewrite cpr_eqE. *)
  (* apply div_both_sides with (c := `Pr[ [% Y, V] = (y, v) ]); try assumption.
    apply /negP.
    assumption. *)
  (* rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a. *)
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hv1 : (V a == v1).
    assert ((V a == v2) = false).
      by rewrite (eqP Hv1); exact/negbTE.
    rewrite H2.
    rewrite andbF.
    rewrite andbF.
    over.
    
    rewrite andbF.
    simpl.
    over.
  
    simpl.
    apply big_pred0_eq.
  
  rewrite H2.
  apply zero_div_zero.
  apply /negP.
  assumption.
Qed.

Lemma adding_conditional_to_indep: forall  {A B C D : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}),
  X _|_ Y | [% W, V] ->
  X _|_ [% Y, V] | [% W, V].
Proof.
  intros.
  unfold cinde_RV in H0.
  unfold cinde_RV.
  intros.
  destruct b as [y z1].
  specialize (H0 a y c).
  destruct c as [w z2].
  rewrite cpr_eq_pairA.
  destruct (classic (z1 == z2)).
    move /eqP in H1.
    inversion H1.
  rewrite remove_redundant_cond_term.
  (* rewrite -> remove_redundant_cond_term with (X := [% X, Y]) (V := V) (Y := W). *)
  rewrite remove_redundant_cond_term.
  assumption.

  (* move /eqP in H1. *)
  (* move /eqP in H1. *)
  rewrite cond_term_makes_impossible.
  rewrite cond_term_makes_impossible.
  rewrite mult_zero_right.
  reflexivity.
  all: apply /negP; assumption.
Qed.

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                SECTION : Parental Adjustment Formula ->
                    Backdoor Adjustment Formula
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

Lemma pair_to_single_non_zero_specialized: 
  (forall (i0 : outcomesPaT) (i1 : outcomesZ) (i2 : outcomesT), 
      `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) ->
  (exists z, z \in outcomesZ) ->
  (forall (i0 : outcomesPaT) (i1 : outcomesT),
      `Pr[ [% T, paT] = (i1, i0) ] != 0).
Proof.
  (* move=> H0 i0 i1.
  have Hz : inhabited outcomesZ by exact: (inhabits_fin _).
  destruct Hz as [z].
  have H0 := H i0 z i1.
  (* H0 : Pr[ [% paT, [% T, Z]] = (i0, (i1, z)) ] != 0 *)
  apply: (pair_to_single_non_zero_right paT [% T, Z] i0 (i1, z)) in H0.
  (* H0 : Pr[ [% T, Z] = (i1, z) ] != 0 *)
  exact: (pair_to_single_non_zero_left T Z i1 z H0). *)

  intros.
  specialize (H0 i0).
  Check pfwd1_neq0.
  (* destruct (classic (exists z, z \in outcomesZ)). *)
  destruct H1 as [z].
  specialize (H0 z i1).
  rewrite pfwd1_pairA in H0.
  rewrite pfwd1_pairC.
  unfold swap.
  simpl.
  pose proof (pair_to_single_non_zero_left [% paT, T] Z (i0, i1) z H0).
  assumption.

  (* apply pair_to_single_non_zero_left in H0. *)
  (* Check pfwd1_pairA. *)
  (* apply pair_to_single_non_zero_right in H0.
  apply pair_to_single_non_zero_right with (X := Z)  *)
  (* specialize (H0 i0 i1).
  Check pfwd1_domin_RV2. *)
Qed.

Lemma cond_to_pair_non_zero: forall t u,
  `Pr[ T = t | paT = u ] != 0 ->
  `Pr[ [% T, paT] = (t, u) ] != 0.
Proof.
Admitted.

Lemma oddly_specific: forall t u z h,
  `Pr[ T=t | paT=u ] != 0 ->
  `Pr[ [% paT, [% T, Z]] = (u, (t, z)) ] = 0 ->
  `Pr[ H = h | [% T, Z] = (t, z) ] * `Pr[ Z = z | [% paT, T] = (u, t) ] * `Pr[ paT = u ] = 0.
Proof.
  intros.
  assert (`Pr[ [% paT, [% T, Z]] = (u, (t, z)) ] = 
      `Pr[ Z = z | [% paT, T] = (u, t) ] * `Pr[ T=t | paT=u] * `Pr[ paT=u]).
    rewrite !cpr_eqE.
    admit.
  rewrite H1 in H2.
  apply esym in H2.
  (* apply Rmult_integral in H2. *)
  Check GRing.mulf_eq0.
  move /eqP in H2.
  rewrite !GRing.mulf_eq0 in H2.
  move /orP in H2.
  inversion H2.
  move /orP in H3.
  inversion H3.
  
  move /eqP in H4.
  rewrite H4.
  rewrite GRing.mulr0.
  rewrite GRing.mul0r.
  reflexivity.

  move /eqP in H4.
  rewrite H4 in H0.
  apply false_cant_be in H0.
  simpl in H0.
  discriminate H0.

  move /eqP in H3.
  rewrite H3.
  rewrite GRing.mulr0.
  reflexivity.
Admitted.

Lemma use_indep_statements: forall h t, 
  Z _|_ T | paT ->
  H _|_ paT | [% T, Z] ->
  (* (exists z, z \in outcomesZ) -> *)
  (* (forall i0 i1, `Pr[ [% T, paT] = (i1, i0) ] != 0) -> *)
  (* (forall i0 i1 i2, `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) -> *)
  (forall u t, `Pr[ T=t | paT=u ] != 0) ->
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z] = (t, i) ] * `Pr[ Z = i | paT = u ] * `Pr[ paT = u ] = 
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z, paT] = (t, i, u) ] * `Pr[ Z = i | [% paT, T] = (u, t) ] 
      * `Pr[ paT = u ].
Proof.
  intros.
  apply eq_bigr.
  intros.
  apply eq_bigr.
  intros.
  (* apply mult_both_sides_r. *)
  specialize (H2 i0 t).
  pose proof (cond_to_pair_non_zero _ _ H2).
  pose proof (indep_to_equality _ _ _ i t i0 H0 H5).
  rewrite H6.
  case: (boolP (`Pr[ [% paT, [% T, Z]] = (i0, (t, i)) ] == 0)).
    intros.
    move /eqP in p.
    pose proof (oddly_specific _ _ _ h H2 p).
    rewrite H7.
    rewrite cpr_eq0_denom.
    rewrite mult_zero_left.
    rewrite mult_zero_left.
    reflexivity.
    rewrite pfwd1_pairC.
    assumption.
  
  intros.
  (* pose proof (pair_to_single_non_zero_specialized H3 H2).
  specialize (H6 i0 t).
  pose proof (indep_to_equality _ _ _ i t i0 H0 H6).
  specialize (H3 i0 i t). *)
  pose proof (indep_to_equality _ _ _ h i0 (t, i) H1 i1).
  (* apply indep_to_equality with (x := i) (y := t) (w := i0) in H0.
  apply indep_to_equality with (x := h) (y := i0) (w := (t, i)) in H1. *)
  (* rewrite H7. *)
  rewrite H7.
  reflexivity.
Qed.

(* Absolutely not proven, and idk if it is proveable. Trying to remove the condition
    where we need the equation to be non-zero at all values. *)
Lemma use_indep_statements_get_rid_of_zero: forall h t, 
  Z _|_ T | paT ->
  H _|_ paT | [% T, Z] ->
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z] = (t, i) ] * `Pr[ Z = i | paT = u ] * `Pr[ paT = u ] = 
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z, paT] = (t, i, u) ] * `Pr[ Z = i | [% paT, T] = (u, t) ] 
      * `Pr[ paT = u ].
Proof.
  intros.
  apply eq_bigr.
  intros.
  apply eq_bigr.
  intros.
  apply mult_both_sides_r.

  have [Hzero | Hnonzero] := boolP (`Pr[ [% paT, [% T, Z]] = (i0, (t, i)) ] == 0).
      move/eqP: Hzero => Hzero.
      assert (`Pr[ H = h | [% T, Z, paT] = (t, i, i0) ] = 0 ).
        admit.
      rewrite H4.
      rewrite mult_zero_left.
      have [Hzero' | Hnonzero' ] := boolP (`Pr[ paT = i0 ] == 0).
        move/eqP: Hzero' => Hzero'.
        rewrite cpr_eq0_denom; try assumption.
        rewrite mult_zero_right.
        reflexivity.

        assert (`Pr[ [% T, Z] = (t, i) ] = 0).
          unfold cinde_RV in H0.
          specialize (H0 i t i0).

          admit.
        rewrite -> cpr_eq0_denom with (Y := [%T, Z]); try assumption.
        rewrite mult_zero_left.
        reflexivity.
      
  (* apply use_indep_statements; try assumption.  *)
  admit.
Admitted.

(* Lemma saying that it the parental adjustment formula, some
    independence statements, and a non-zero statement is true,
    THEN the backdoor adjustment formula holds. 
    Notes: the non-zero condition feels like it could maybe be 
      removed/isn't a great assumption to be making? Could it
      be an artifact of the way we write Hinterv vs H|T? *)
Lemma parental_to_cond: forall t,
  (forall h, `Pr[(Hinterv t) = h] = \sum_(u : outcomesPaT) 
      `Pr[ H = h | [% T, paT] = (t, u)] * `Pr[paT=u]) ->
  T _|_ Z | paT ->
  H _|_ paT | [% T, Z] ->
  (* (exists z, z \in outcomesZ) -> *)
  (* (forall (i0 : outcomesPaT) (i1 : outcomesZ) (i2 : outcomesT), 
      `Pr[ [% paT, T, Z] = (i0, i2, i1) ] != 0) -> *)
  (forall u t, `Pr[ T = t | paT = u] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(z : outcomesZ) 
      `Pr[ H = h | [% T, Z] = (t, z)] * `Pr[Z=z]).
Proof. 
  move => t fact ind1 ind2 nonzero h.
  assert (forall z, `Pr[ H = h | [% T, Z] = (t, z) ] * `Pr[ Z = z ] = 
      `Pr[ H = h | [% T, Z] = (t, z) ] * \sum_(u in outcomesPaT) 
      `Pr[ Z = z | paT = u] * `Pr[ paT = u ]).
    intros.
    apply mult_both_sides_l.
    (* rewrite <- marginalize. *)
    apply marginalize.
  (* Check eq_bigr. *)
  rewrite -> eq_bigr with (F2 := fun z => `Pr[ H = h | [% T, Z] = (t, z) ] *
      (\sum_(u in outcomesPaT) `Pr[ Z = z | paT = u ] * `Pr[ paT = u ])); cycle 1.
    intros.
    specialize (H0 i).
    apply H0.
  assert (\sum_(i in outcomesZ) `Pr[ H = h | [% T, Z] = (t, i) ] * 
      (\sum_(u in outcomesPaT) `Pr[ Z = i | paT = u ] * `Pr[ paT = u ]) =
      \sum_(i in outcomesZ) (\sum_(u in outcomesPaT) 
      `Pr[ H = h | [% T, Z] = (t, i) ] * `Pr[ Z = i | paT = u ] * `Pr[ paT = u ])).
    apply eq_bigr.
    intros.
    rewrite big_distrr.
    simpl.
    apply eq_bigr.
    intros.
    rewrite GRing.mulrA.
    reflexivity.
  rewrite H1.
  rewrite use_indep_statements; cycle 1.
    apply cinde_RV_sym.
    assumption.
    assumption.
    assumption.
    (* intros.
    (* Check pfwd1_pairA. *)
    rewrite pfwd1_pairA.
    specialize (H4 i0 i1 i2).
    assumption. *)
  rewrite exchange_big.
  simpl.
  under eq_bigr => i _.
    rewrite -big_distrl.
    simpl.
    under eq_bigr => i0 _.
      rewrite rearrange_cond.
      rewrite rearrange_brackets.
      simpl.
      over.
    simpl.
    rewrite -marginalize_cond.
    over.
  simpl.
  rewrite fact.
  apply eq_bigr => i _.
  apply mult_both_sides_r.
  apply rearrange_cond.
Qed.

(* T _|_ Z | paT
  Z not descendants of T
  parents T = paT 
  --------
  Z no descendant of T -> Z and T d-sep of Z and T have backdoor path through paT
  paT is a mediator of confounder on backdoor path bw Z and T
  backdoor path bw Z and T blocked by paT 
  Z and T d-sep *)

(* H _|_ paT | [% T, Z] 
  Z not descendants of T
  parents T = paT 
  H descendant of T
  --------

  *)

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                SECTION : Parental Adjustment Formula
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

(* Lemma temp: forall t h,
  \sum_(u in (outcomesT * outcomesPaT * outcomesE)%type)
      `Pr[ [% Hinterv t, [% Tinterv t, paTinterv t, Einterv t]] = (h, u) ] = 
  \sum_(t' in outcomesT) (\sum_(pa' in outcomesPaT) ( \sum_(e' in outcomesE)
      `Pr[ [% Hinterv t, [% Tinterv t, paTinterv t, Einterv t]] = (h, t', pa', e') ])).
Proof.
  intros.
  rewrite pair_bigA. *)
  
(* 
Lemma parental: forall h t pa e,
  `Pr[ [% (Hinterv t), (Tinterv t), (paTinterv t), (Einterv t)] = (h, t, pa, e) ] 
      = `Pr[ [% H, T, paT, E] = (h, t, pa, e) ]/`Pr[ T = t | paT = pa ] ->
  (forall t', t' = t -> `Pr[(Tinterv t') = t] = 1) ->
  (forall t', t' != t -> `Pr[(Tinterv t') = t] = 0) ->
  `Pr[(Hinterv t) = h] = \sum_(u in outcomesPaT) 
      `Pr[ H=h | [% T, paT] = (t, u)] * `Pr[paT=u]. *)


(* Lemma proving the parental adjustment formula is true, 
    given some starting equation. The starting equation comes
    from Markov factorizations, but we aren't working with 
    Markov factorizations to avoid having to work with paT and
    E as sets. *)
Lemma parental: forall t,
  (forall h pa e,
    `Pr[ [% (Hinterv t), (paTinterv t), (Einterv t)] = (h, pa, e) ] 
        = `Pr[ [% H, T, paT, E] = (h, t, pa, e) ] / `Pr[ T = t | paT = pa ]) ->
  (* (forall i0 i1 i2, `Pr[ [% paT, T, Z] = (i0, i2, i1) ] != 0) -> *)
  (forall i0 i1, `Pr[ [% paT, T] = (i0, i1) ] != 0) ->
  (* (exists z, z \in outcomesZ) -> *)
  (forall h, `Pr[(Hinterv t) = h] = \sum_(u: outcomesPaT) 
      `Pr[ H=h | [% T, paT] = (t, u)] * `Pr[paT=u]).
Proof.
  intros.
  rewrite (total_prob' (Hinterv t) (paTinterv t) h).
  apply eq_bigr => u _.
  rewrite (total_prob' [% Hinterv t, paTinterv t] (Einterv t) (h, u)).
  under eq_bigr => u0 _.
    specialize (H0 h u u0).
    rewrite H0.
    over.
  rewrite <- big_enum.
  (* simpl.
  Check big_enum.
  rewrite <- big_enum with (A := outcomesE)
      (F := (fun u0 => `Pr[ [% H, T, paT, E] = (h, t, u, u0) ] / `Pr[ T = t | paT = u ])). *)
  simpl.
  (* Check big_distrl. *)
  (* under eq_bigr => i _. *)

  assert (\sum_(i <- enum outcomesE) `Pr[ [% H, T, paT, E] = (h, t, u, i) ] / `Pr[ T = t | paT = u ] =
          (\sum_(i <- enum outcomesE) `Pr[ [% H, T, paT, E] = (h, t, u, i) ]) / `Pr[ T = t | paT = u ]).
    rewrite big_distrl.
    simpl.
    reflexivity.
  rewrite H2.

  (* rewrite <- big_distrl with (r := (enum outcomesE))
      (a := (`Pr[ T = t | paT = u ])^-1)
      (F := (fun i => `Pr[ [% H, T, paT, E] = (h, t, u, i) ])). *)
  rewrite big_enum.
  simpl.
  (* case: (boolP (`Pr[ [% T, paT] = (t, u) ] == 0)).
    intros.
    move /eqP in p.
    rewrite -> cpr_eq0_denom with (Y := [% T, paT]); try assumption.
    rewrite mult_zero_left.
    under eq_bigr => e _.
      Check pfwd1_pairAC.
      (* rewrite pfwd1_pairAC. *)
      rewrite pfwd1_pairC.
      unfold swap. simpl.
      assert (`Pr[ [% E, [% H, T, paT]] = (e, (h, t, u)) ] 
          = `Pr[ [% [% E, H], [% T, paT]] = ((e, h), (t, u)) ]).
        rewrite [in RHS] pfwd1_pairA.
        admit.
      rewrite H2.
      (* Check pfwd1_pairAC.
      rewrite <- pfwd1_pairA.
      rewrite -> pfwd1_pairA with (TY := T) (TZ := paT).
      rewrite -> pfwd1_pairAC with (TY := [% T, paT]).
      Check pfwd1_domin_RV1. *)
      rewrite pfwd1_domin_RV1; try assumption.
    over.
    simpl.
    rewrite big1.
    rewrite zero_div_zero.
    reflexivity.
      
      

  intros. *)
  rewrite <- total_prob' with (X := [% H, T, paT]) (W := E).
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite div_div.
  rewrite pfwd1_pairA.
  reflexivity.

  specialize (H1 u t).
  rewrite pfwd1_pairC. unfold swap. simpl.
  assumption.
  specialize (H1 u t).
  rewrite -> pair_to_single_non_zero_left with (Y := T) (y := t).
  exact is_true_true.
  assumption.
  (* destruct H2 as [z].
  specialize (H1 u z t).
  rewrite pfwd1_pairC. unfold swap. simpl.
  pose proof (pair_to_single_non_zero_left [% paT, T] Z (u, t) z H1).
  assumption.
  destruct H2 as [z].
  specialize (H1 u z t).
  rewrite <- pfwd1_pairA in H1.
  pose proof (pair_to_single_non_zero_left paT [% T, Z] u (t, z) H1).
  assumption. *)
  (* apply pair_to_single_non_zero_left with (Y := Z) (y := z). *)
Qed.


(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                  SECTION : Putting it together
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

(* Given Markov factorization equation,
        independence statements,
        non-zero statment,
    THEN the backdoor adjustment formula is true. *)
Lemma graphfactor_indp_backdoor_adj: forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), (paTinterv t), (Einterv t)] = (h, pa, e) ] 
      = `Pr[ [% H, T, paT, E] = (h, t, pa, e) ] / `Pr[ T = t | paT = pa ]) ->
  T _|_ Z | paT ->
  H _|_ paT | [% T, Z] ->
  (* (exists z, z \in outcomesZ) -> *)
  (* (forall i0 i1 i2, `Pr[ [% paT, T, Z] = (i0, i2, i1) ] != 0) -> *)
  (forall u t, `Pr[ T = t | paT = u] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(z: outcomesZ) 
      `Pr[ H = h | [% T, Z] = (t, z)] * `Pr[Z=z]).
Proof.
  intros.
  apply parental_to_cond; try assumption.
  apply parental; try assumption.
  intros.
  rewrite pfwd1_pairC.
  unfold swap. simpl.
  apply cond_to_pair_non_zero.
  specialize (H3 i0 i1).
  assumption.
Qed.

Print Assumptions graphfactor_indp_backdoor_adj.

(* Note: move for all h in *)
(* (paTinterv t) = paT *)
(* (Zinterv t) = Z *)
(* paT = [% paT1, paT2, paT3, ..., paTn ] *)

End ParentalAdjustmentFormula.










(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                  SECTION : Testing Examples
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)


Section FourVarConfounderExample.
(* Graph :  C <- E -> H
            T <- C -> H
               T -> H *)

(* Graph:           E
                   / |
                  C  |
                 / \ v
                T--->H*)

(* T=t, H=h, paT = C, E = CE Z = C *)


Context {R : realType}.

Variables (UT UH UC UE : finType).
Variable P : R.-fdist (((UE * UC) * UT) * UH).
Variable outcomesT: finType.
Variable outcomesH: finType.
Variable outcomesC: finType.
Variable outcomesE: finType.

Variable fE : UE -> outcomesE.
Variable fC : UC -> outcomesE -> outcomesC.
Variable fT : UT -> outcomesC -> outcomesT.
Variable fH : UH -> outcomesE -> outcomesC -> outcomesT -> outcomesH.

(* Let E (p: UE * UC * UT * UH) : outcomes :=
  fE p.1.1.1.
Let C (p: UE * UC * UT * UH) : outcomes :=
  fC p.1.1.2 (E p).
Let T (p : UE * UC * UT * UH ): outcomes :=
  fT p.1.2 (C p).
Let H (p : UE * UC * UT * UH) : outcomes :=
  fH p.2 (E p) (C p) (T p).
Let Hinterv (p : UE * UC * UT * UH) t : outcomes :=
  fH p.2 (E p) (C p) t.  

Let Enodefn : {RV P -> outcomes} :=
  fun u => E u.
Let Cnodefn : {RV P -> outcomes} :=
  fun u => C u.
Let Tnodefn : {RV P -> outcomes} :=
  fun u => T u.
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Hnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Hinterv u t. *)

Let E : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.
Let C : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (E p).
Let T : {RV P -> outcomesT} :=
  fun p => fT p.1.2 (C p).
Let H : {RV P -> outcomesH} :=
  fun p => fH p.2 (E p) (C p) (T p).

Let Tinterv (t: outcomesT) : {RV P -> outcomesT} :=
  fun p => t.
Let Einterv (t: outcomesT) : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.
Let Cinterv (t: outcomesT) : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (Einterv t p).
Let Hinterv (t: outcomesT) : {RV P -> outcomesH}:= 
  fun p => fH p.2 (Einterv t p) (Cinterv t p) t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.2.
Let UERV: {RV P -> UE} :=
  fun u => u.1.1.1.

Definition mutual_indep_three {X' Y' Z': finType}
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}) := 
  (forall x y z,
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [%[% X, Y], Z] = ((x,y), z)]) /\ 
    P |= X _|_ Y /\ P |= Y _|_ Z /\ P |= X _|_ Z.

Definition mutual_indep_four {W' X' Y' Z': finType}
  (W : {RV P -> W'}) (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}) := 
  (forall w x y z,
  `Pr[ W = w ] * `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [% [% [% W, X], Y], Z] = (((w,x),y),z)]) /\ 
  mutual_indep_three W X Y /\
  mutual_indep_three W X Z /\
  mutual_indep_three W Y Z /\
  mutual_indep_three X Y Z.

Lemma mult_one_right: forall (a : R),
  a * 1 = a.
Proof.
  Check GRing.mulr1.
  apply GRing.mulr1.
Qed.

Lemma zero_div_zero': forall (a : R),
  a != 0 ->
  0 / a = 0.
Proof.
Admitted.

Lemma a_div_a_is_one: forall (a : R),
  a != 0 ->
  a / a = 1.
Proof.
Admitted.

Lemma pfwd1_diag_ext (U U': eqType) 
  (X : {RV P -> U}) (Y: {RV P -> U'}) (x : U) (y : U') : 
  `Pr[ [% Y, X, X] = (y, x, x) ] = `Pr[ [% Y, X] = (y, x) ].
Proof.
  rewrite pfwd1E.
  rewrite pfwd1E.
  rewrite /Pr.
  apply eq_bigl => a.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a == x).
    case Hy : (Y a == y).
      simpl.
      reflexivity.
      simpl.
      reflexivity.
      rewrite !andbF.
      reflexivity.
(* by rewrite !pfwd1E /Pr; apply: eq_bigl=> a; rewrite !inE xpair_eqE andbb. *)
Qed.

Lemma if_one_is_true_the_other_isnt: forall {X': finType} 
  (X : {RV P -> X'}) b c a,
  b != c ->
  (X a == b) = true ->
  (X a == c) = false.
Proof.
  intros.
  by rewrite (eqP H1); exact/negbTE.
Qed.

Lemma pfwd1_diag_not_xx: forall {X': finType} (X : {RV P -> X'}) b c,
  b != c ->
  `Pr[ [% X, X] = (b, c) ] = 0.
Proof.
  intros.
  rewrite !pfwd1E /Pr.
  under eq_bigl => a.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a == b).
    assert ((X a == c) = false). eapply if_one_is_true_the_other_isnt.
      exact H0.
      exact Hx. 
    rewrite H1.
    simpl.
    over.

    simpl.
    over.

    simpl.
    apply big_pred0_eq.
Qed.

Lemma pfwd1_diag_not: forall {X' Y' : finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) b c y,
  b != c ->
  `Pr[ [% Y, X, X] = (y, b, c) ] = 0.
Proof.
  intros.
  rewrite !pfwd1E /Pr.
  under eq_bigl => a.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a == b).
    assert ((X a == c) = false). eapply if_one_is_true_the_other_isnt.
      exact H0.
      exact Hx. 
    rewrite H1.
    rewrite andbF.
    over.

    rewrite andbF.
    simpl.
    over.

    simpl.
    apply big_pred0_eq.
Qed.

Lemma var_cond_diff_zero: forall {X': finType} (X : {RV P -> X'}) b c,
  b != c ->
  `Pr[ X = b | X = c ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ X = c ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_diag_not_xx; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma var_cond_diff_zero_gen: forall {X' Y': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) b c y,
  b != c ->
  `Pr[ [% Y, X] = (y, b) | X = c ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ X = c ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_diag_not; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma var_cond_diff_zero_gen2: forall {X' Y' W': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) (W : {RV P -> W'}) b c w y,
  b != c ->
  `Pr[ [% Y, X] = (y, b) | [% W, X] = (w, c) ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ [% W, X] = (w, c) ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_pairCA.
  assert (`Pr[ [% W, [% Y, X, X]] = (w, (y, b, c)) ]
      = `Pr[ [% W, Y, X, X] = (w, y, b, c) ]).
    rewrite !pfwd1E /Pr.
    apply: eq_bigl=> a0.
    rewrite !inE.
    rewrite !xpair_eqE.
    case Hb : (X a0 == b).
      assert ((X a0 == c) = false). eapply if_one_is_true_the_other_isnt.
        exact H0.
        exact Hb. 
      rewrite H1.
      rewrite !andbF.
      reflexivity.
      rewrite !andbF.
      simpl.
      reflexivity.
  rewrite H1.
  rewrite pfwd1_diag_not; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma var_cond_diff_zero_gen3: forall {X' Y': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) b c y,
  b != c ->
  `Pr[ X = b | [% Y, X] = (y, c) ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ [% Y, X] = (y, c) ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_pairCA.
  rewrite pfwd1_pairA.
  rewrite pfwd1_diag_not; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma extra_indentical_factor: forall t c,
  `Pr[ [% T, C] = (t, c) | C = c] = `Pr[ T = t | C = c].
Proof.
  intros.
  rewrite cpr_eqE.
  Check pfwd1_diag.
  rewrite pfwd1_diag_ext.
  rewrite <- cpr_eqE.
  reflexivity.
Qed.

Lemma var_in_cond_true: forall {X' Y': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) x y,
  `Pr[ [% Y, X] = (y, x) ] != 0 ->
  `Pr[ X = x | [% Y, X] = (y, x) ] = 1.
Proof.
  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_pairCA.
  rewrite pfwd1_pairA.
  rewrite pfwd1_diag_ext.
  rewrite a_div_a_is_one.
  reflexivity.
  assumption.
Qed.

(* Lemma extra_identical_factor_general: forall {X' Y' W': finType} 
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (W : {RV P -> W'}) w x a b,
  b != c ->
  `Pr[ [% Y, X] = (y, b) | X = c ] = 0.
  `Pr[ [% T, C] = (t, c) | C = c] = `Pr[ T = t | C = c]. *)

Lemma fvc_indep1:
  (* mutual_indep_four E C T H -> *)
  (forall c t, `Pr[ [% C, T] = (c, t) ] != 0) ->
  T _|_ C | C.
Proof.
  intros.
  unfold cinde_RV.
  intros.
  have [Hc | Hc'] := boolP (b == c).
    move/eqP: Hc => Hc.
    rewrite Hc.
    rewrite cPr_eq_id.
    rewrite extra_indentical_factor.
    rewrite mult_one_right.
    reflexivity.
  
    specialize (H0 c a).
    (* Check pair_to_single_non_zero. *)
    apply pair_to_single_non_zero with (outcomesH := outcomesH)
        (outcomesT := outcomesT) (outcomesPaT := outcomesH) 
        (outcomesZ := outcomesH) (outcomesE := outcomesH) in H0; try eauto.

  rewrite var_cond_diff_zero; try assumption.
  rewrite mult_zero_right.
  rewrite var_cond_diff_zero_gen; try assumption.
  reflexivity.
Qed.

Lemma fvc_indep2:
  (* mutual_indep_four E C T H -> *)
  H _|_ C | [% T, C].
Proof.
  intros.
  unfold cinde_RV.
  intros.
  destruct c as [t c].
  case (boolP (b == c)).
    intros.
    move /eqP in i.
    inversion i.
    (* pose proof (remove_redundant_cond_term). *)
    rewrite -> remove_redundant_cond_term with (outcomesH := outcomesH)
        (outcomesT := outcomesT) (outcomesPaT := outcomesC) 
        (outcomesZ := outcomesC) (outcomesE := outcomesE); try eauto.
    case (boolP (`Pr[ [% T, C] = (t, c) ] == 0)).
      intros.
      move /eqP in i0.
      rewrite !cpr_eq0_denom; try assumption.
      rewrite GRing.mul0r.
      reflexivity.
    intros.
    rewrite var_in_cond_true.
    rewrite mult_one_right.
    reflexivity.
    assumption.
    
  intros.
  rewrite -> cond_term_makes_impossible with (outcomesH := outcomesH)
        (outcomesT := outcomesT) (outcomesPaT := outcomesC) 
        (outcomesZ := outcomesC) (outcomesE := outcomesE); try eauto.
  rewrite -> var_cond_diff_zero_gen3; try assumption.
  rewrite GRing.mulr0.
  reflexivity.
Qed.

(* Lemma extra_factor_in_nonzero:
  (forall i0 i2, `Pr[ [% C, T] = (i0, i2) ] != 0) ->
  (forall i0 i1 i2, `Pr[ [% C, T, C] = (i0, i2, i1) ] != 0).
Proof.
Admitted. *)

Lemma four_var_confounder_backdoor_adjustment: forall t,
  (forall h c e,
  `Pr[ [% (Hinterv t), (Cinterv t), (Einterv t)] = (h, c, e) ] 
      = `Pr[ [% H, T, C, E] = (h, t, c, e) ] / `Pr[ T = t | C = c ]) ->
  mutual_indep_four UERV UCRV UTRV UHRV ->
  (forall u t, `Pr[ T = t | C = u ] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(c : outcomesC) 
      `Pr[ H = h | [% T, C] = (t, c)] * `Pr[C = c]).
Proof.
  intros.
  (* pose proof (fvc_indep1 H1).
  pose proof (fvc_indep2 H1).
  pose proof (extra_factor_in_nonzero H2). *)
  eapply graphfactor_indp_backdoor_adj with (paT := C) 
    (paTinterv := Cinterv) (Einterv := Einterv) (E := E); try assumption.
  info_eauto.
  apply fvc_indep1; try assumption.
  intros.
  specialize (H2 c t0).
  rewrite pfwd1_pairC. unfold swap. simpl.
  apply cond_to_pair_non_zero with (outcomesH := outcomesH) 
      (outcomesZ := outcomesC) (outcomesE := outcomesE); eauto.
  apply fvc_indep2; try assumption.
  (* apply extra_factor_in_nonzero; try assumption. *)
Qed.

(* Print Assumptions four_var_confounder_backdoor_adjustment. *)

End FourVarConfounderExample.


Section LargeExample.
Context {R : realType}.

Variables (UT UH UC UE UQ UD UF UG : finType).
Variable P : R.-fdist (((((((UG * UQ) * UD) * UF ) * UE) * UC) * UT) * UH).
Variable outcomesT: finType.
Variable outcomesH: finType.
Variable outcomesC: finType.
Variable outcomesE: finType.
Variable outcomesQ: finType.
Variable outcomesD: finType.
Variable outcomesF: finType.
Variable outcomesG: finType.

Variable fE : UE -> outcomesE.
Variable fC : UC -> outcomesE -> outcomesC.
Variable fQ : UQ -> outcomesQ.
Variable fF : UF -> outcomesF.
Variable fD : UD -> outcomesF -> outcomesD.
Variable fT : UT -> outcomesC -> outcomesQ -> outcomesD -> outcomesT.
Variable fH : UH -> outcomesE -> outcomesC -> outcomesF -> outcomesT -> outcomesH.
Variable fG : UG -> outcomesH -> outcomesT -> outcomesG.

Let E : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.2.
Let C : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (E p).
Let Q: {RV P -> outcomesQ} :=
  fun p => fQ p.1.1.1.1.1.1.2.
Let F: {RV P -> outcomesF} :=
  fun p => fF p.1.1.1.1.2.
Let D: {RV P -> outcomesD} :=
  fun p => fD p.1.1.1.1.1.2 (F p).
Let T : {RV P -> outcomesT} :=
  fun p => fT p.1.2 (C p) (Q p) (D p).
Let H : {RV P -> outcomesH} :=
  fun p => fH p.2 (E p) (C p) (F p) (T p).
Let G : {RV P -> outcomesG} :=
  fun p => fG p.1.1.1.1.1.1.1 (H p) (T p).

Let Tinterv (t: outcomesT) : {RV P -> outcomesT} :=
  fun p => t.
Let Einterv (t: outcomesT) : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.2.
Let Cinterv (t: outcomesT) : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (Einterv t p).
Let Qinterv (t: outcomesT) : {RV P -> outcomesQ} :=
  fun p => fQ p.1.1.1.1.1.1.2.
Let Finterv (t: outcomesT) : {RV P -> outcomesF} :=
  fun p => fF p.1.1.1.1.2.
Let Dinterv (t: outcomesT) : {RV P -> outcomesD} :=
  fun p => fD p.1.1.1.1.1.2 (F p).
Let Hinterv (t: outcomesT) : {RV P -> outcomesH}:= 
  fun p => fH p.2 (Einterv t p) (Cinterv t p) (Finterv t p) t.
Let Ginterv (t: outcomesT) : {RV P -> outcomesG} :=
  fun p => fG p.1.1.1.1.1.1.1 (Hinterv t p) t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.2.
Let UERV: {RV P -> UE} :=
  fun u => u.1.1.1.2.
Let UFRV: {RV P -> UF} := 
  fun u => u.1.1.1.1.2.
Let UDRV: {RV P -> UD} :=
  fun u => u.1.1.1.1.1.2.
Let UQRV: {RV P -> UQ} :=
  fun u => u.1.1.1.1.1.1.2.
Let UGRV: {RV P -> UG} :=
  fun u => u.1.1.1.1.1.1.1.

(*  H = H
    T = T
    paT = [% C, D, Q ]
    E = [% E, F]
    Z = [% C, F]
*)

Lemma eight_var_confounder_backdoor_adjustment: forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Qinterv t)], 
      [% (Einterv t), (Finterv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, Q] , [% E, F]] = (h, t, pa , e ) ] 
        / `Pr[ T = t | [% C, D, Q] = pa ]) ->
  T _|_ [% C, F] | [% C, D, Q] ->
  H _|_ [% C, D, Q] | [% T, [% C, F]] ->
  (forall pa t, `Pr[ T = t | [% C, D, Q] = pa ] != 0) ->
  (* true. *)
  (forall h, `Pr[(Hinterv t) = h] = \sum_(cf : outcomesC * outcomesF) 
      `Pr[ H = h | [% T, [% C, F] ] = (t, cf)] * `Pr[[% C, F] = cf]).
Proof.
  intros.
  apply graphfactor_indp_backdoor_adj with 
      (outcomesPaT := (outcomesC*outcomesD*outcomesQ)%type)
      (outcomesE := (outcomesE*outcomesF)%type)
      (paT := [% C, D, Q]) (E := [% E, F])
      (paTinterv := (fun t => [% (Cinterv t), (Dinterv t), (Qinterv t)]))
      (Einterv := (fun t => [% (Einterv t), (Finterv t)])); eauto. 
  exact (fun t => [% (Cinterv t), (Finterv t)]).
Qed.

Lemma can_swap_indep_cond_order: forall  {A B C D : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}),
  X _|_ Y | [% W, V] ->
  X _|_ Y | [% V, W].
Proof.
Admitted.

Lemma adding_brackets_in_indep: forall  {A B C D A' : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}) (Z' : {RV P -> A'}),
  Z' _|_ V | [% W, X, Y] ->
  Z' _|_ V | [% W, [% X, Y]].
Proof.
  intros.
  unfold cinde_RV.
  unfold cinde_RV in H0.
  intros.
  destruct c as [w [x y]].
  specialize (H0 a b (w, x, y)).
Admitted.

Lemma eight_var_confounder_backdoor_adjustment_weaker_indp: forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Qinterv t)], 
      [% (Einterv t), (Finterv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, Q] , [% E, F]] = (h, t, pa , e ) ] 
        / `Pr[ T = t | [% C, D, Q] = pa ]) ->
  T _|_ F | [% C, D, Q] ->
  H _|_ [% D, Q] | [% T, [% C, F]] ->
  (forall pa t, `Pr[ T = t | [% C, D, Q] = pa ] != 0) ->
  (* true. *)
  (forall h, `Pr[(Hinterv t) = h] = \sum_(cf : outcomesC * outcomesF) 
      `Pr[ H = h | [% T, [% C, F] ] = (t, cf)] * `Pr[[% C, F] = cf]).
Proof.
  intros.
  apply eight_var_confounder_backdoor_adjustment; try assumption.
  (* apply can_swap_indep_cond_order in H1. *)
  apply adding_brackets_in_indep in H1.
  pose proof (can_swap_indep_cond_order T F C [% D, Q] H1).
  (* apply adding_conditional_to_indep in H4. *)

  (* pose proof (adding_conditional_to_indep T F C [% D, Q]). *)
  unfold cinde_RV in H4. 
  apply adding_conditional_to_indep with (outcomesH := outcomesH)
      (outcomesT := outcomesT) (outcomesPaT := outcomesH) (outcomesZ := outcomesH)
      (outcomesE := outcomesH) in H4; eauto.
  admit.
Admitted.
  

End LargeExample.