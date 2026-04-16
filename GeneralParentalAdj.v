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
  (* c != 0 -> *)
  a = b ->
  a * c = b * c.
Proof.
Admitted.

Lemma mult_both_sides_l: forall (a b c : R),
  (* c != 0 -> *)
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
  a / b * ( b / c ) = a / c.
Proof.
Admitted.

Lemma mult_zero_right: forall (a : R),
  a * 0 = 0.
Proof.
Admitted.

Lemma mult_zero_left: forall (a : R),
  0 * a = 0.
Proof.
Admitted.

Lemma div_div: forall (a b c : R),
  a / (b / c) = a / b * c.
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
  under eq_bigr => u _.
    rewrite !cpr_eqE.
    rewrite -> pfwd1_pairC with (TY := Y) (TX := W).
    simpl.
    rewrite mult_in_middle.
    over.
  simpl.
  (* Check big_enum. *)
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
Admitted.

Lemma pair_to_single_non_zero_left: forall {A B : finType} 
  (X : {RV P -> A}) (Y : {RV P -> B}) x y,
  (forall (i0 : outcomesPaT) (i1 : outcomesZ) (i2 : outcomesT), 
      `Pr[ [% X, Y] = (x, y) ] != 0) ->
  (forall (i0 : outcomesPaT) (i1 : outcomesT),
      `Pr[ X = x ] != 0).
Proof.
Admitted.

Lemma pair_to_single_non_zero_right: forall {A B : finType} 
  (X : {RV P -> A}) (Y : {RV P -> B}) x y,
  (forall (i0 : outcomesPaT) (i1 : outcomesZ) (i2 : outcomesT), 
      `Pr[ [% X, Y] = (x, y) ] != 0) ->
  (forall (i0 : outcomesPaT) (i1 : outcomesT),
      `Pr[ Y = y ] != 0).
Proof.
Admitted.

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                SECTION : Parental Adjustment Formula ->
                    Backdoor Adjustment Formula
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

Lemma pair_to_single_non_zero_specialized: 
  (forall (i0 : outcomesPaT) (i1 : outcomesZ) (i2 : outcomesT), 
      `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) ->
  (forall (i0 : outcomesPaT) (i1 : outcomesT),
      `Pr[ [% T, paT] = (i1, i0) ] != 0).
Proof.
  intros.
  (* specialize (H0 i0 i1).
  Check pfwd1_domin_RV2. *)
Admitted.

Lemma use_indep_statements: forall h t, 
  Z _|_ T | paT ->
  H _|_ paT | [% T, Z] ->
  (* (forall i0 i1, `Pr[ [% T, paT] = (i1, i0) ] != 0) -> *)
  (forall i0 i1 i2, `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) ->
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
  pose proof (pair_to_single_non_zero_specialized H2).
  specialize (H5 i0 t).
  pose proof (indep_to_equality _ _ _ i t i0 H0 H5).
  specialize (H2 i0 i t).
  pose proof (indep_to_equality _ _ _ h i0 (t, i) H1 H2).
  (* apply indep_to_equality with (x := i) (y := t) (w := i0) in H0.
  apply indep_to_equality with (x := h) (y := i0) (w := (t, i)) in H1. *)
  rewrite H6.
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
Lemma parental_to_cond: forall h t,
  `Pr[(Hinterv t) = h] = \sum_(u in outcomesPaT) 
      `Pr[ H = h | [% T, paT] = (t, u)] * `Pr[paT=u] ->
  T _|_ Z | paT ->
  H _|_ paT | [% T, Z] ->
  (forall (i0 : outcomesPaT) (i1 : outcomesZ) (i2 : outcomesT), 
      `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) ->
  `Pr[(Hinterv t) = h] = \sum_(z in outcomesZ) 
      `Pr[ H = h | [% T, Z] = (t, z)] * `Pr[Z=z].
Proof. 
  intros.
  assert (forall z, `Pr[ H = h | [% T, Z] = (t, z) ] * `Pr[ Z = z ] = 
      `Pr[ H = h | [% T, Z] = (t, z) ] * \sum_(u in outcomesPaT) 
      `Pr[ Z = z | paT = u] * `Pr[ paT = u ]).
    intros.
    apply mult_both_sides_l.
    (* rewrite <- marginalize. *)
    apply marginalize.
  Check eq_bigr.
  rewrite -> eq_bigr with (F2 := fun z => `Pr[ H = h | [% T, Z] = (t, z) ] *
      (\sum_(u in outcomesPaT) `Pr[ Z = z | paT = u ] * `Pr[ paT = u ])); cycle 1.
    intros.
    specialize (H4 i).
    apply H4.
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
  rewrite H5.
  rewrite use_indep_statements; cycle 1.
    apply cinde_RV_sym.
    assumption.
    assumption.
    assumption.
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
  rewrite H0.
  apply eq_bigr => i _.
  apply mult_both_sides_r.
  apply rearrange_cond.
Qed.


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
Lemma parental: forall h t,
  (forall pa e,
    `Pr[ [% (Hinterv t), (paTinterv t), (Einterv t)] = (h, pa, e) ] 
        = `Pr[ [% H, T, paT, E] = (h, t, pa, e) ] / `Pr[ T = t | paT = pa ]) ->
  `Pr[(Hinterv t) = h] = \sum_(u in outcomesPaT) 
      `Pr[ H=h | [% T, paT] = (t, u)] * `Pr[paT=u].
Proof.
  intros.
  rewrite (total_prob' (Hinterv t) (paTinterv t) h).
  apply eq_bigr => u _.
  rewrite (total_prob' [% Hinterv t, paTinterv t] (Einterv t) (h, u)).
  under eq_bigr => u0 _.
    specialize (H0 u u0).
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
  rewrite H1.

  (* rewrite <- big_distrl with (r := (enum outcomesE))
      (a := (`Pr[ T = t | paT = u ])^-1)
      (F := (fun i => `Pr[ [% H, T, paT, E] = (h, t, u, i) ])). *)
  rewrite big_enum.
  simpl.
  rewrite <- total_prob' with (X := [% H, T, paT]) (W := E).
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite div_div.
  rewrite pfwd1_pairA.
  reflexivity.
Qed.


(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                  SECTION : Putting it together
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

(* Given Markov factorization equation,
        independence statements,
        non-zero statment,
    THEN the backdoor adjustment formula is true. *)
Lemma markov_indp_backdoor: forall t h,
  (forall pa e,
  `Pr[ [% (Hinterv t), (paTinterv t), (Einterv t)] = (h, pa, e) ] 
      = `Pr[ [% H, T, paT, E] = (h, t, pa, e) ] / `Pr[ T = t | paT = pa ]) ->
  T _|_ Z | paT ->
  H _|_ paT | [% T, Z] ->
  (forall i0 i1 i2, `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) ->
  `Pr[(Hinterv t) = h] = \sum_(z in outcomesZ) 
      `Pr[ H = h | [% T, Z] = (t, z)] * `Pr[Z=z].
Proof.
  intros.
  apply parental_to_cond; try assumption.
  apply parental; assumption.
Qed.