From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
Require Import Reals.
From infotheo.probability Require Import proba fdist. (* fsdist jfdist_cond. *)
Require Import List.
Import ListNotations.
From mathcomp Require Import reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require Import unstable mathcomp_extra reals exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section TwoVarExample.

Context {R : realType}.
Variables (UT UH : finType).
Variable P : R.-fdist (UT * UH).
(* Variables (UTRV : {RV P -> UT}) (UHRV : {RV P -> UH}). *)
Variable fT : UT -> R.
Variable fH : UH -> R -> R.
Let T (p : UT * UH ): R :=
  fT p.1.
Let Hinterv (p : UT * UH) t : R :=
  fH p.2 t. 
Let H (p : UT * UH) : R :=
  fH p.2 (T p).
Let nodefn : {RV P -> R * R} :=
  fun u => (T u , H u).
Let nodefnint (t:R) : {RV P -> R * R} :=
  fun u => (t , Hinterv u t).
Let Hnodefn : {RV P -> R} :=
  fun u => H u.
Let Hnodefnint (t:R) : {RV P -> R} :=
  fun u => Hinterv u t.
Let Tnodefn : {RV P -> R} :=  (*T.*)
  fun u => T u.
(* Locate "'RV'".
Print RV_of.
Print RV. *)
Let UTRV: {RV P -> UT} :=
  fun u => u.1.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.

Check comp_RV.
(* Check inde_RV_comp. *)

(* Lemma transform_fn:
  X _|_ Y -> f(X) _|_ Y.
  injective f? *)

Lemma mult_div: forall (a b: R),
  b != 0 ->
  a = a * b / b.
Proof.
  intros.
  rewrite <- GRing.mulrA.
  rewrite GRing.mulfV.
  (* Check GRing.mulr1. *)
  rewrite GRing.mulr1.
  reflexivity.
  assumption.
Qed.

Lemma div_mult: forall (a b: R),
  b != 0 ->
  a = a / b * b.
Proof.
  intros.
  eapply eqr_divrMr.
  assumption.
  reflexivity.
Qed.

Lemma indep_then_cond_irrelevant: 
    forall (TX: finType) (TZ: finType) (P: R.-fdist (TX*TZ) ) 
    (X: {RV P -> R}) (Z: {RV P -> R}),
  P |= Z _|_ X ->
  forall x, `Pr[ X = x ] != 0 ->
  forall z, `Pr[ Z = z ] = `Pr[ Z = z | X = x ].
Proof.
  intros.
  unfold inde_RV in H0.
  specialize (H0 z x).
  rewrite cpr_eqE.
  rewrite H0.
  set y := `Pr[ X = x].
  assert (y != 0) by exact H1.
  apply mult_div.
  assumption.
Qed.

Lemma prob_version: forall t,
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  pose proof (indep_then_cond_irrelevant UT UH P Tnodefn (Hnodefnint t) H0).
  specialize (H2 t).
  pose proof (H2 H1).
  specialize (H3 a).
  clear H2.
  rewrite H3.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold T.
  unfold Hnodefnint.
  unfold Hinterv.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  unfold Tnodefn in H1.
  unfold T in H1.
  eapply eqr_divrMr. assumption.
  rewrite <- div_mult; try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Ht : (fT a0.1 == t).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Qed.

Lemma prob_as_sum_of_eq: forall t, 
  (forall a, `Pr[ Hnodefn = a | Tnodefn = t ] = `Pr[ (Hnodefnint t) = a]) ->
  `E (Hnodefnint t) = \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint t)) 
      r * `Pr[ Hnodefn = r | Tnodefn = t ].
Proof.
  intros.
  rewrite <- Ex_altE.
  unfold Ex_alt.
  apply eq_big => r.
  reflexivity.
  intros.
  specialize (H0 r).
  rewrite H0.
  reflexivity.
Qed.

Lemma same_preimg_helper_int_general: forall t, 
  `Pr[ Tnodefn = t ] != 0 ->
  (forall a : R, `Pr[ Hnodefn = a | Tnodefn = t ] = `Pr[ (Hnodefnint t) = a ]) ->
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint t) | i
      \notin fin_img (A:=(UT * UH)%type) (B:=R) Hnodefn)
      i * `Pr[ Hnodefn = i | Tnodefn = t ] = 0.
Proof.
  intros.
  apply big1.
  intros.
  apply pfwd1_eq0 in H2.
  rewrite cpr_eqE.
  apply pfwd1_domin_RV2 with (TY := Tnodefn) (b := t) in H2.
  rewrite H2.
  rewrite GRing.mulrA.
  rewrite GRing.mulr0.
  rewrite eqr_divrMr.
  rewrite GRing.mul0r.
  reflexivity.
  assumption.
Qed.

Lemma same_preimg_helper_noint_general: forall t, 
  (forall a : R, `Pr[ Hnodefn = a | Tnodefn = t ] = `Pr[ (Hnodefnint t) = a ]) ->
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) Hnodefn | i
      \notin fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint t))
      i * `Pr[ Hnodefn = i | Tnodefn = t ] = 0.
Proof.
  intros.
  apply big1.
  intros.
  apply pfwd1_eq0 in H1.
  rewrite <- H0 in H1.
  rewrite H1.
  rewrite GRing.mulr0.
  reflexivity.
Qed.

Lemma fin_img_uniq: forall f1,
  uniq (fin_img (A:=(UT * UH)%type) (B:=R) f1).
Proof.
  intros.
  unfold fin_img.
  apply undup_uniq.
Qed.

Lemma seq_cond_or_cond_seq: forall (A B : seq R),
  uniq A ->
  uniq B ->
  perm_eq [seq i <- A | i  \in B] [seq i <- B | i  \in A].
Proof.
  intros.
  apply uniq_perm.
  - apply filter_uniq.
    assumption.
  - apply filter_uniq.
    assumption.
  - move=> x.
    rewrite mem_filter.
    rewrite mem_filter.
    apply Bool.andb_comm.
Qed.

Lemma sums_with_diff_index_forms: forall t (f1 f2 : {RV (P) -> (R)}),
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f1 | i \in fin_img (A:=(UT * UH)%type) (B:=R) f2) i * `Pr[ Hnodefn = i | Tnodefn = t ] = 
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | i \in fin_img (A:=(UT * UH)%type) (B:=R) f1) i * `Pr[ Hnodefn = i | Tnodefn = t ].
Proof.
  intros.
  rewrite <- big_filter.
  assert (\sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      i \in fin_img (A:=(UT * UH)%type) (B:=R) f1)
      i * `Pr[ Hnodefn = i | Tnodefn = t ] = 
      \sum_(i <- [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1])
      i * `Pr[ Hnodefn = i | Tnodefn = t ]).
    rewrite big_filter.
    reflexivity.
  rewrite H0.
  clear H0.
  apply perm_big.
  apply seq_cond_or_cond_seq.
  apply fin_img_uniq.
  apply fin_img_uniq.
Qed. 

Lemma sums_with_int_and_noint_index: forall t, 
  `Pr[ Tnodefn = t ] != 0 ->
  (forall a, `Pr[ Hnodefn = a | Tnodefn = t ] = `Pr[ (Hnodefnint t) = a ]) ->
  \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint t))
    r * `Pr[ Hnodefn = r | Tnodefn = t ] = 
    \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) Hnodefn)
    r * `Pr[ Hnodefn = r | Tnodefn = t ].
Proof.
  intros.
  Check bigID.
  rewrite (bigID (fun r => r \in fin_img (Hnodefn))).
  simpl.
  rewrite same_preimg_helper_int_general; cycle 1; try assumption.
  rewrite GRing.addr0.
  rewrite [in RHS] (bigID (fun r => r \in fin_img (Hnodefnint t))).
  simpl.
  rewrite same_preimg_helper_noint_general; cycle 1; try assumption.
  rewrite GRing.addr0.
  rewrite sums_with_diff_index_forms.
  reflexivity.
Qed.

Lemma prob_to_exp: forall t,
  `Pr[ Tnodefn = t ] != 0 ->
  (forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a]) ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) ] = `E (Hnodefnint t).
Proof.
  intros.
  rewrite prob_as_sum_of_eq; cycle 1. assumption.
  rewrite sums_with_int_and_noint_index; cycle 1. assumption. assumption.
  rewrite /cEx.
  apply eq_big => r. reflexivity.
  intros.
  rewrite <- GRing.mulrA.
  rewrite /cPr_eq.
  rewrite /cPr.
  unlock.
  reflexivity.
Qed.

Lemma doint_equiv: forall t, (* T -> H *)
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 -> 
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) ] = `E (Hnodefnint t).
Proof.
  intros.
  apply prob_to_exp. assumption.
  apply prob_version. assumption.
  assumption.
Qed.

(* Lemma indep_implication *)

(* Lemma
  UH indep UT ->
  P |= (Hnodefnint t) _|_ Tnodefn *)

(* Lemma prob_version_wo_indp: forall t,
  (* I'm not sure how to state that UH, UT are indep? I think it might be implicit in my sample space definition? *)
  (* P |= (Hnodefnint t) _|_ Tnodefn -> *)
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
Admitted. *)


Lemma doint_equiv_wo_indp: forall (t : R), 
  `Pr[ Tnodefn = t ] != 0 ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) ] = `E (Hnodefnint t).
Proof.
  intros.
  pose proof (prob_version_wo_indp t H0).
  pose proof (prob_to_exp t H0 H1).
  assumption.
Admitted.

End TwoVarExample.










Section ThreeVarExample.

Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UC * UT) * UH).

Variable fC : UC -> R.
Variable fT : UT -> R -> R.
Variable fH : UH -> R -> R -> R.

Let C (p: UC * UT * UH) : R :=
  fC p.1.1.
Let T (p : UC * UT * UH ): R :=
  fT p.1.2 (C p).
Let H (p : UC * UT * UH) : R :=
  fH p.2 (C p) (T p).
Let Hinterv (p : UC * UT * UH) t : R :=
  fH p.2 (C p) t.  

Let Cnodefn : {RV P -> R} :=
  fun u => C u.
Let Tnodefn : {RV P -> R} :=
  fun u => T u.
Let Hnodefn : {RV P -> R} :=
  fun u => H u.
Let Hnodefnint (t: R) : {RV P -> R}:= 
  fun u => Hinterv u t.


Lemma indep_then_cond_irrelevant_wcond: 
  forall (TX TY TZ: finType) (P: R.-fdist ((TY*TX)*TZ) ) (X Y Z: {RV P -> R}),
  Z _|_ X | Y->
  forall y, `Pr[ Y = y ] != 0 ->
  forall x, `Pr[ X = x | Y = y ] != 0 ->
  forall z, `Pr[ Z = z | Y = y] = `Pr[ Z = z | [%X, Y] = (x, y) ].
Proof.
  intros.
  unfold cinde_RV in H0.
  specialize (H0 z x y).
  rewrite [in RHS] cpr_eqE.
  Check eqr_divrMr.
  apply eqr_divrMr in H0; cycle 1. assumption.
  rewrite <- H0.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite pfwd1_pairA.
  (* rewrite pfwd1_pairAC. *)
  (* rewrite [in (`Pr[ [% X, Y] = (x, y) ])] pfwd1_pairC. *)
  (* rewrite /swap. *)
  (* simpl. *)



  (* rewrite GRing.commrV. *)
  (* Check GRing.mulVr. *)
  (* rewrite GRing.mulf_div.
  Search (_ / _ * _).
  info_eauto.
  rewrite GRing.mulrA.
  Check GRing.mulrA.
  rewrite pfwd1_pairC with (TY := X) (TX := Y).
  Check fdistX_RV2.
  Check fdistA_RV3.
  (* rewrite fdistX_RV2. *)
  set y := `Pr[ X = x].
  assert (y != 0) by exact H1.
  apply mult_div.
  assumption. *)
Admitted.

(* Lemma prob_cond_simplify: forall h t c,
  `Pr[ (fun u : UC * UT * UH => fH u.2 (fC u.1.1) (fT u.1.2 (fC u.1.1))) = h | 
      [% fun u : UC * UT * UH => fT u.1.2 (fC u.1.1), 
      fun u : UC * UT * UH => fC u.1.1] = (t, c) ] =
  `Pr[ (fun u : UC * UT * UH => fH u.2 c t) = h | 
      [% fun u : UC * UT * UH => fT u.1.2 (fC u.1.1), 
      fun u : UC * UT * UH => fC u.1.1] = (t, c) ]. *)


Lemma doint_equiv_with_confounder_prob: forall t c, 
  (Hnodefnint t) _|_ Tnodefn | Cnodefn ->
  `Pr[ Cnodefn = c ] != 0 ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ] 
      = `Pr[ (Hnodefnint t) = h | Cnodefn = c ]).
Proof.
  intros.
  pose proof (indep_then_cond_irrelevant_wcond UT UC UH P 
      Tnodefn Cnodefn (Hnodefnint t) H0 c H1 t H2 h).
  rewrite H3.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn.
  unfold C.
  unfold Hnodefnint.
  unfold Hinterv.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  unfold Tnodefn in H1.
  unfold T in H1.
  eapply eqr_divrMr. admit.
  rewrite <- div_mult. try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Ht : (fT a0.1 == t).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Admitted.

Lemma doint_equiv_with_confounder: forall t c, 
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  `Pr[ Cnodefn = c ] != 0 ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) :&: finset (Cnodefn @^-1 c) ] 
      = `E_[ (Hnodefnint t) | finset (Cnodefn @^-1 c) ].
Proof.
  intros.
Admitted.


End ThreeVarExample.


Section BackdoorAdjustment.

Lemma doint_prob:
  

End BackdoorAdjustment.