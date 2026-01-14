(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop. *)
From mathcomp Require Import ssreflect eqtype fintype bigop.
Require Import Reals.
(* From infotheo.information_theory Require Import entropy. *)
From infotheo.probability Require Import proba fdist fsdist jfdist_cond.
(*From infotheo.probability Require Import fdist proba fsdist.
From infotheo.probability Require Import jfdist_cond.*)
Require Import List.
Import ListNotations.
(* From infotheo.probability Require Import fdist fsdist jfdist_cond. *)
From mathcomp Require Import reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
(* From mathcomp Require boolp. *)
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
Definition T (p : UT * UH ): R :=
  fT p.1.
Definition Hinterv (p : UT * UH) t : R :=
  fH p.2 t.  
Definition H (p : UT * UH) : R :=
  fH p.2 (T p).
Definition nodefn : {RV P -> R * R} :=
  fun u => (T u , H u).
Definition nodefnint (t:R) : {RV P -> R * R} :=
  fun u => (t , Hinterv u t).
Definition Hnodefn : {RV P -> R} :=
  fun u => H u.
Definition Hnodefnint (t:R) : {RV P -> R} :=
  fun u => Hinterv u t.
Definition Tnodefn : {RV P -> R} :=
  fun u => T u.
Locate "'RV'".
Print RV_of.
Print RV.

Lemma mult_div: forall (a b: R),
  b != 0 ->
  a = a * b / b.
Proof.
  intros.
  rewrite <- GRing.mulrA.
  rewrite GRing.mulfV.
  Check GRing.mulr1.
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


Lemma indep_cond_irrelevant: 
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
  Check y.
  assert (y != 0) by exact H1.
  apply mult_div.
  assumption.
Qed.

Lemma prob_version:
  P |= (Hnodefnint 1) _|_ Tnodefn ->
  `Pr[ Tnodefn = 1 ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = 1] = `Pr[ (Hnodefnint 1) = a].
Proof.
  intros.
  pose proof (indep_cond_irrelevant UT UH P Tnodefn (Hnodefnint 1) H0).
  specialize (H2 1).
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
  case Ht : (fT a0.1 == 1).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Qed.

Lemma prob_to_exp_smaller:
  (forall a, `Pr[ Hnodefn = a | Tnodefn = 1] = `Pr[ (Hnodefnint 1) = a]) ->
  `E (Hnodefnint 1) = \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint 1)) r * `Pr[ Hnodefn = r | Tnodefn = 1 ].
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

Lemma same_preimg_helper_int:
  `Pr[ Tnodefn = 1 ] != 0 ->
  (forall a : R, `Pr[ Hnodefn = a | Tnodefn = 1 ] = `Pr[ (Hnodefnint 1) = a ]) ->
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint 1) | i
      \notin fin_img (A:=(UT * UH)%type) (B:=R) Hnodefn)
      i * `Pr[ Hnodefn = i | Tnodefn = 1 ] = 0.
Proof.
  intros.
  apply big1.
  intros.
  apply pfwd1_eq0 in H2.
  rewrite cpr_eqE.
  apply pfwd1_domin_RV2 with (TY := Tnodefn) (b := 1) in H2.
  rewrite H2.
  rewrite GRing.mulrA.
  rewrite GRing.mulr0.
  rewrite eqr_divrMr.
  rewrite GRing.mul0r.
  reflexivity.
  assumption.
Qed.

Lemma same_preimg_helper_noint:
  (forall a : R, `Pr[ Hnodefn = a | Tnodefn = 1 ] = `Pr[ (Hnodefnint 1) = a ]) ->
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) Hnodefn | i
      \notin fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint 1))
      i * `Pr[ Hnodefn = i | Tnodefn = 1 ] = 0.
Proof.
  intros.
  apply big1.
  intros.
  apply pfwd1_eq0 in H1.
  rewrite <- H0 in H1.
  rewrite H1.
  (* assert (forall r, (r \notin fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint 1)) ->
      `Pr[Hnodefn = r | Tnodefn = 1] = 0).
    intros.
    rewrite H0.
    rewrite /pfwd1.
    unlock.
    rewrite Pr_set0P.
    intros.
    Check fin_img.
    rewrite inE in H2.
    Check imsetP.
    assert (r \in fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint 1)).
      info_eauto.
      admit.
    exfalso.
    rewrite H3 in H1.
    simpl in H1.
    apply not_false_is_true.
    exact H1.
  
  Check big1.
  apply big1.
  intros.
  specialize (H1 i).
  apply H1 in H2.
  rewrite H2. *)
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

Lemma filtering_equal: forall (A B : seq R),
  uniq A ->
  uniq B ->
  perm_eq [seq i <- A | i  \in B] [seq i <- B | i  \in A].
Proof.
  intros.
  Check uniq_perm.
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

Lemma simplifying_summing: forall (f1 f2 : {RV (P) -> (R)}),
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f1 | i \in fin_img (A:=(UT * UH)%type) (B:=R) f2) i * `Pr[ Hnodefn = i | Tnodefn = 1 ] = 
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | i \in fin_img (A:=(UT * UH)%type) (B:=R) f1) i * `Pr[ Hnodefn = i | Tnodefn = 1 ].
Proof.
  intros.
  rewrite <- big_filter.
  assert (\sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      i \in fin_img (A:=(UT * UH)%type) (B:=R) f1)
      i * `Pr[ Hnodefn = i | Tnodefn = 1 ] = 
      \sum_(i <- [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1])
      i * `Pr[ Hnodefn = i | Tnodefn = 1 ]).
    rewrite big_filter.
    reflexivity.
  rewrite H0.
  clear H0.
  apply perm_big.
  apply filtering_equal.
  apply fin_img_uniq.
  apply fin_img_uniq.
Qed. 

Lemma same_preimg:
  `Pr[ Tnodefn = 1 ] != 0 ->
  (forall a, `Pr[ Hnodefn = a | Tnodefn = 1 ] = 
    `Pr[ (Hnodefnint 1) = a ]) ->
  \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) (Hnodefnint 1))
    r * `Pr[ Hnodefn = r | Tnodefn = 1 ] = 
    \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) Hnodefn)
    r * `Pr[ Hnodefn = r | Tnodefn = 1 ].
Proof.
  intros.
  Check bigID.
  rewrite (bigID (fun r => r \in fin_img (Hnodefn))).
  simpl.
  rewrite same_preimg_helper_int; cycle 1; try assumption.
  rewrite GRing.addr0.
  rewrite [in RHS] (bigID (fun r => r \in fin_img (Hnodefnint 1))).
  simpl.
  rewrite same_preimg_helper_noint; cycle 1; try assumption.
  rewrite GRing.addr0.
  rewrite simplifying_summing.
  reflexivity.
Qed.

Lemma prob_to_exp:
  `Pr[ Tnodefn = 1 ] != 0 ->
  (forall a, `Pr[ Hnodefn = a | Tnodefn = 1] = `Pr[ (Hnodefnint 1) = a]) ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 1) ] = `E (Hnodefnint 1).
Proof.
  intros.
  rewrite prob_to_exp_smaller; cycle 1. assumption.
  rewrite same_preimg; cycle 1. assumption. assumption.
  (* Search (?x * _ = ?x * _). *)
  rewrite /cEx.
  apply eq_big => r. reflexivity.
  intros.
  rewrite <- GRing.mulrA.
  rewrite /cPr_eq.
  rewrite /cPr.
  unlock.
  reflexivity.
Qed.


Lemma doint_equiv:
  P |= (Hnodefnint 1) _|_ Tnodefn ->
  `Pr[ Tnodefn = 1 ] != 0 ->
  (* `E_[ Hnodefn | Tnodefn = 1] = `E (Hnodefnint 1). *)
  `E_[ Hnodefn | finset (Tnodefn @^-1 1) ] = `E (Hnodefnint 1).
  (* `E_[ Hnodefn | Tnodefn = 1] = `E (Hnodefnint 1).
  `E_[ let (_, second) := nodefn in second | nodefn.1 = 1].
  `E_[ nodefn | nodefn.1 = 1] = `E[ (nodefnint 1) ]. *)
Proof.
  intros.
  pose proof (prob_version H0 H1).
  pose proof (prob_to_exp H1 H2).
  assumption.
Qed.

Lemma doint_equiv_not1: forall (t : R), 
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) ] = `E (Hnodefnint t).
Proof.
Admitted.

Lemma doint_equiv_wo_indp: forall (t : R), 
  (* I'm not sure how to state that UH, UT are indep? I think it might be implicit in my sample space definition? *)
  `Pr[ Tnodefn = t ] != 0 ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) ] = `E (Hnodefnint t).
Proof.
Admitted.

End TwoVarExample.


Section ThreeVarExample.

Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UC * UT) * UH).

Variable fC : UC -> R.
Variable fT : UT -> R -> R.
Variable fH : UH -> R -> R -> R.

Definition C (p: UC * UT * UH) : R :=
  fC p.1.1.
Definition T (p : UC * UT * UH ): R :=
  fT p.1.2 (C p).
Definition H (p : UC * UT * UH) : R :=
  fH p.2 (C p) (T p).
Definition Hin (p : UC * UT * UH) t : R :=
  fH p.2 (C p) t.  

Definition Cnodefn : {RV P -> R} :=
  fun u => C u.
Definition Tnodefn : {RV P -> R} :=
  fun u => T u.
Definition Hnodefn : {RV P -> R} :=
  fun u => H u.
Definition Hnodefnint (t: R) : {RV P -> R}:= 
  fun u => Hint u t.


Lemma doint_equiv_with_confounder: forall t c, 
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  `Pr[ Cnodefn = c ] != 0 ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) & finset (Cnodefn @^-1 c) ] = `E_[ (Hnodefnint t) | finset (Cnodefn @^-1 c) ].
Proof.
Admitted.


End ThreeVarExample.