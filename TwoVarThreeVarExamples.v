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

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(*
OUTLINE:
Graph T -> H (Section TwoVarExample)
- *prob_version_wo_indp* states that P[H|T] = P[H|do(T)],
  assuming that some probabilities are non-zero, and that
  unobserved distributions are independent.
  In other words, under interventional treatment, and
  observation of the treatement health outcomes are the
  same (so a RCT where we assign T would be valid for
  learning the interventional probability).
  This is basically complete, the only missing lemma is:
  + *inde_RV_comp*, which is pulled directly from the 
  infotheo library (and proven there), but for whatever 
  reason I'm struggling to access it.
- *doint_equiv_wo_indp* states that E[H|T] = E[H|do(T)] 
  with the same assumptions as in the probability case, and 
  also with the assumption that the function that maps the 
  outcomes to real numbers is injective.
  Work left:
  + *change_to_R_version* is not proven. I'm running into
    issues with type mismatches (realType and finType). This
    seems like it is potentially rather difficult to fix,
    since the type mismatch means I can't use their lemmas.
Graph O -> T -> H, O -> H (confounder, Section ThreeVarConfounderExample)
- doint_equiv_with_confounder_prob states that
  P[H|T,O] = P[H|do(T),O], but has the assumption
  (Hnodefnint t) _|_ Tnodefn | Cnodefn, as well as some
  assumptions about certain probabilities being non-zero.
  Almost done. Work left:
  + 2 lemmas that assert basic arithmetic facts, 
    *zero_div_zero* and *div_num_and_denom*
- doint_equiv_with_confounder_prob_wo_indp states
  the same thing, but now instead assumes that
  UT, UT, UO are mutually independent instead of the
  independence assumption in the previous lemma.
  Work left:
  + Lots of gaps between this proof and the one above.
Graph T -> H, T -> O <- H (collider) 
- Done
Graph T -> O -> H, T -> H (mediator, Section ThreeVarColliderExample)
- Done
General case
- Will be done in new file but rough sketch is here:
  Theorem:
    set Z d-separates H and T ->
    underlying variables for set Z, H, T are all mutually independent ->
    P[H|T,Z] = P[H|do(T),Z].
  This is the general theorem that states that if we
  satisfy the backdoor criterion, then we can use
  observational probabilities to learn about interventional
  probabilities.

  Lemma:
    underlying variables for set Z, H, T are all mutually independent ->
    T _|_ H | Z
  
  Lemma:
    T _|_ H | Z ->
    Tnodefn _|_ Hnodefnint | Znodefns

  Lemma:
    T _|_ H | Z ->
    P[Z] != 0 -> P [T|Z] != 0 ->
    P [H | Z] = P [H | T, Z].
*)

Section TwoVarExample. (* Graph: T -> H *)

Context {R : realType}.
Variables (UT UH : finType).
Variables (outcomes: finType).
Variable P : R.-fdist (UT * UH).
(* Variables (UTRV : {RV P -> UT}) (UHRV : {RV P -> UH}). *)
Variable fT : UT -> outcomes.
Variable fH : UH -> outcomes -> outcomes.
Let T (p : UT * UH ): outcomes :=
  fT p.1.
Let Hinterv (p : UT * UH) t : outcomes :=
  fH p.2 t. 
Let H (p : UT * UH) : outcomes :=
  fH p.2 (T p).
(* Let nodefn : {RV P -> R * R} :=
  fun u => (T u , H u).
Let nodefnint (t:R) : {RV P -> R * R} :=
  fun u => (t , Hinterv u t). *)
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Hnodefnint (t:outcomes) : {RV P -> outcomes} :=
  fun u => Hinterv u t.
(* Let Hnodefnint (t:outcomes) : RV_of P (Phant (UT * UH)) (Phant outcomes) :=
  fun u => Hinterv u t. *)
Let Tnodefn : {RV P -> outcomes} :=  (*T.*)
  fun u => T u.
(* Locate "'RV'".
Print RV_of.
Print RV. *)
Variable fn_outcomes_R : outcomes -> R.
Let RHnodefn : {RV P -> R} :=
  fn_outcomes_R `o Hnodefn.
Let RHnodefnint (t:outcomes) : {RV P -> R} :=
  fn_outcomes_R `o (Hnodefnint t).
Let RTnodefn : {RV P -> R} :=
  fn_outcomes_R `o Tnodefn.
Let UTRV: {RV P -> UT} :=
  fun u => u.1.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.

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

(* Alternate independence definition *)
Lemma indep_then_cond_irrelevant: 
    forall (TX: finType) (TZ: finType) (P: R.-fdist (TX*TZ) ) 
    (X: {RV P -> outcomes}) (Z: {RV P -> outcomes}),
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
  apply esym.
  apply mult_div.
  assumption.
Qed.

(* Probability lemma with stronger assumption than desired *)
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
  rewrite div_mult; try assumption.

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

(* If the unobserved terms are independent, then the nodefns are
   independent on the intervention graph *)
Lemma indep_implication: forall t,
  P |= UHRV _|_ UTRV ->
  P |= (Hnodefnint t) _|_ Tnodefn.
Proof.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  (* apply inde_RV_comp. *)
  (* Check (Hnodefnint t). *)
  (* pose proof (inde_RV_comp _ _ UH UT _ _ UHRV UTRV (fun u => fH u t) (fun u => fT u) H0). *)
  pose proof (inde_RV_comp (fun u => fH u t) (fun u => fT u) H0).
  unfold comp_RV in H1. 
  unfold UTRV in H1.
  unfold UHRV in H1.
  apply H1.
Qed.

(* The probability lemma I want.
   If the unobserved factors are independent, and some
   probability isn't 0, then if we are observe T then the
   probability is equal to if we intervene on T. We denote
   P[H=a|do(T=t)] as P[Hint=a] since if we write out 
   probabilities, do(T=t) change the node functions depending
   on T, which in this case is H, but doesn't actually have an
   extra probability associated with doing (T=t). *)
Lemma prob_version_wo_indp: forall (t : outcomes), 
  P |= UHRV _|_ UTRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  apply prob_version.
  apply indep_implication.
  assumption.
  assumption.
Qed.

(* Helper lemma without much intrinsic meaning. *)
Lemma prob_as_sum_of_eq: forall t, 
  (forall a, `Pr[ RHnodefn = a | Tnodefn = t ] = `Pr[ (RHnodefnint t) = a]) ->
  `E (RHnodefnint t) = \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) (RHnodefnint t)) 
      r * `Pr[ RHnodefn = r | Tnodefn = t ].
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

(* Helper lemma without much intrinsic meaning. *)
Lemma same_preimg_helper_int_general: forall t, 
  `Pr[ Tnodefn = t ] != 0 ->
  (forall a : R, `Pr[ RHnodefn = a | Tnodefn = t ] = `Pr[ (RHnodefnint t) = a ]) ->
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) (RHnodefnint t) | i
      \notin fin_img (A:=(UT * UH)%type) (B:=R) RHnodefn)
      i * `Pr[ RHnodefn = i | Tnodefn = t ] = 0.
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

(* Helper lemma without much intrinsic meaning. *)
Lemma same_preimg_helper_noint_general: forall t, 
  (forall a : R, `Pr[ RHnodefn = a | Tnodefn = t ] = `Pr[ (RHnodefnint t) = a ]) ->
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) RHnodefn | i
      \notin fin_img (A:=(UT * UH)%type) (B:=R) (RHnodefnint t))
      i * `Pr[ RHnodefn = i | Tnodefn = t ] = 0.
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

(* Helper lemma.
   fin_img is a set with no repeated elements. *)
Lemma fin_img_uniq: forall f1,
  uniq (fin_img (A:=(UT * UH)%type) (B:=R) f1).
Proof.
  intros.
  unfold fin_img.
  apply undup_uniq.
Qed.

(* Helper lemma.
   Given two sets without repeats ordering based on one
   and conditioning on the other results in the same set
   of elements regradless of which you pick for ordering
   vs conditioning. *)
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

(* Helper lemma without much intrinsic meaning. *)
Lemma sums_with_diff_index_forms: forall t (f1 f2 : {RV (P) -> (R)}),
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f1 | i \in fin_img (A:=(UT * UH)%type) (B:=R) f2) i * `Pr[ RHnodefn = i | Tnodefn = t ] = 
  \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | i \in fin_img (A:=(UT * UH)%type) (B:=R) f1) i * `Pr[ RHnodefn = i | Tnodefn = t ].
Proof.
  intros.
  rewrite <- big_filter.
  assert (\sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      i \in fin_img (A:=(UT * UH)%type) (B:=R) f1)
      i * `Pr[ RHnodefn = i | Tnodefn = t ] = 
      \sum_(i <- [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1])
      i * `Pr[ RHnodefn = i | Tnodefn = t ]).
    rewrite big_filter.
    reflexivity.
  rewrite H0.
  clear H0.
  apply perm_big.
  apply seq_cond_or_cond_seq.
  apply fin_img_uniq.
  apply fin_img_uniq.
Qed. 

(* Helper lemma without much intrinsic meaning. 
   (Rewrite what we are summing over.) *)
Lemma sums_with_int_and_noint_index: forall t, 
  `Pr[ Tnodefn = t ] != 0 ->
  (forall a, `Pr[ RHnodefn = a | Tnodefn = t ] = `Pr[ (RHnodefnint t) = a ]) ->
  \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) (RHnodefnint t))
    r * `Pr[ RHnodefn = r | Tnodefn = t ] = 
    \sum_(r <- fin_img (A:=(UT * UH)%type) (B:=R) RHnodefn)
    r * `Pr[ RHnodefn = r | Tnodefn = t ].
Proof.
  intros.
  Check bigID.
  rewrite (bigID (fun r => r \in fin_img (RHnodefn))).
  simpl.
  rewrite same_preimg_helper_int_general; cycle 1; try assumption.
  rewrite GRing.addr0.
  rewrite [in RHS] (bigID (fun r => r \in fin_img (RHnodefnint t))).
  simpl.
  rewrite same_preimg_helper_noint_general; cycle 1; try assumption.
  rewrite GRing.addr0.
  rewrite sums_with_diff_index_forms.
  reflexivity.
Qed.

(* The lemma says that if the probabilites match at each
   point, then the expectations are the same. The previous
   lemmas are helper lemmas to deal with the summations 
   in this lemma. *)
Lemma prob_to_exp: forall t,
  `Pr[ Tnodefn = t ] != 0 ->
  (forall a, `Pr[ RHnodefn = a | Tnodefn = t] = `Pr[ (RHnodefnint t) = a]) ->
  `E_[ RHnodefn | finset (Tnodefn @^-1 t) ] = `E (RHnodefnint t).
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

(* EXPECATIONS.
   Since for expectations I need the outcomes to be eqType
   instead of finType, I need a lemma that lets me convert
   between these two. RHnodefn/RHnodefnint is just Hnodefn/
   Hnodefnint but mapped to the reals. *)
Lemma change_to_R_version: forall t : outcomes,
  injective fn_outcomes_R ->
  P |= Hnodefnint t _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  (forall a : outcomes, `Pr[ Hnodefn = a | Tnodefn = t ] =
    `Pr[ (Hnodefnint t) = a ]) ->
  forall b: R, `Pr[ RHnodefn = b | Tnodefn = t ] = 
    `Pr[ (RHnodefnint t) = b ].
Proof.
  intros.
  unfold RHnodefn.
  unfold RHnodefnint.
  destruct (classic  (exists a, fn_outcomes_R a = b)) as [ [a Ha] | Hnotin ].
  rewrite <- Ha.
  Check pfwd1_comp.
  admit.
  (* rewrite [in RHS] pfwd1_comp. *)
  (* pose proof (pfwd1_comp (Hnodefnint t) a H0 fn_outcomes_R a H0). *)
  (* pose proof (pfwd1_comp (Hnodefnint t) _ H0 fn_outcomes_R a H0). *)
  (* pose proof (pfwd1_comp _ _ _ _ (Hnodefnint t) fn_outcomes_R a H0). *)
  (* rewrite [in RHS] pfwd1_comp. *)
  (* rewrite pfwd1_comp. *)
  rewrite cpr_eqE.
  rewrite eqr_divrMr; try assumption.

  (* specialize (H3 (inv fn_outcomes_R b)). *)
  (* rewrite pfwd1_comp. *)
  (* rewrite pr_in_comp in H3. *)
Admitted.

(* EXPECTATIONS.
   Same lemma as before except for expectations instead
   of probabilities. 
   Says that given indp node fns, the interventional and
   observational expectations are the same. *)
Lemma doint_equiv: forall t, (* T -> H *)
  injective fn_outcomes_R ->
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 -> 
  `E_[ RHnodefn | finset (Tnodefn @^-1 t) ] = `E (RHnodefnint t).
Proof.
  intros.
  apply prob_to_exp. assumption.
  apply change_to_R_version; try assumption.
  (* Check prob_version. *)
  apply prob_version. assumption.
  assumption.
Qed.

(* EXPECTATIONS.
   Expectation Lemma stating that if the unobserved factors
   are independent, then the expectations with intervention
   or observation of T are equivalent. *)
Lemma doint_equiv_wo_assumption: forall t, (* T -> H *)
  injective fn_outcomes_R ->
  P |= UHRV _|_ UTRV ->
  `Pr[ Tnodefn = t ] != 0 -> 
  `E_[ RHnodefn | finset (Tnodefn @^-1 t) ] = `E (RHnodefnint t).
Proof.
  intros.
  apply doint_equiv; try assumption.
  apply indep_implication.
  assumption.
Qed.

End TwoVarExample.





Section ThreeVarConfounderExample. (* C -> T -> H, C -> H *)

Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UC * UT) * UH).
Variable outcomes: finType.

Variable fC : UC -> outcomes.
Variable fT : UT -> outcomes -> outcomes.
Variable fH : UH -> outcomes -> outcomes -> outcomes.

Let C (p: UC * UT * UH) : outcomes :=
  fC p.1.1.
Let T (p : UC * UT * UH ): outcomes :=
  fT p.1.2 (C p).
Let H (p : UC * UT * UH) : outcomes :=
  fH p.2 (C p) (T p).
Let Hinterv (p : UC * UT * UH) t : outcomes :=
  fH p.2 (C p) t.  

Let Cnodefn : {RV P -> outcomes} :=
  fun u => C u.
Let Tnodefn : {RV P -> outcomes} :=
  fun u => T u.
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Hnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Hinterv u t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.

Lemma div_num_and_denom: forall (a b c d : R),
  b != 0 ->
  a / b / (c / b) = a / c.
Proof.
  intros.
  Check GRing.mulrC.
  Check GRing.mulrVK.
  (* rewrite GRing.divrA. *)
  rewrite GRing.mulrC.
  (* rewrite GRing.divrA. *)
  (* rewrite GRing.mulrVK. *)
  (* nra. *)
Admitted.

Lemma zero_div_zero: forall (a : R),
  a != 0  ->
  0 / a = 0.
Proof.
Admitted.

Lemma mult_by_zero_right: forall (a : R),
  a * 0 = 0.
Proof.
  intros.
Admitted.

Lemma mult_by_zero_left: forall (a : R),
  0 * a = 0.
Proof.
  intros.
Admitted.

(* Important Lemma that says that if the thing you're
   conditioning on in a probability is 0, the entire 
   conditional probability is zero. Is used to deal
   with annyoing P[Z=b] != 0 cases throughout proofs. *)
Lemma cpr_eq0_denom: forall {TA TD: finType}
  (X : {RV P -> TA}) (Z: {RV P -> TD}) a b,
  `Pr[Z = b] = 0 ->
  `Pr[X = a | Z = b] = 0.
Proof.
  intros.
  rewrite cPr_eq_finType.
  apply cPr_eq0P.
  rewrite setIC. 
  apply Pr_domin_setI.
  (* rewrite <- H0. *)

  (* rewrite pfwd1E.
  rewrite /preim in H0.
  rewrite /= in H0.
  rewrite /Pr. *)

  rewrite <- cpr_eq_unit_RV in H0.
  rewrite cPr_eq_finType in H0.
  apply cPr_eq0P in H0.
  assert (Z @^-1: [set b] :&: unit_RV P @^-1: [set tt] = Z @^-1: [set b]).
    simpl.
    apply/setP => u.
    rewrite !inE.
    destruct (Z u == b).
    simpl.
    unfold unit_RV.
    rewrite eq_refl.
    reflexivity.
    simpl.
    reflexivity.
  rewrite <- H0.
  rewrite H1.
  reflexivity.

  (* rewrite /Pr.

  unfold unit_RV in H0.
  simpl in H0. *)

  (* rewrite cPr_eq_def in H0. 
  rewrite cPr_eq_finType in H0.
  
  rewrite pfwd1E in H0.
  simpl in H0. *)

Qed.

(* Another definition of indepedence. I wrote it because I needed
   this for the 2 variable case, but I actually think it was already
   defined for condition indepence in cinde_alt, and I should change
   this to cinde_alt at some point instead. *)
Lemma indep_then_cond_irrelevant_wcond: 
  forall (TX TY TZ: finType) (P: R.-fdist ((TY*TX)*TZ) ) (X Y Z: {RV P -> outcomes}),
  Z _|_ X | Y->
  forall y, `Pr[ Y = y ] != 0 ->
  forall x, `Pr[ X = x | Y = y ] != 0 ->
  forall z, `Pr[ Z = z | Y = y] = `Pr[ Z = z | [%X, Y] = (x, y) ].
Proof.
  (* Check cinde_alt. *)
  intros.
  unfold cinde_RV in H0.
  specialize (H0 z x y).
  rewrite [in RHS] cpr_eqE.
  apply eqr_divrMr in H0; cycle 1. assumption.
  rewrite <- H0.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite pfwd1_pairA.
  set `Pr[ [% Z, X, Y] = (z, x, y) ] as Pxyz.
  rewrite div_num_and_denom.
  reflexivity.
  assumption.
  assumption.
Qed.

(* Lemma prob_cond_simplify: forall h t c,
  `Pr[ (fun u : UC * UT * UH => fH u.2 (fC u.1.1) (fT u.1.2 (fC u.1.1))) = h | 
      [% fun u : UC * UT * UH => fT u.1.2 (fC u.1.1), 
      fun u : UC * UT * UH => fC u.1.1] = (t, c) ] =
  `Pr[ (fun u : UC * UT * UH => fH u.2 c t) = h | 
      [% fun u : UC * UT * UH => fT u.1.2 (fC u.1.1), 
      fun u : UC * UT * UH => fC u.1.1] = (t, c) ]. *)

Lemma cond_then_joint_zero: forall (A B : {RV P -> outcomes}) (a b : outcomes), 
  `Pr[ A = a ] != 0 ->
  `Pr[ B = b | A = a ] != 0 ->
  `Pr[ [% B, A] = (b, a) ] != 0.
Proof.
  intros.
  rewrite cpr_eqE in H1.
  case PBA : (`Pr[ [% B, A] = (b, a) ] == 0).
  move/eqP in PBA.
  rewrite PBA in H1.
  pose proof (zero_div_zero `Pr[ A = a ] H0).
  rewrite H2 in H1.
  rewrite eq_refl in H1.
  exact H1.
  rewrite <- PBA.
  move/eqP in PBA.
  apply/negP.
  move/eqP.
  assumption.
Qed.

(* If we have that nodefunctions are independent, then on 
   the graph
   C -> T -> H, C -> H
   we get that once we condition on C, the observational
   and interventional probability distributions for H
   are the same.
   This is a precursor to the stronger theorem that instead
   assumes the unobserved variables are mutually independent. *)
Lemma doint_equiv_with_confounder_prob: forall t c, 
  (Hnodefnint t) _|_ Tnodefn | Cnodefn ->
  `Pr[ Cnodefn = c ] != 0 ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ] 
      = `Pr[ (Hnodefnint t) = h | Cnodefn = c ]).
Proof.
  intros.
  (* Check cinde_alt.
  assert (`Pr[ [% Tnodefn, Cnodefn] = (t, c)] != 0).
    admit.
  pose proof (cinde_alt c H0 H3). *)
  pose proof (indep_then_cond_irrelevant_wcond UT UC UH P 
      Tnodefn Cnodefn (Hnodefnint t) H0 c H1 t H2 h).
  rewrite H3.
  
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  eapply eqr_divrMr.
  apply cond_then_joint_zero; assumption.
  rewrite div_mult.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold C.
  (* rewrite cpr_eqE.
  rewrite cpr_eqE. *)
  unfold Tnodefn in H1.
  unfold T in H1.
  (* eapply eqr_divrMr. *)
    (* rewrite cpr_eqE in H2. *)
    (* admit. *)
  (* rewrite div_mult. try assumption. *)

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Hc : (fC a.1.1 == c).
  - move/eqP : Hc => Hc.
    rewrite Hc.
    case Ht : (fT a.1.2 c == t).
    + move/eqP : Ht => Ht.
      rewrite Ht.
      reflexivity.
    + rewrite !andbF.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
  apply cond_then_joint_zero; assumption.
Qed.

(* The library only seems to have mutually independent
   events and not RV, although I'm maybe missing something. *)
Definition mutual_indep_three {X' Y' Z': finType}
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}) := 
  (forall x y z,
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [%[% X, Y], Z] = ((x,y), z)]) /\ 
    P |= X _|_ Y /\ P |= Y _|_ Z /\ P |= X _|_ Z.
    
Check mutual_indeE. (* For events, will need something for RVs. *)
(* Definition mutual_inde_RV := forall k, @kwise_inde R A I k.+1 d E. *)

(* This lemma states that mutual independence gives us
   conditional independence.
   This lemma needs a pesky non-zero assumption, and I'm not
   sure how to get rid of it. *)
Lemma mut_indp_cond_indp : forall {X' Y' Z': finType}
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}),
  mutual_indep_three X Y Z ->
  (* (forall c', `Pr[ Z = c' ] != 0) -> *)
  X _|_ Y | Z.
Proof.
  intros.
  unfold mutual_indep_three in H0.
  unfold cinde_RV.
  intros.
  (* specialize (H1 c). *)
  destruct H0 as [Indp3 [IndpXY [IndpYZ IndpXZ]]].
  specialize (Indp3 a b c).
  unfold inde_RV in IndpXY.
  unfold inde_RV in IndpXZ.
  unfold inde_RV in IndpYZ.
  specialize (IndpXY a b).
  specialize (IndpXZ a c).
  specialize (IndpYZ b c).
  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    Check cpr_eq0_denom.
    move/eqP: Hzero => H0.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_by_zero_left.
    reflexivity.
  rewrite !cpr_eqE.
  rewrite IndpYZ.
  rewrite IndpXZ.
  rewrite mult_div.
  rewrite mult_div.
  rewrite eqr_divrMr.
  rewrite Indp3.
  reflexivity.
  (* all: assumption. *)
  all: assumption.
(* Qed. *)
Qed.

(* Lemma that states that if there is no value d such
   that h d = z, then we also know that the RV h `o Z
   can also never be z. *)
Lemma no_fn_val_prob_zero : forall {TD UD : finType}
  (Z: {RV P -> TD}) (h : TD -> UD) z,
  ~ (exists d : TD, h d = z) ->
  `Pr[ (h `o  Z) = z ] = 0.
Proof.
  intros.
  apply pfwd1_eq0.
  rewrite /fin_img.
  apply /negP.
  rewrite mem_undup.
  move /mapP.
  move => Hhoz.
  move: Hhoz => [x Hx Hhoz].
  unfold comp_RV in Hhoz.
  assert (exists d : TD, h d = z).
    exists (Z x).
    rewrite Hhoz.
    reflexivity.
  contradiction.
Qed. 

(* REDUNDANT.
   Says that three mutually indp events are still indp*)
Lemma mut_indp_fn :
  forall {TA TB TD UA UB UD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD})
  (f : TA -> UA) (g : TB -> UB) (h : TD -> UD),
  injective f ->
  injective g ->
  injective h ->
  mutual_indep_three X Y Z ->
  mutual_indep_three (f `o X) (g `o Y) (h `o Z).
Proof.
  intros.
  unfold mutual_indep_three.
  intros.
  unfold mutual_indep_three in H3.
  destruct H3 as [Indp3 [IndpXY [IndpYZ IndpXZ]]].
  split.

  intros.
  destruct (classic  (exists a, f a = x)) as [ [a Hf] | Hfnotin ].
  destruct (classic  (exists b, g b = y)) as [ [b Hg] | Hgnotin ].
  destruct (classic  (exists d, h d = z)) as [ [d Hh] | Hhnotin ].
  specialize (Indp3 a b d).
  rewrite <- Hf.
  rewrite <- Hg.
  rewrite <- Hh.
  rewrite !pfwd1_comp; try assumption.
  rewrite -> fox_in_paired_RV1 with (x:=a).
  rewrite <- pfwd1_pairA.
  rewrite <- pfwd1_pairCA.
  rewrite -> pfwd1_pairA.
  rewrite -> fox_in_paired_RV1 with (x:=b).
  rewrite pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite -> pfwd1_pairA.
  rewrite -> fox_in_paired_RV1 with (x:=d).
  rewrite <- pfwd1_pairA.
  rewrite <- pfwd1_pairCA.
  rewrite -> pfwd1_pairA.
  rewrite -> pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite -> pfwd1_pairA.
  assumption.
  rewrite pfwd1_comp.
  reflexivity.
  assumption.
  rewrite pfwd1_comp.
  reflexivity.
  assumption.
  rewrite pfwd1_comp.
  reflexivity.
  assumption.

  pose proof (no_fn_val_prob_zero Z h z Hhnotin).
  rewrite H3.
  rewrite pfwd1_pairC.
  rewrite pfwd1_domin_RV2.
  rewrite mult_by_zero_right.
  reflexivity.
  simpl.
  assumption.

  pose proof (no_fn_val_prob_zero Y g y Hgnotin).
  rewrite H3.
  rewrite <- pfwd1_pairA.
  rewrite <- pfwd1_pairCA.
  rewrite pfwd1_domin_RV2.
  rewrite mult_by_zero_right.
  rewrite mult_by_zero_left.
  reflexivity.
  assumption.

  pose proof (no_fn_val_prob_zero X f x Hfnotin).
  rewrite H3.
  rewrite pfwd1_domin_RV2.
  rewrite mult_by_zero_left.
  rewrite mult_by_zero_left.
  reflexivity.
  rewrite pfwd1_domin_RV2.
  reflexivity.
  assumption.

  split; try split.
  all : apply inde_RV_comp; assumption.
Qed.

(* Lemma inde_RV_comp (TA TB UA UB : finType) (X : {RV P -> TA}) (Y : {RV P -> TB})
    (f : TA -> UA) (g : TB -> UB) :
  P |= X _|_ Y -> P|= (f `o X) _|_ (g `o Y).
Proof.
move=> /inde_RVP inde_XY; apply/inde_RVP => E F.
by rewrite (pr_in_comp' f) (pr_in_comp' g) -inde_XY -preimsetX -pr_in_comp'.
Qed. *)


(* If the unobserved factors are independent, then the
   nodefunctions are independent. *)
(* Lemma unobv_indp_fn_indp: 
  (* (UH, UC) _|_ (UT, UC) | UC *)
  UHRV _|_ UTRV | UCRV ->
  (forall t, (Hnodefnint t) _|_ Tnodefn | Cnodefn).
Proof.
  intros.
  pose proof (inde_RV_comp_cond _ _ _ _ _ _ UHRV UTRV UCRV 
      (fun u => fH u (fC u) t) (fun u => fT u) (fun u => H0).
  apply inde_RV_comp_cond.
  Check cinde_alt.
  unfold cinde_RV.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn. 
  unfold C.
  Check inde_RV_comp.
  unfold cinde_RV in H0.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Hc : (fC a.1.1 == c).
  - move/eqP : Hc => Hc.
    rewrite Hc.
    case Ht : (fT a.1.2 c == t).
    + move/eqP : Ht => Ht.
      rewrite Ht.
      reflexivity.
    + rewrite !andbF.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
  apply cond_then_joint_zero; assumption.


  pose proof (inde_RV_comp ()).

  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  (* apply inde_RV_comp. *)
  (* Check (Hnodefnint t). *)
  pose proof (inde_RV_comp UH UT _ _ UHRV UTRV (fun u => fH u t) (fun u => fT u) H0).
  unfold comp_RV in H1. 
  unfold UTRV in H1.
  unfold UHRV in H1.
  apply H1.
Admitted. *)

Lemma same_RV_two_vals: forall {TA: finType} (X : {RV P -> TA}) a b,
  b <> a ->
  `Pr[ [% X, X] = (a, b)] = 0.
Proof.
  intros.
  rewrite pfwd1_eq0.
  reflexivity.
  rewrite /fin_img.
  apply /negP.
  rewrite mem_undup.
  move /mapP.
  move => Hpair.
  move: Hpair => [x Hx Hpair].
  unfold RV2 in Hpair.
  inversion Hpair.
  rewrite H3 in H0.
  rewrite H2 in H0.
  contradiction.
Qed.

Lemma can_move_cond: forall {TA TD: finType}
  (X : {RV P -> TA}) (Z: {RV P -> TD}) a c,
  (* `Pr[ Z = c ] != 0 ->  *)
  `Pr[ [% X, Z] = (a, c) | Z = c ] = `Pr[ X = a | Z = c].
Proof.
  intros.
  
  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    Check cpr_eq0_denom.
    move/eqP: Hzero => H0.
    rewrite !cpr_eq0_denom; try assumption.
    reflexivity.

  rewrite cpr_eqE.
  simpl.
  rewrite cpr_eqE.
  eapply eqr_divrMr.
  assumption.
  rewrite div_mult.

  rewrite pfwd1E. rewrite pfwd1E.
  rewrite /Pr.
  apply eq_bigl => a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite <- andbA.
  rewrite Bool.andb_diag.
  reflexivity.
  assumption.
Qed.

(* Lemma can_move_cond': forall {TA TD: finType}
  (X : {RV P -> TA}) (Z: {RV P -> TD}) a c,
  `Pr[ [% Z, X] = (c, a) | Z = c ] = `Pr[ X = a | Z = c].
Proof.
  intros.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  eapply eqr_divrMr.
  admit.
  rewrite div_mult.
  admit.
  admit.
Admitted. *)

Lemma cond_not_match_arg: forall {TA TD: finType}
  (X : {RV P -> TA}) (Z: {RV P -> TD}) a b c,
  b <> c ->
  (* `Pr[ Z = c ] != 0 -> *)
  `Pr[ [% X, Z] = (a, b) | Z = c ] = 0.
Proof.
  intros.
  
  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom; try assumption.
    reflexivity.

  rewrite cpr_eqE.
  eapply eqr_divrMr.
  assumption.
  rewrite mult_by_zero_left.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1.
  apply same_RV_two_vals.
  apply nesym.
  assumption.
Qed.

Lemma indp_not_affected_by_adding_cond: forall {TA TB TD: finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD}),
  X _|_ Y | Z ->
  [% X, Z] _|_ [% Y, Z ] | Z. 
Proof.
  intros.
  unfold cinde_RV.
  intros.
  destruct a as [a a2].
  destruct b as [b b2].

  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_by_zero_left.
    reflexivity.

  destruct (a2 =P c) as [Heq1 | Hneq1].
  destruct (b2 =P c) as [Heq2 | Hneq2].
  rewrite Heq1.
  rewrite Heq2.
  rewrite can_move_cond.
  rewrite can_move_cond.

  unfold cinde_RV in H0.
  specialize (H0 a b c).
  rewrite <- H0.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite eqr_divrMr.
  rewrite div_mult.

  rewrite pfwd1E. 
  rewrite pfwd1E.
  rewrite /Pr.
  apply eq_bigl => a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  rewrite !andbA.
  rewrite <- andbA.
  rewrite Bool.andb_diag.
  destruct (X a0 == a).
  destruct (Y a0 == b).
  destruct (Z a0 == c).
  all: simpl.
  reflexivity.
  reflexivity.
  destruct (Z a0 == c).
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  reflexivity.
  assumption.
  assumption.

  inversion Heq1.
  clear H1.
  rewrite can_move_cond.
  rewrite cond_not_match_arg; try assumption.
  rewrite cpr_eqE.
  rewrite -> pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite -> pfwd1_pairA.
  rewrite -> pfwd1_pairA. 
  rewrite mult_by_zero_right.
  rewrite eqr_divrMr.
  rewrite mult_by_zero_left.
  rewrite <- pfwd1_pairA.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1 with (TX := Z) (TY := [% X, Z, [% Y, Z]]).
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1 with (TX := X) (TY := [% Z, [% Y, Z]]).
  rewrite pfwd1_pairCA.
  apply pfwd1_domin_RV1 with (TX := Y) (TY := [% Z, Z]).
  apply same_RV_two_vals.
  assumption.
  assumption.
  
  rewrite cond_not_match_arg; try assumption.
  rewrite mult_by_zero_left.
  rewrite cpr_eqE.
  rewrite eqr_divrMr.
  rewrite mult_by_zero_left.
  rewrite <- pfwd1_pairA.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1 with (TX := X) (TY := [% Z, [% Y, Z, Z]]).
  rewrite -> pfwd1_pairCA.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1.
  apply pfwd1_domin_RV1.
  apply same_RV_two_vals.
  apply nesym.
  assumption.
  assumption.

  (* rewrite pfwd1_eq0.
  reflexivity.
  simpl.

  Check pfwd1_domin_RV2.


  (* rewrite -> pfwd1_pairC with (TY := Z) (TX := [% [% X, Z], Y, Z]). *)
  (* rewrite -> pfwd1_pairA with (TX := Z) (TY := [% X, Z]) (TZ := [% Y, Z]). *)
  (* rewrite -> pfwd1_pairA with (TX := [% X, Z]) (TY := Y) (TZ := Z). *)
  
  Check cPr_eq_id. *)
Qed.

(* Lemma mut_indp_fn_cond_fns :
  forall {TA TB TD UA UB UD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD})
  (f : TA -> UA) (g : TB -> UB) (h : TD -> UD),
  injective f ->
  injective g ->
  injective h ->
  mutual_indep_three X Y Z ->
  (f `o [% X, Z] ) _|_ (g `o [% Y, Z] ) | (h `o Z). *)

(* Lemma inj_double_map: forall {TA TD UA UD : finType}
  (f : (TA*TD) -> UA) (h : TD -> UD),
  injective f ->
  injective h ->
  injective (fun (u: TA*TD) (v: TD) => (f u, h v)).
Proof.
Admitted. *)

(* Lemma pr_double_map:
  forall {TA TD UA UD : finType}
  (X : {RV P -> TA}) (Z: {RV P -> TD})
  (f : TA -> UA) (h : TD -> UD) x z,
  Pr[ [% f `o  X, h `o  Z] = (f x, h z) ] =
  Pr[ (fun x => (f `o x.1, h `o x.2)) `o [% X, Z] = 
      ((fun x => (f `o x.1, h `o x.2)) (x, z))]. *)

      (* pfwd1_comp
     : forall (U : finType) (P0 : {fdist U}) (A B : finType)
(X0 : {RV (P0) -> (A)}) (f0 : A -> B) (a0 : A),
injective f0 -> `Pr[ (f0 `o  X0) = (f0 a0) ] =
`Pr[ X0 = a0 ] *)

Lemma pfwd1_comp_in_joint: 
  forall {TA TD UA UD : finType}
  (X : {RV P -> TA}) (Z: {RV P -> TD})
  (f : TA -> UA) (x: TA) z,
  injective f ->
  `Pr[ [% (f `o  X), Z] = ((f x), z) ] = `Pr[ [% X, Z] = (x, z) ].
Proof.
  intros.
  Check pfwd1_comp.
  Check eqP.
  (* unfold RV2. *)
  set g := (fun p:(TA * TD) => (f p.1, p.2)).
  assert (injective g).
    unfold injective.
    intros.
    destruct x1 as [xa xd].
    destruct x2 as [xa' xd'].
    unfold g in H1.
    inversion H1.
    unfold injective in H0.
    specialize (H0 xa xa').
    apply H0 in H3.
    rewrite H3.
    reflexivity.
  assert (g `o [% X, Z] = [% (f `o X), Z]).
    unfold comp_RV.
    unfold g.
    unfold RV2. 
    simpl.
    reflexivity.
  assert (g (x, z) = (f x, z)).
    unfold g.
    simpl.
    reflexivity.
  rewrite <- H2.
  rewrite <- H3.
  Check pfwd1_comp.
  rewrite -> pfwd1_comp with (f := g) (X := [% X, Z]) (a := (x, z)).
  reflexivity.
  assumption.
Qed.


(* Lemma inj_triple_map: forall {TA TB TD UA UB UD : finType}
  (f : (TA*TD) -> UA) (g : (TB*TD) -> UB) (h : TD -> UD),
  injective f ->
  injective g ->
  injective h ->
  injective (fun (u, v, w) => (f u, g v, h w)). *)

(* TO DO *)
Lemma cinde_fn_transform:
  forall {TA TB TD UA UB UD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD})
  (f : (TA*TD) -> UA) (g : (TB*TD) -> UB) (h : TD -> UD),
  injective f ->
  injective g ->
  injective h ->
  [% X, Z] _|_ [% Y, Z ] | Z ->
  f `o [% X, Z] _|_ g `o [% Y, Z ] | (h `o Z).
Proof.
  intros.
  unfold cinde_RV.
  intros.

  have [Hzero | Hnonzero] := boolP (`Pr[(h `o Z) = c] == 0).
    Check cpr_eq0_denom.
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_by_zero_left.
    reflexivity.
  
  destruct (classic  (exists xz, f xz = a)) as [ [xz Hf] | Hfnotin ].
  destruct (classic  (exists yz, g yz = b)) as [ [yz Hg] | Hgnotin ].
  destruct (classic  (exists z, h z = c)) as [ [z Hh] | Hhnotin ].
  rewrite <- Hf.
  rewrite <- Hg.
  rewrite <- Hh.
  rewrite !cpr_eqE.
  rewrite pfwd1_comp; try assumption.
  destruct xz as [xf zf].
  destruct yz as [yg zg].
  rewrite !pfwd1_comp_in_joint; try assumption.

  rewrite [in RHS] pfwd1_pairC.
  Check pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite [in RHS] pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite -> pfwd1_pairC with (TY := [% Y, Z]).
  unfold swap.
  simpl.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite -> pfwd1_pairC with (TX := [% Y, Z]).
  unfold swap.
  simpl.
  
  Check cpr_eqE.
  rewrite <- cpr_eqE with (X := [% X, Z]) (Y := Z).
  rewrite <- cpr_eqE.
  unfold cinde_RV in H3.
  
  Check pfwd1_pairA.
  rewrite <- pfwd1_pairA.
  rewrite pfwd1_comp_in_joint; try assumption.
  Check pfwd1_pairA.
  rewrite -> pfwd1_pairA with (TX := [% X, Z]) (TY := (g `o [% Y, Z])) 
      (TZ := (h `o Z)) (a:= (xf, zf)).
  rewrite -> pfwd1_pairC with (TY := [% X, Z, (g `o [%Y, Z])]).
  unfold swap.
  simpl.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite -> pfwd1_pairC with (TX := [% X, Z, (g `o [%Y, Z])]).
  unfold swap.
  simpl.
  rewrite <- pfwd1_pairA.
  rewrite -> pfwd1_pairCA.
  rewrite pfwd1_comp_in_joint; try assumption.
  Check pfwd1_pairCA.
  rewrite -> pfwd1_pairCA with (TX := [% Y, Z]) (TY := [% X, Z]) 
      (TZ := Z).
  rewrite -> pfwd1_pairA.
  rewrite <- cpr_eqE.

  specialize (H3 (xf, zf) (yg, zg) z).
  exact H3.

  Check no_fn_val_prob_zero.
  pose proof (no_fn_val_prob_zero Z _ _ Hhnotin).
  rewrite H4 in Hnonzero.
  move/eqP: Hnonzero.
  intros.
  contradiction.

  pose proof (no_fn_val_prob_zero [% Y, Z] _ _ Hgnotin).
  rewrite !cpr_eqE.
  Check pfwd1_domin_RV2.
  pose proof (pfwd1_domin_RV2 (h `o Z) c H4).
  pose proof (pfwd1_domin_RV1 (f `o [% X, Z]) a H5).
  rewrite H5.
  rewrite pfwd1_pairA in H6.
  rewrite H6.
  rewrite zero_div_zero.
  rewrite mult_by_zero_right.
  reflexivity.
  assumption.
  
  pose proof (no_fn_val_prob_zero [% X, Z] _ _ Hfnotin).
  rewrite !cpr_eqE.
  pose proof (pfwd1_domin_RV2 (h `o Z) c H4).
  pose proof (pfwd1_domin_RV2 (g `o [% Y, Z]) b H4).
  pose proof (pfwd1_domin_RV2 (h `o Z) c H6).
  rewrite H5.
  rewrite H7.
  rewrite zero_div_zero.
  rewrite mult_by_zero_left.
  reflexivity.
  assumption.
Qed.

(* Lemma taking_fst_of_pair_HC: forall x,
  ([% UHRV, UCRV] x).1 = (UHRV x).
Proof.
  intros.
  destruct x as [xh xc].
  simpl.
  reflexivity.
Qed. *)

(* Lemma fn_same_HC:
  forall t, 
  (fun x : UC * UT * UH => fH ([% UHRV, UCRV] x).1 
    (fC ([% UHRV, UCRV] x).2) t) = 
    (fun x : UC * UT * UH => fH (UHRV x) (fC (UCRV x)) t).
Proof.
  intros.
  simpl.
  reflexivity.
Qed. *)

(* Lemma fn_same_TC: 
  (fun x : UC * UT * UH => fT ([% UTRV, UCRV] x).1 
    (fC ([% UTRV, UCRV] x).2)) = 
    (fun x : UC * UT * UH => fT (UTRV x) (fC (UCRV x))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed. *)

Lemma inj_Hnodefnintt_formulations: forall t,
  (exists t' : UT, True) ->
  injective (Hnodefnint t) ->
  injective (fun u : UH * UC => fH u.1 (fC u.2) t).
Proof.
  intros.
  unfold Hnodefnint in H1.
  unfold Hinterv in H1.
  unfold C in H1.
  unfold injective.
  unfold injective in H1.
  intros.
  destruct x1 as [x1h x1c].
  destruct x2 as [x2h x2c].
  simpl in H2.
  destruct H0 as [t' _].
  specialize (H1 (x1c, t', x1h) (x2c, t', x2h)).
  simpl in H1.
  apply H1 in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma inj_Tnodefn_formulations:
  (exists h : UH, True) ->
  injective (fun u' : UC * UT * UH => fT u'.1.2 (fC u'.1.1)) ->
  injective (fun u : UT * UC => fT u.1 (fC u.2)).
Proof.
  intros.
  unfold injective.
  unfold injective in H1.
  intros.
  destruct x1 as [x1t x1c].
  destruct x2 as [x2t x2c].
  simpl in H2.
  destruct H0 as [h _].
  specialize (H1 (x1c, x1t, h) (x2c, x2t, h)).
  simpl in H1.
  apply H1 in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma inj_Cnodefn_formulations:
  (exists t : UT, True) ->
  (exists h : UH, True) ->
  injective (fun u : UC * UT * UH => fC u.1.1) ->
  injective fC.
Proof.
  intros.
  unfold injective.
  intros.
  unfold injective in H2.
  destruct H0 as [t _].
  destruct H1 as [h _].
  specialize (H2 (x1, t, h) (x2, t, h)).
  simpl in H2.
  apply H2 in H3.
  inversion H3.
  reflexivity.
Qed.

(* Lemma removing previous stricter condition, claiming
   that if we start with mutual independence and some 
   injectivity and non-zero set properties, then we get
   the conditional independence condition that was used
   in doint_equiv_with_confounder_prob lemma. *)
Lemma mut_unobs_indp_cond_indp: forall t, 
  mutual_indep_three UHRV UTRV UCRV ->
  injective (Hnodefnint t) ->
  injective Tnodefn ->
  injective Cnodefn ->
  (exists h : UH, True) ->
  (exists t : UT, True) ->
  (Hnodefnint t) _|_ Tnodefn | Cnodefn.
Proof.
  intros.
  apply mut_indp_cond_indp in H0.
  apply indp_not_affected_by_adding_cond in H0.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn.
  unfold C.
  assert (injective (fun u : UH * UC => fH u.1 (fC u.2) t)).
    apply inj_Hnodefnintt_formulations; assumption.
  assert (injective (fun u : UT * UC => fT u.1 (fC u.2))).
    unfold Tnodefn in H2.
    unfold T in H2.
    unfold C in H2. 
    apply inj_Tnodefn_formulations; assumption.
  assert (injective fC).
    unfold Cnodefn in H3.
    unfold C in H3.
    apply inj_Cnodefn_formulations; assumption.
  pose proof (cinde_fn_transform UHRV UTRV UCRV 
      (fun u => fH u.1 (fC u.2) t) 
      (fun u => fT u.1 (fC u.2))
      (fun u => fC u)
      H6 H7 H8 H0) as Hcindp.
  unfold comp_RV in Hcindp. 
  simpl in Hcindp.
  (* rewrite fn_same_TC in H7.
  rewrite fn_same_HC in H7. *)
  unfold UCRV in Hcindp.
  unfold UTRV in Hcindp.
  unfold UHRV in Hcindp.
  simpl.
  exact Hcindp.
Qed. 


(* If we have mutual independence, then on the graph
   C -> T -> H, C -> H
   we get that once we condition on C, the observational
   and interventional probability distributions for H
   are the same. *)
Lemma doint_equiv_with_confounder_prob_wo_indp: forall t c, 
  mutual_indep_three UHRV UTRV UCRV ->
  injective (Hnodefnint t) ->
  injective Tnodefn ->
  injective Cnodefn ->
  (exists h : UH, True) ->
  (exists t : UT, True) ->
  `Pr[ Cnodefn = c ] != 0 ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ] 
      = `Pr[ (Hnodefnint t) = h | Cnodefn = c ]).
Proof.
  intros. 
  apply doint_equiv_with_confounder_prob; try assumption.
  apply mut_unobs_indp_cond_indp; assumption. 
Qed.

(* Lemma doint_equiv_with_confounder: forall t c, 
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  `Pr[ Cnodefn = c ] != 0 ->
  `E_[ Hnodefn | finset (Tnodefn @^-1 t) :&: finset (Cnodefn @^-1 c) ] 
      = `E_[ (Hnodefnint t) | finset (Cnodefn @^-1 c) ].
Proof.
Admitted. *)


End ThreeVarConfounderExample.













Section ThreeVarMediatorExample. (* T -> C -> H, T -> H*)
Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UT * UC) * UH).
Variable outcomes: finType.

Variable fC : UC -> outcomes -> outcomes.
Variable fT : UT -> outcomes.
Variable fH : UH -> outcomes -> outcomes -> outcomes.

Let T (p : UT * UC * UH ): outcomes :=
  fT p.1.1.
Let C (p: UT * UC * UH) : outcomes :=
  fC p.1.2 (T p).
Let H (p : UT * UC * UH) : outcomes :=
  fH p.2 (C p) (T p).
Let Cinterv (p: UT * UC * UH) t : outcomes :=
  fC p.1.2 t.
Let Hinterv (p : UT * UC * UH) t : outcomes :=
  fH p.2 (Cinterv p t) t. 

Let Cnodefn : {RV P -> outcomes} :=
  fun u => C u.
Let Tnodefn : {RV P -> outcomes} :=
  fun u => T u.
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Cnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Cinterv u t.
Let Hnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Hinterv u t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.1.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.2.


Lemma change_ord_mult: forall (a b c : R),
  a * b * c  = a * c * b.
Proof.
Admitted.

(* Probability lemma with stronger assumption than desired *)
Lemma doint_prob_mediator_w_assump: forall t,
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  (* Check indep_then_cond_irrelevant. *)
  pose proof (indep_then_cond_irrelevant outcomes (UT * UC)%type UH P Tnodefn (Hnodefnint t) H0).
  specialize (H2 t).
  pose proof (H2 H1).
  specialize (H3 a).
  clear H2.
  rewrite H3.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold C.
  unfold T.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  unfold Tnodefn in H1.
  unfold T in H1.
  eapply eqr_divrMr. assumption.
  rewrite div_mult; try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Ht : (fT a0.1.1 == t).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Qed.

Lemma mediator_indpU_indpNF: forall t,
  P |= [% UHRV, UCRV] _|_ UTRV ->
  P |= (Hnodefnint t) _|_ Tnodefn.
Proof.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Cinterv.
  unfold Tnodefn.
  unfold T.
  Check inde_RV_comp.
  (* apply inde_RV_comp. *)
  (* Check (Hnodefnint t). *)
  (* pose proof (inde_RV_comp _ _ UH UT _ _ UHRV UTRV (fun u => fH u t) (fun u => fT u) H0). *)
  pose proof (inde_RV_comp 
      (fun u => fH u.1 (fC u.2 t) t) 
      (fun u => fT u) H0).
  unfold comp_RV in H1. 
  unfold UTRV in H1.
  unfold UHRV in H1.
  apply H1.
Qed.

Lemma mediator_mut_indp_to_pair_indp:
  mutual_indep_three UC UH UT P UHRV UTRV UCRV ->
  P |= [% UHRV, UCRV] _|_ UTRV.
Proof.
  intros.
  unfold inde_RV.
  unfold mutual_indep_three in H0.
  inversion H0.
  clear H0.
  inversion H2.
  clear H2.
  inversion H3.
  clear H3.
  destruct x as [h c].
  intros.
  specialize (H1 h y c).
  rewrite pfwd1_pairAC.
  unfold inde_RV in H4.
  specialize (H4 h c).
  rewrite H4.
  apply esym.
  rewrite change_ord_mult in H1.
  exact H1.
Qed.

Lemma doint_mediator: forall t,
  mutual_indep_three UC UH UT P UHRV UTRV UCRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  apply doint_prob_mediator_w_assump.
  apply mediator_indpU_indpNF.
  apply mediator_mut_indp_to_pair_indp.
  exact H0.
  assumption.
Qed.


End ThreeVarMediatorExample.


Section ThreeVarColliderExample.
Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UT * UC) * UH).
Variable outcomes: finType.

Variable fC : UC -> outcomes -> outcomes -> outcomes.
Variable fT : UT -> outcomes.
Variable fH : UH -> outcomes -> outcomes.

Let T (p : UT * UC * UH ): outcomes :=
  fT p.1.1.
Let H (p : UT * UC * UH) : outcomes :=
  fH p.2 (T p).
Let C (p: UT * UC * UH) : outcomes :=
  fC p.1.2 (T p) (H p).
Let Hinterv (p : UT * UC * UH) t : outcomes :=
  fH p.2 t. 
Let Cinterv (p: UT * UC * UH) t : outcomes :=
  fC p.1.2 t (Hinterv p t).

Let Cnodefn : {RV P -> outcomes} :=
  fun u => C u.
Let Tnodefn : {RV P -> outcomes} :=
  fun u => T u.
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Cnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Cinterv u t.
Let Hnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Hinterv u t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.1.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.2.


(* Probability lemma with stronger assumption than desired *)
Lemma doint_prob_collider_w_assump: forall t,
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  (* Check indep_then_cond_irrelevant. *)
  pose proof (indep_then_cond_irrelevant outcomes (UT * UC)%type UH P Tnodefn (Hnodefnint t) H0).
  specialize (H2 t).
  pose proof (H2 H1).
  specialize (H3 a).
  clear H2.
  rewrite H3.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold C.
  unfold T.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  unfold Tnodefn in H1.
  unfold T in H1.
  eapply eqr_divrMr. assumption.
  rewrite div_mult; try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Ht : (fT a0.1.1 == t).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Qed.

Lemma collider_mut_indp_to_pair_indp:
  mutual_indep_three UC UH UT P UHRV UTRV UCRV ->
  P |= UHRV _|_ UTRV.
Proof.
  intros.
  unfold mutual_indep_three in H0.
  inversion H0.
  clear H0.
  inversion H2.
  assumption.
Qed.

Lemma collider_indpU_indpNF: forall t,
  P |= UHRV _|_ UTRV ->
  P |= (Hnodefnint t) _|_ Tnodefn.
Proof.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  pose proof (inde_RV_comp (fun u => fH u t) (fun u => fT u) H0).
  unfold comp_RV in H1. 
  unfold UTRV in H1.
  unfold UHRV in H1.
  apply H1.
Qed.

Lemma doint_collider: forall t,
  mutual_indep_three UC UH UT P UHRV UTRV UCRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof. 
  intros.
  apply doint_prob_collider_w_assump.
  apply collider_indpU_indpNF.
  apply collider_mut_indp_to_pair_indp.
  exact H0.
  assumption.
Qed.

End ThreeVarColliderExample.



Section BackdoorAdjustment.

(* Lemma doint_prob: *)
  

End BackdoorAdjustment.