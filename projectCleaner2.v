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
- TBD
Graph T -> O -> H (mediator)
- TBD

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
  (* Check eqr_divrMr. 
  Search (?x = ?y -> ?y = ?x). *)
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

(* This lemma is in the infotheo library, but for whatever reason I 
   can't seem to access it. I've added it in as a lemma and admitted
   it for now rather than figuring out how to do this. *)
Lemma inde_RV_comp (TA TB UA UB : finType) (X : {RV P -> TA}) (Y : {RV P -> TB})
    (f : TA -> UA) (g : TB -> UB) :
  P |= X _|_ Y -> P|= (f `o X) _|_ (g `o Y).
Proof.
  (* Check (f `o X). *)
Admitted.
(* move=> /inde_RVP inde_XY; apply/inde_RVP => E F.
by rewrite (pr_in_comp' f) (pr_in_comp' g) -inde_XY -preimsetX -pr_in_comp'.
Qed. *)

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
  pose proof (inde_RV_comp UH UT _ _ UHRV UTRV (fun u => fH u t) (fun u => fT u) H0).
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

(* Lemma inde_RVP : forall (A' : finType) (P' : R.-fdist A') (TA' TB': finType)
  (X' : {RV P' -> TA'}) (Y' : {RV P' -> TB'}),
  P' |= X' _|_ Y' <-> forall E' F',
  `Pr[ [% X', Y'] \in E' `* F'] = `Pr[ X' \in E' ] * `Pr[ Y' \in F' ].
Proof.
Admitted.

Lemma inde_RV_comp_generalized (TA TB : finType) (X : {RV P -> TA}) (Y : {RV P -> TB})
    (f : TA -> R) (g : TB -> R) :
  P |= X _|_ Y -> P|= (f `o X) _|_ (g `o Y).
Proof.
  move => inde_XY.
  pose proof (inde_RVP _ P _ _ X Y).
  rewrite H0 in inde_XY.
  Check ((UT*UH)%type).
  (* Check (UT * UH). *)
  Check pr_in_comp'.
  (* Check pr_in_comp_image. *)
  Check pfwd1_comp.
  Check pr_in_comp.
  (* pose proof (pr_in_comp' f). (prod UT UH) P _ _ f X _).
  Check preimsetX.
  rewrite (pr_in_comp' f). *)

Admitted. *)

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

(* Since for expectations I need the outcomes to be eqType
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

(* Expectation Lemma stating that if the unobserved factors
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

Check comp_RV.
(* Search (_ |= _ _|_ _). *)
(* Check inde_RV_comp. *)
(* Check inde_RVP. *)

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
  (* Check eqr_divrMr. *)
  apply eqr_divrMr in H0; cycle 1. assumption.
  rewrite <- H0.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite pfwd1_pairA.
  (* Check (`Pr[ [% Z, X, Y] = (z, x, y) ]). *)
  set `Pr[ [% Z, X, Y] = (z, x, y) ] as Pxyz.
  rewrite div_num_and_denom.
  reflexivity.
  assumption.
  assumption.
  (* Check (`Pr[ Y = y ]). *)

  (* Search (_ / (_ / _)). *)
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

(* Check inde_RV_comp.
Lemma inde_RV_comp (TA TB UA UB : finType) (X : {RV P -> TA}) (Y : {RV P -> TB})
    (f : TA -> UA) (g : TB -> UB) :
  P |= X _|_ Y -> P|= (f `o X) _|_ (g `o Y).
Proof.
Admitted. *)

(* The library only seems to have mutually independent
   events and not RV, although I'm maybe missing something. *)
Definition mutual_indep_three {X' Y' Z': finType}
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}) := 
  forall x y z,
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [%[% X, Y], Z] = ((x,y), z)] /\ 
    P |= X _|_ Y /\ P |= Y _|_ Z /\ P |= X _|_ Z.
    
Check mutual_indeE. (* For events, will need something for RVs. *)
(* Definition mutual_inde_RV := forall k, @kwise_inde R A I k.+1 d E. *)

(* This lemma states that mutual independence gives us
   conditional independence.
   This lemma needs a pesky non-zero assumption, and I'm not
   sure how to get rid of it. *)
Lemma mut_indp_cond_indp: forall {X' Y' Z': finType}
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
  specialize (H0 a b c).
  destruct H0 as [Indp3 [IndpXY [IndpYZ IndpXZ]]].
  unfold inde_RV in IndpXY.
  unfold inde_RV in IndpXZ.
  unfold inde_RV in IndpYZ.
  specialize (IndpXY a b).
  specialize (IndpXZ a c).
  specialize (IndpYZ b c).
  rewrite !cpr_eqE.
  rewrite IndpYZ.
  rewrite IndpXZ.
  rewrite mult_div.
  rewrite mult_div.
  rewrite eqr_divrMr.
  rewrite Indp3.
  reflexivity.
  (* all: assumption. *)
  all: admit.
(* Qed. *)
Admitted.

(* If the unobserved factors are independent, then the
   nodefunctions are independent. *)
Lemma unobv_indp_fn_indp: 
  UHRV _|_ UTRV | UCRV ->
  (forall t, (Hnodefnint t) _|_ Tnodefn | Cnodefn).
Proof.
  intros.
  (* rewrite cinde_alt.
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
  apply H1. *)
Admitted.

(* If we have mutual independence, then on the graph
   C -> T -> H, C -> H
   we get that once we condition on C, the observational
   and interventional probability distributions for H
   are the same. *)
Lemma doint_equiv_with_confounder_prob_wo_indp: forall t c, 
  mutual_indep_three UHRV UTRV UCRV ->
  `Pr[ Cnodefn = c ] != 0 ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ] 
      = `Pr[ (Hnodefnint t) = h | Cnodefn = c ]).
Proof.
  intros.
  apply mut_indp_cond_indp in H0.
  pose proof (unobv_indp_fn_indp H0 t).
  apply doint_equiv_with_confounder_prob; assumption.
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


Section BackdoorAdjustment.

(* Lemma doint_prob: *)
  

End BackdoorAdjustment.