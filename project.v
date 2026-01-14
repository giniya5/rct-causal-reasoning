From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
Require Import Reals.
From infotheo.information_theory Require Import entropy.
From infotheo.probability Require Import fdist proba fsdist.
From infotheo.probability Require Import jfdist_cond.
Require Import List.
Import ListNotations.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require boolp.
From mathcomp Require Import unstable mathcomp_extra reals exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln fdist.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section THExampleCleaner.

Context {R : realType}. (* used to be realType*)
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
  (* Check eqr_divrMr.
  Check mulC.
  Check mulV_l. *)
  rewrite <- GRing.mulrA.
  rewrite GRing.mulfV.
  Check GRing.mulr1.
  rewrite GRing.mulr1.
  reflexivity.
  assumption.
  (* apply mulV_l. *)
  (* rewrite mulV_l. *)
  (* pose proof (mulV_l H0). *)
  (* Search (_ / _). *)
  (* eapply eqr_divrMr. *)
  (* Check natrme. *)
  (* admit. *)
  (* rewrite divr_inv.
  rewrite invrK.
  reflexivity.
  Search ( _ ^-1). *)
  (* pose proof (GRing.mulfV H0). *)
  (* pose proof (Rmult_eq_compat_l a 1 (b / b)). *)
  (* Search ( _ * _ * _ = _ * (_ * _) ). *)
  (* Check Rmult_eq_compat_l. *)
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
  (* Search ( ?x / ?x). *)
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
  (* Search (_/?x = _/?x). *)
  (* Check eqr_divrMr. *)
  eapply eqr_divrMr. assumption.
  rewrite <- div_mult; try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  (* Search ( _ && _ = _ && _ ). *)
  (* apply/andb_congr.  *)
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

  (* forall (f1 f2 : {RV (P) -> (R)}),
  perm_eq [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f1
 | i  \in fin_img (A:=(UT * UH)%type) (B:=R) f2]
  [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2
 | i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1]. *)

 (* perm_eq
[seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f1
 | i  \in fin_img (A:=(UT * UH)%type) (B:=R) f2
 & i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1]
[seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2
 | i  \in fin_img (A:=(UT * UH)%type) (B:=R) f2
 & i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1]. *)
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
  (* rewrite big_seq_cond.
  rewrite [in RHS] big_seq_cond.
  rewrite big_andbC. *)
  rewrite <- big_filter.
  (* assert (
      \sum_(i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      (i \in fin_img (A:=(UT * UH)%type) (B:=R) f2) &&
      (i \in fin_img (A:=(UT * UH)%type) (B:=R) f1))
      i * `Pr[ Hnodefn = i | Tnodefn = 1 ]
      = 
      \sum_(i <- [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | 
      i  \in fin_img (A:=(UT * UH)%type) (B:=R) f2
      & i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1])
      i * `Pr[ Hnodefn = i | Tnodefn = 1 ]
      ). *)
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
  (* rewrite <- big_filter at 1. *)
  apply perm_big.
  apply filtering_equal.
  apply fin_img_uniq.
  apply fin_img_uniq.
  (* rewrite perm_big with (r2 := [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1]). *)
  (* pose proof (filtering_equal f1 f2).
  pose proof (perm_big _ _ _ _ ).
  rewrite perm_big_supp_cond with (s := [seq i <- fin_img (A:=(UT * UH)%type) (B:=R) f2 | i  \in fin_img (A:=(UT * UH)%type) (B:=R) f1]).
  pose proof (filtering_equal).
  rewrite big_filter.
  reflexivity. *)
  (* rewrite big_filter_cond. *)
  (* rewrite big_seq_cond.
  rewrite [in RHS] big_seq_cond.
  rewrite big_andbC.
  Check big_cat.
  Check big_filter. *)
  
  (* Check big_filter.
  Check big_filter_cond.
  Check big_seq_cond.
  Check big_andbC.
  
  Check eq_bigl.
  Check big_filter.
  Check big_union.
  Check partition_big_preimset.
  Check eq_bigr.
  Check eq_big.
  Check big_rV0_row_of_tuple.
  (* Check partition_big_fin_img. *)
  (* Check big_morph. *)
  Check big_union. *)
  (* rewrite (big_union (fin_img (Hnodefnint 1)) (fin_img Hnodefn)). *)
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
  (* Check bigID2. *)
  (* pose proof (bigID). *)
  
  rewrite (bigID (fun r => r \in fin_img (Hnodefn))).
  simpl.
  rewrite same_preimg_helper_int; cycle 1; try assumption.
  rewrite GRing.addr0.
  (* Search (?x = ?y -> ?y = ?x). *)
  (* rewrite Logic.eq_sym. *)
  rewrite [in RHS] (bigID (fun r => r \in fin_img (Hnodefnint 1))).
  simpl.
  rewrite same_preimg_helper_noint; cycle 1; try assumption.
  rewrite GRing.addr0.
  rewrite simplifying_summing.
  reflexivity.
  (* info_eauto.
  Check (Hnodefnint 1).
  Check Hnodefn.
  Check (1 * `Pr[ Hnodefn = 1 | Tnodefn = 1 ]).
  (* pose proof (simplifying_summing (Hnodefnint 1) Hnodefn). *)
  (* rewrite eq_big => i. *) *)
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
  (* 
  (* rewrite mulC. *)
  Search 
  (* rewrite /cPr. *)

  (* rewrite /cEx.
  rewrite /Ex.
  apply: Ex_cEx. *)
  (* rewrite Ex_cEx.
  rewrite Ex_cEx with (F := Tnodefn) (I := UT * UH). *)
  (* rewrite <- Ex_altE.
  unfold Ex_alt.
  rewrite <- H0. *)
  (* rewrite /Ex. *)
  rewrite /cEx.
  (* assert (Pr P
  (finset (T:=(UT * UH)%type) (preim Hnodefn (pred1 r))
  :&: finset (T:=(UT * UH)%type) (preim Tnodefn (pred1 1))) /
  Pr P (finset (T:=(UT * UH)%type) (preim Tnodefn (pred1 1))) = 
    `Pr[(finset (T:=(UT * UH)%type) (preim Hnodefn (pred1 r))) | 
      (finset (T:=(UT * UH)%type) (preim Tnodefn (pred1 1)))]). *)
  unfold cPr.
  unfold cPr_eq.
  destruct u as (ut uh).
  Check exchange_big.
  rewrite (exchange_big
         (fun u => Hnodefn u)  (* the function mapping states to values *)
         (fun r => r * Pr P (finset (preim Hnodefn r) :&: finset (preim Tnodefn (pred1 1))))).
  apply eq_big => // a _.
  Check partition_big.
  rewrite (partition_big (fun x => Hnodefn x)).
  rewrite (H0 r).
  (* set r := Hnodefn u. *)
  eapply eq_bigl. *)
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
  (* rewrite <- Ex_altE.
  unfold Ex_alt.
  unfold cEx.
  apply: eq_bigl=> r.
  Check cinde_alt.

  rewrite (@Ex_cEx _ _ UH _ _ Hnodefnint).
  rewrite Ex_cEx. *)
   (* with (I := UH) (F := Hnodefnint). *)
Qed.












Context {R : realType}.
Variables (UT UH : finType).
Variable P : R.-fdist (UT * UH).
(* Variables (UTRV : {RV P -> UT}) (UHRV : {RV P -> UH}). *)
Variable fT : UT -> bool.
Variable fH : UH -> bool -> bool.
Definition T (p : UT * UH ): bool :=
  fT p.1.
Definition Hinterv (p : UT * UH) t : bool :=
  fH p.2 t.  
Definition H (p : UT * UH) : bool :=
  fH p.2 (T p).
Definition nodefn : {RV P -> bool * bool} :=
  fun u => (T u , H u).
Definition nodefnint (t:bool) : {RV P -> bool * bool} :=
  fun u => (t , Hinterv u t).
Locate "'RV'".
Print RV_of.
Print RV.

Lemma doint_equiv:
  `E_[ nodefn | nodefn.1 = true] = `E[ (nodefnint true) ].

Variable Tset, Hset : bool.
Variable P'' : R.-fdist ((UT * UH) * (bool * bool)).
Variable UT'' : {RV P'' -> UT}.
Variable UH'' : {RV P'' -> UH}.
Variable T'' : {RV P'' -> bool}.
Variable H'' : {RV P'' -> bool}.

End THExampleCleaner.



Section THExample.

Context {R : realType}.
(* Underlying sample space Ω as an arbitrary type *)
(* Variable Ω : finType.
Variable (P : R.-fdist (Ω)).
Variables (X : {RV P -> UT}) (Y : {RV P -> UH}).
Variable (SX : {set UT}) (SY : {set UH}). *)

Variables (UT UH : finType).

(* A probability distribution on UT × UH *)
Variable P : R.-fdist (UT * UH).

(* Random variables X : Ω → UT   and   Y : Ω → UH *)
Variables (UTRV : {RV P -> UT}) (UHRV : {RV P -> UH}).

(* Define the boolean functions fT and fH *)
Variable fT : UT -> bool.
Variable fH : UH -> bool -> bool.
(* fH takes an UH and a bit (0/1) and returns a bit. *)

Variable P' : R.-fdist ((UT * UH) * bool).

(* Maybe I can make them RV to start? *)
Variable fTRV : {RV P -> bool}.
Variable fHRV : {RV P' -> bool}.

(* Definition fHRV' : {RV P -> bool} :=
  fH P`2 true. *)

(* Define derived random variables on UT * UH: *)
(* Definition T (p : P`1): bool :=
  fT p. *)

Definition T (p : UT * UH ): bool :=
  fT p.1.

Definition Htrue (p : UT * UH) : bool :=
  fH p.2 true.  

Definition H (p : UT * UH) : bool :=
  fH p.2 (T p).

(* Definition T_RV : {RV UT*UH -> bool} :=
  fH  *)

Variable UTUH : UT * UH.
(* Specific values x ∈ UT and y ∈ UH *)
(* Variable ut : UT.
Variable uh : UH. *)

Check UTRV.
(* Check T_RV. *)
(* Check Htrue_RV. *)
(* Type T_RV. *)
Check UTUH.2.

(* Lemma simplecase: forall p (ut:UT) (uh:UH),
    P |= T _|_ Htrue ->
   (* `E_[ H_RV p | T_RV p = true]. *)
   `E_[ P''`2`2 | uh]. *)


Variable Tset : bool.
Variable Hset : bool.
Check (Tset * Hset).
(* Check (bool * bool). *)
(* Variable P'' : R.-fdist ((UT * UH) * (Tset * Hset)). *)
Variable P'' : R.-fdist ((UT * UH) * (bool * bool)).
Variable UT'' : {RV P'' -> UT}.
Variable UH'' : {RV P'' -> UH}.
Variable T'' : {RV P'' -> bool}.
Variable H'' : {RV P'' -> bool}.

Lemma simplecase: forall (ut:UT) (uh:UH),
    T'' _|_ H'' | T'' ->
   (* `E_[ H_RV p | T_RV p = true]. *)
   `Pr[ H'' = true | T'' = true ] = 0.5%R.
   `E_[ P`2`2 | (T'' = true) ].

End THExample.

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals classical_sets
     measure integral prob.

Open Scope classical_set_scope.
Open Scope ring_scope.

Section ConditionalExpectationExample.

Context {R : realType}.

(* Underlying sample space Ω as an arbitrary type *)
Variable Ω : Type.

(* σ-algebra on Ω *)
Variable μ : {math real_measure Ω}.

Hypothesis μprob : isProbability μ.

(* Finite output types for random variables *)
Variables (UT UH : finType).

(* Random variables X : Ω → UT and Y : Ω → UH *)
Variables (X : Ω -> UT) (Y : Ω -> UH).

(* Assumptions: measurability of X and Y *)
Hypothesis Xmeas : measurable_fun (Sigma μ) [set: UT] X.
Hypothesis Ymeas : measurable_fun (Sigma μ) [set: UH] Y.

(* Particular values x ∈ UT and y ∈ UH *)
Variable x : UT.
Variable y : UH.

(* Events: X = x and Y = y *)
Definition event_Xx : set Ω := [set ω | X ω = x].
Definition event_Yy : set Ω := [set ω | Y ω = y].

(* Their indicator functions *)
Definition ind_Xx := indic_fun event_Xx.
Definition ind_Yy := indic_fun event_Yy.

(* Conditional expectation of indicator (X = x) given Y = y *)
Definition cond_prob :=
  cond_exp μ event_Yy ind_Xx.

End ConditionalExpectationExample.




Section TwoVariable.


Context {R : realType}.
Variables (UT UH : finType).

(* A probability distribution on UT × UH *)
Variable P : R.-fdist (UT * UH).

(* Random variables X : Ω → UT   and   Y : Ω → UH *)
Variables (X : {RV P -> UT}) (Y : {RV P -> UH}).

(* Specific values x ∈ UT and y ∈ UH *)
Variable x : UT.
Variable y : UH.

(* Event: “X = x” *)
Definition A := [set ω | X ω == x].

(* Event: “Y = y” *)
Definition B := [set ω | Y ω == y].

(* Conditional expectation  E[ 1_{X=x} | Y=y ]  *)
Definition cond_prob :=
  \E_(P | B) (1%:R *+ (X == x)).

  (* Conditional expectation E[ 1_{X=x} | Y=y ] = P(X=x | Y=y) *)
Definition cond_prob :=
  \E_(P | event_Yy) ((X == x)%:R).



Context {R: realType}.
Variables (UT UH : finType).
Variable (P : R.-fdist (UT*UH)).
Variables (X : {RV P -> UT}) (Y : {RV P -> UH}).
Variable (SX : {set UT}) (SY : {set UH}).

Variable fT : fun a => event.
Variable fH : fun a b => event.

Lemma blah : forall
  (fun uT => )

End TwoVariable.


Section ToyExample.

Context {R: realType}.
Variables (TX TY TZ : finType).
Variable (P : R.-fdist (TX*(TY*TZ))).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z: {RV P -> TZ}).
Variable (SX : {set TX}) (SY : {set TY}) (SZ : {set TZ}).

Variable fT : fun a => event.
Variable fH : fun a b => event.

Lemma E[fH(uH, fT (uT)) | fT (uT) = t] = E[fH (uH, t)].

End ToyExample.


Section DoCalc.

Context {R: realType}.
Variables (TX TY TZ : finType).
  (* idk what type these should be really.. *)
Variable (P : R.-fdist (TX*(TY*TZ))).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z: {RV P -> TZ}).
(* Implicit Types (SX : {set TX}) (SY : {set TY}) (SZ : {set TZ}). *)
Variable (SX : {set TX}) (SY : {set TY}) (SZ : {set TZ}).


Defintion docalculusoperator (TZ: finType) (Z: RV {P - > TZ}) (z: TZ) :=
  
Notation doc( TZ = z ) := TZ = z.
Definition docrule2:
    P |= Z _|_ X ->
    forall x z, `Pr[ Z = z | doc(X = x) ] = `Pr[ Z = z | X = x ].
(* Definition Pr (y | doc(x), doc(z), w) := Pr (y | doc(x), z, w) if 
    Y _|_ Z | X, W. *)

End DoCalc.