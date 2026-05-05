From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
Require Import Reals.
From infotheo.probability Require Import proba fdist. (* fsdist jfdist_cond. *)
Require Import List.
Import ListNotations.
From mathcomp Require Import reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require Import unstable mathcomp_extra reals exp.
(* Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln. *)
Require Import ssralg_ext bigop_ext realType_ext realType_ln.
Require Import Classical.
Require Import Field.
Require Import Lia.
From project Require Import TwoVarThreeVarExamples.
From project Require Import GeneralParentalAdj.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.




Section SNSGPA.
Context {R : realType}.

Variables (UT UH UA UN UD UE UC UO : finType).
Variable P : R.-fdist (((UO * UD * UA * UN * UE * UC) * UT) * UH).
Variables ocT ocH ocD ocA ocN ocE ocC ocO : finType.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.2.
Let UERV: {RV P -> UE} :=
  fun u => u.1.1.1.2.
Let UNRV: {RV P -> UN} := 
  fun u => u.1.1.1.1.2.
Let UARV: {RV P -> UA} :=
  fun u => u.1.1.1.1.1.2.
Let UDRV: {RV P -> UD} :=
  fun u => u.1.1.1.1.1.1.2.
Let UORV: {RV P -> UO} :=
  fun u => u.1.1.1.1.1.1.1.

Variable fD : UD -> ocD.
Variable fA : UA -> ocD -> ocA.
Variable fN : UN -> ocD -> ocN.
Variable fE : UE -> ocD -> ocE.
Variable fC : UC -> ocD -> ocE -> ocC.
Variable fO : UO -> ocD -> ocE -> ocC -> ocO.
Variable fT : UT -> ocD -> ocE -> ocC -> ocT.
Variable fH : UH -> ocD -> ocE -> ocC -> ocA -> ocN -> ocO -> ocT -> ocH.

Let D : {RV P -> ocD} :=
  fun p => fD (UDRV p).
Let A : {RV P -> ocA} :=
  fun p => fA (UARV p) (D p).
Let N: {RV P -> ocN} :=
  fun p => fN (UNRV p) (D p).
Let E: {RV P -> ocE} :=
  fun p => fE (UERV p) (D p).
Let C: {RV P -> ocC} :=
  fun p => fC (UCRV p) (D p) (E p).
Let Ot: {RV P -> ocO} :=
  fun p => fO (UORV p) (D p) (E p) (C p).
Let T : {RV P -> ocT} :=
  fun p => fT (UTRV p) (D p) (E p) (C p).
Let H : {RV P -> ocH} :=
  fun p => fH (UHRV p) (D p) (E p) (C p) (A p) (N p) (Ot p) (T p).

Let Tinterv (t: ocT) : {RV P -> ocT} :=
  fun p => t.
Let Dinterv (t: ocT) : {RV P -> ocD} :=
  fun p => fD (UDRV p).
Let Ainterv (t: ocT) : {RV P -> ocA} :=
  fun p => fA (UARV p) (Dinterv t p).
Let Ninterv (t: ocT) : {RV P -> ocN} :=
  fun p => fN (UNRV p) (Dinterv t p).
Let Einterv (t: ocT) : {RV P -> ocE} :=
  fun p => fE (UERV p) (Dinterv t p).
Let Cinterv (t: ocT) : {RV P -> ocC} :=
  fun p => fC (UCRV p) (Dinterv t p) (Einterv t p).
Let Ointerv (t: ocT) : {RV P -> ocO} :=
  fun p => fO (UORV p) (Dinterv t p) (Einterv t p) (Cinterv t p).
Let Hinterv (t: ocT) : {RV P -> ocH}:= 
  fun p => fH (UHRV p) (Dinterv t p) (Einterv t p) (Cinterv t p) 
      (Ainterv t p) (Ninterv t p) (Ointerv t p) t.

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


Lemma sci_exp_node_indp : forall t, 
  mutual_indep_three [% UHRV, UARV, UNRV] UTRV [% UCRV, UDRV, UERV] ->
  (Hinterv t) _|_ T | [% C, D, E].
Proof.
  intros.
  (* Check mut_indp_with_fn.  *)
  (* pose proof (mut_indp_with_fn UCRV UDRV UERV 
      (fun p => [% (fun p => fC (UCRV p) (D p) (E p)), 
          (fun p => fD (UDRV p)), (fun p => fE (UERV p) (D p))])).
  unfold Hinterv.
  unfold T.

  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn.
  unfold C.
  pose proof (mut_indp_with_fn UHRV UTRV UCRV fC).
  (* apply mut_indp_with_fn in H0. *)
  apply mut_indp_cond_indp in H1; try assumption.
  apply indp_not_affected_by_adding_cond in H1.
  (* Check cinde_fn_transform'. *)
  pose proof (cinde_fn_transform' UHRV UTRV (fC `o UCRV) (fun u => fH u.1 u.2 t)
    (fun u => fT u.1 u.2) H1).
  unfold comp_RV in H2.
  simpl in H2.
  unfold UHRV in H2.
  unfold UCRV in H2.
  unfold UTRV in H2.
  exact H2. *)
Admitted. 

Lemma backdoor_adj_snsgpa_tt : forall t,
  mutual_indep_three UHRV UTRV [% UCRV, UDRV, UERV] ->
  (forall pa t, `Pr[ T = t | [% C, D, E] = pa ] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(cde : ocC * ocD * ocE) 
      `Pr[ H = h | [% T, [% C, D, E] ] = (t, cde)] * `Pr[[% C, D, E] = cde]).
Proof.
  move=> t indp nonneg.
  (* rewrite <- three_var_confounder_backdoor_adjustment. *)
Admitted.



Lemma backdoor_adj_snsgpa : forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Einterv t)], 
      [% (Ainterv t), (Ninterv t), (Ointerv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, E] , [% A, N, Ot]] = (h, t, pa, e) ] 
        / `Pr[ T = t | [% C, D, E] = pa ]) ->
  (forall pa t, `Pr[ T = t | [% C, D, E] = pa ] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(cde : ocC * ocD * ocE) 
      `Pr[ H = h | [% T, [% C, D, E] ] = (t, cde)] * `Pr[[% C, D, E] = cde]).
Proof.
  move => t factor nonneg.
  (* apply parental. *)
  apply parental with (E := [% A, N, Ot ])
      (Einterv := (fun t => [% (Ainterv t), (Ninterv t), (Ointerv t) ])) 
      (paTinterv := (fun t => [% (Cinterv t), (Dinterv t), (Einterv t)])).
  assumption.
  intros.
  rewrite pfwd1_pairC.
  apply cond_to_pair_non_zero.
  simpl.
  specialize (nonneg i0 i1).
  assumption.
Qed.

(* Lemma CDE_equal: forall t pa,
  `Pr[ [% (Cinterv t), (Dinterv t), (Einterv t)] = pa ] = 
  `Pr[ [% C, D, E] = pa ].
Proof.
Admitted. *)

Lemma Hinterv_H : forall t a, 
  T a = t -> 
  Hinterv t a = H a.
Proof. 
  by move=> t a <-. 
Qed.

(* Lemma preim_pair : forall (f g : _ -> _) a b,
  preim [% f, g] (pred1 (a, b)) =i 
  [predI preim f (pred1 a) & preim g (pred1 b)]. *)

(* Lemma factorhelp: forall t, 
  mutual_indep_four UHRV UTRV [% UCRV, UDRV, UERV ] [% UARV, UNRV] -> *)


Lemma factorholds_helper: forall t,
  mutual_indep_four UHRV UTRV [% UCRV, UDRV, UERV ] [% UARV, UNRV] ->
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Einterv t)], 
      [% (Ainterv t), (Ninterv t) ]] = (h, pa, e)] * 
    `Pr[ [% T, [% C, D, E]] = (t, pa) ] = 
    `Pr[ [% H, T, [% C, D, E] , [% A, N]] = (h, t, pa, e)] * 
    `Pr[ [% C, D, E] = pa ]).
Proof.
  intros.
  change (Cinterv t) with C.
  change (Dinterv t) with D.
  change (Einterv t) with E.
  change (Ainterv t) with A.
  change (Ninterv t) with N.

  (* rewrite !pr_eqE /=. *)

  destruct e as [a n].
  destruct pa as [[c d] e].
    
    

  rewrite !pfwd1E /Pr.
  
  (* rewrite !big_mkcond /=. *)
  rewrite big_distrl.
  simpl.
  rewrite [in RHS] big_distrl.
  simpl.
  (* under eq_bigr => a _ do rewrite big_distrr.
  simpl.
  under [in RHS] eq_bigr => a _ do rewrite big_distrr.
  simpl.

  have LHS_split: 
  \sum_(a | [% Hinterv t, [% C,D,E], [% A,N]] a == (h,pa,e)) P a =
  \sum_(a | ([% Hinterv t, [% C,D,E], [% A,N]] a == (h,pa,e)) && (T a == t)) P a +
  \sum_(a | ([% Hinterv t, [% C,D,E], [% A,N]] a == (h,pa,e)) && (T a != t)) P a.
  { by rewrite -bigID. } *)

  (* rewrite pair_big.
  simpl.
  rewrite [in RHS] pair_big.
  simpl.
  (* rewrite (bigID (fun a => T a == t)). *)
  apply eq_bigl.
  rewrite !inE.
  Check eq_bigl.
  (* rewrite !cpr_eqE. *)
  rewrite !pfwd1E /Pr.
  
  rewrite !cPr_eq_def. *)

  
Admitted.

Lemma factorholds_helper2: forall {A' B' : finType} 
  (* {P' : R.-fdist (U')} *)
  (X' : {RV P -> A'}) (Y' : {RV P -> B'}) t, 
  [% (Hinterv t), X' ] _|_ T | Y' -> 
  forall h x y, `Pr[ [% (Hinterv t), X' ] = (h, x) | Y' = y ] = 
  `Pr[ [% (Hinterv t), X'] = (h, x) | [% T, Y'] = (t, y) ]. 
Proof.
Admitted.

Lemma factorholds': forall t, 
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% A, N, Ot ]] = (h, e) | [% C, D, E] = pa ] =
  `Pr[ [% H, [% A, N, Ot]] = (h, e) | [% T, [% C, D, E]] = (t, pa) ]).
Proof.
Admitted.

Lemma factorholds: forall t, 
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Einterv t)], 
      [% (Ainterv t), (Ninterv t), (Ointerv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, E] , [% A, N, Ot]] = (h, t, pa, e) ] 
        / `Pr[ T = t | [% C, D, E] = pa ]).
Proof.
  intros.
  change (Cinterv t) with C.
  change (Dinterv t) with D.
  change (Einterv t) with E.
  change (Ainterv t) with A.
  change (Ninterv t) with N.
  change (Ointerv t) with Ot.
  
  (* destruct e as [a n].
  destruct pa as [[c d] e]. *)
  rewrite cpr_eqE.
  (* rewrite /Pr. *)
Admitted.

Lemma factor_to_equ: forall t,
  (forall h pa e, `Pr[ [% (Hinterv t), (Tinterv t),
      [% (Cinterv t), (Dinterv t), (Einterv t)], 
      [% (Ainterv t), (Ninterv t), (Ointerv t) ]] = (h, t, pa, e)]) ->
  (forall h pa e, `Pr[ [% H, T, [% C, D, E] , [% A, N, Ot]] = (h, t, pa, e)] = 
    `Pr[H=h|[% A, ]]
  ) ->
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Einterv t)], 
      [% (Ainterv t), (Ninterv t), (Ointerv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, E] , [% A, N, Ot]] = (h, t, pa, e) ] 
        / `Pr[ T = t | [% C, D, E] = pa ]).



End SNSGPA.