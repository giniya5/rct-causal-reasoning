From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
Require Import Reals.
From infotheo.probability Require Import proba fdist.
Require Import List.
Import ListNotations.
From mathcomp Require Import reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require Import unstable mathcomp_extra reals exp.
From infotheo Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import Classical.
Require Import Field.
Require Import Lia.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import IntermediateNodes.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding Adjacency.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Check find_parents.

Definition find_descendants_set (N: nodes) (G: graph) : nodes :=
  flat_map (fun x => find_descendants x G) N.

Definition find_parents_set (N: nodes) (G: graph) : nodes :=
  flat_map (fun x => find_parents x G) N.

Lemma T_Z_dsep_given_paT :
  forall (G: graph) (T Z: nodes),
    G_well_formed G = true /\ contains_cycle G = false ->
    (* T is an antichain: no directed path between distinct members *)
    (forall t t', In t T -> In t' T -> t <> t' ->
       (~ In t (find_descendants t' G) \/ 
       ~ In t' (find_descendants t G))) ->
    (* Z avoids T, parents(T), and all descendants of T *)
    (forall z, In z Z ->
       ~ In z T /\
       ~ In z (find_descendants_set T G) /\
       ~ In z (find_parents_set T G) ) ->
    forall t z, In t T -> In z Z ->
      d_separated_bool t z G (find_parents_set T G) = true.