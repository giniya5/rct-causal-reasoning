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


From Semantics Require Import FunctionRepresentation.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From CausalDiagrams Require Import Assignments.
(* From CausalDiagrams Require Import CausalPaths. *)

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section RCT.

Definition node : Type := nat.
Definition nodes := list node.

Definition edge : Type := node * node.
Definition edges := list edge.

Definition graph : Type := nodes * edges.

Variables R T H : node.
Hypothesis distinct_RTH : R <> T /\ R <> H /\ T <> H.

Lemma RCT_then_do_equiv:
  is_edge ((R, T) : edge) G = true ->
  (forall x, is_edge (x, R) G = false) ->
  (forall x, is_edge (R, x) G = true -> x = T) ->
  (forall x, is_edge (x, T) G = true -> x = R).
  (forall h t, `Pr[H h t] = `Pr[_do g H h T t]).
    
    is_edge (R, T) G = true



  
End RCT.