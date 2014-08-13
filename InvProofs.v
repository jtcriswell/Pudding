(*
 * Module: InvProofs
 *
 * Description:
 *  Prove that certain invariants needed for the core proofs hold when
 *  executing SVA instructions.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.

(* Load SVAOS specific modules *)
Require Export Semantics.
Require Export ThreadProofs.

(*
 * Theorem: alwaysGoodTH
 *
 * Description:
 *  Prove that the trap handler function within the configuration always
 *  remains within the CFG.
 *)
Theorem alwaysGoodTH : forall (c1 c2 : config),
(c1 ==> c2) /\
(In (getTH c1) (getCFG c1)) ->
(In (getTH c2) (getCFG c2)).
Proof.
intros.
destruct H as [H1 H2].
destruct H1.
destruct c.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
simpl.
apply H.
auto.
auto.
auto.
Qed.

