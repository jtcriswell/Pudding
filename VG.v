(*
 * Module: VG
 *
 * Description:
 *  This file contains proofs that properties of ghost memory are maintained.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import Arith.Lt.
Require Import List.
Require Import Coq.Logic.Classical_Prop.

(* Load SVAOS specific modules *)
Require Export Semantics.

(*
 * Theorem: ghostNoWrite
 *
 * Description:
 *  This theorem shows that a properly configured Virtual Ghost system does not
 *  write data into memory that backs the ghost memory address space partition.
 *)
Theorem ghostNoWrite : forall (c1 c2 : config) (gv : nat),
  ((validConfig c1) /\
  (c1 ==> c2) /\
  ((getGhostStart c1) <= gv <= (getGhostEnd c1)) /\
  ((In (getPhysical (getTLB gv (getCMMU c1))) (getGhost c1))) /\
  forall (v : nat), (v < (getGhostStart c1) \/ (getGhostEnd c1) < v) -> (not (In (getPhysical (getTLB v (getCMMU c1))) (getGhost c1))))
  ->
  (vLookup gv (getCMMU c1) (getStore c1)) =
  (vLookup gv (getCMMU c2) (getStore c2)).
Proof.
intros.
destruct H as [H1 H].
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
destruct H2.
destruct c.

(* Case 1 *)
auto.

(* Case 2 *)
auto.

(* Case 3 *)
simpl.
simpl in H1.
simpl in H3.
simpl in H4.
simpl in H.
destruct H0.
destruct H2.
destruct H5.

(* Show that the address accessed by the store is not a ghost frame *)
assert (not (In (getPhysical (getTLB n MMU)) gl)).
apply H.
auto.

unfold vLookup.

(* Prove that the two physical addresses being looked up are different *)
assert ((getPhysical (getTLB gv MMU)) <> (getPhysical (getTLB n MMU))).
contradict H7.
rewrite <- H7.
apply H4.

(* Resume main proof: show that the fetch isn't affected by the store *)
apply sameRead.
apply H8.

(* Case 4 *)
auto.

(* Case 5 *)
auto.

(* Subtraction case *)
auto.

(* Case 6 *)
simpl.
simpl in H1.
simpl in H3.
simpl in H4.
simpl in H.
destruct H0.
destruct H2.
destruct H5.
destruct H6.
destruct H7.
destruct H8.
destruct H9.

(* Show that we're not changing a ghost memory virtual address *)
assert (v <> gv).
destruct H8.
contradict H8.
rewrite -> H8.
apply le_not_lt.
apply H3.

contradict H8.
rewrite -> H8.
apply le_not_lt.
apply H3.

(* Now show that reading ghost memory will retrieve the same value *)
apply sameMMURead.
auto.

(* Case 7 *)
auto.

(* Case 8 *)
auto.
auto.

(* Case 9 *)
auto.
auto.

(* Case 10 *)
auto.

(* Case 11 *)
auto.

(* Case 12 *)
auto.

(* Case 13 *)
auto.

(* Case 14 *)
auto.

(* Case 15 *)
auto.

(* Case 16 *)
auto.

(* Case 17 *)
auto.

(* Case 18 *)
auto.
Qed.

(*
 * Theorem: ghostNoRead
 *
 * Description:
 *  This theorem shows that a properly configured Virtual Ghost system does not
 *  read data from memory that backs the ghost memory address space partition.
 *)
Theorem ghostNoRead : forall (c1 c2 : config) (gv : nat), exists tv,
  ((validConfig c1) /\
  (c1 ==> c2) /\
  ((getGhostStart c1) <= gv <= (getGhostEnd c1)) /\
  ((In (getPhysical (getTLB gv (getCMMU c1))) (getGhost c1))) /\
  ((getGhostStart c1) <= tv <= (getGhostEnd c1)) /\
  ((vlookup tv c1) = sec) /\
  ((getReg c1) <> (sec)) /\
  (forall (v : nat),
    (v < (getGhostStart c1) \/ (getGhostEnd c1) < v) ->
    (not (In (getPhysical (getTLB v (getCMMU c1))) (getGhost c1))) /\
    ((vlookup v c1) <> (sec))))
  ->
  ((getReg c2) <> (sec)).
Proof.
intros.
exists 2.
intros.
destruct H as [H1 H].
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
destruct H as [H5 H].
destruct H as [H6 H].
destruct H as [H7 H].
destruct H2.
destruct c.

(* Case 1 *)
simpl.
intro eq.
inversion eq.

(* Case 2 *)
simpl.
simpl in H.
simpl in H1.
simpl in H3.
simpl in H4.
unfold vlookup in H.
simpl in H.
destruct H0.
destruct H2.
destruct H8.
destruct H9.
rewrite <- H9.
apply H.
auto.

(* Case 3 *)
simpl.
simpl in H7.
auto.

(* Case 4 *)
simpl.
intro eq.
inversion eq.

(* Case 5 *)
simpl.
intro eq.
inversion eq.

(* Case 6 *)
simpl.
intro eq.
inversion eq.

(* Case 7 *)
simpl.
simpl in H7.
auto.

(* Case 8 *)
simpl.
simpl in H7.
auto.

(* Case 8a: jeq fallthrough *)
simpl.
auto.

(* Case 9 *)
simpl.
simpl in H7.
auto.


(* Case 9a: jne fallthrough *)
simpl.
auto.

(* Case 10 *)
simpl.
intro eq.
inversion eq.

(* Case 11 *)
simpl.
intro eq.
inversion eq.

(* Case 12 *)
simpl.
intro eq.
inversion eq.


(* Case 13 *)
simpl.
intro eq.
inversion eq.

(* Case 14 *)
simpl.
intro eq.
inversion eq.

(* Case 15 *)
auto.

(* Case 16 *)
auto.

(* Case 17 *)
auto.

(* Case 18 *)
auto.

(* Case 19 *)
auto.
Qed.
