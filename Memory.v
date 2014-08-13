(*
 * Module: Memory
 *
 * Description:
 *  This module defines data types, functions, lemma, and theorems to describe
 *  the physical memory of the system (often called the "store" in Programming
 *  Language Theory literature).
 *
 * Note:
 *  The code for the store comes from "Software Foundations" by Benjamin Pierce
 *  et. al.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.

(* Load SVAOS specific modules *)
Require Export Instructions.

(*
 * Define the store.  Reading an uninitialized address will result in reading
 * a zero.
 *)
Definition store := list tm.
Definition emptyStore := nil : list tm.
Definition lookup (n : nat) (st : store) := nth n st (val 0).
Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t => 
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.


(*
 * Lemma: writeEmptyStore
 *
 * Description:
 *   Writing to an empty store is the same as doing nothing.
 *)
Lemma writeEmptyStore: forall (n : nat) (v : Instructions.tm), replace n v nil = nil.
intros.
induction n.
auto.
auto.
Qed.

(*
 * Lemma: readEmptyStore
 *
 * Description:
 *  Reading two different addresses from an empty store result in the same
 *  value.
 *)
Lemma readEmptyStore: forall (n1 n2 : nat), lookup n1 nil = lookup n2 nil.
Proof.
intros.
induction n2.
induction n1.
auto.
auto.
assert (forall n : nat, lookup n nil = val 0).
intros.
induction n.
auto.
auto.
apply H.
Qed.

Lemma succRead: forall (n : nat) (v : Instructions.tm) (DS : store), lookup (S n) (v :: DS) = lookup n DS.
Proof.
intros.
unfold lookup.
auto.
Qed.

(*
 * Theorem: sameRead
 *
 * Description:
 *   Show that reading a location that hasn't been modified is the same as
 *   reading from an unmodified store.
 *)
Theorem sameRead : forall (DS : store) (n1 n2 : nat) (v : Instructions.tm),
(n1 <> n2) -> lookup (n1) DS = lookup (n1) (replace n2 v DS).
Proof.

intro DS.
induction DS.
intros.
rewrite -> writeEmptyStore.
reflexivity.
intros.
destruct n1.
destruct n2.
simpl.
contradiction H.
reflexivity.
simpl.
unfold lookup.
simpl.
reflexivity.


destruct n2.
simpl.
unfold lookup.
simpl.
reflexivity.
rewrite -> succRead.
simpl.
rewrite -> succRead.
apply IHDS.
auto.
Qed.
