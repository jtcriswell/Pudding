(*
 * Module: MMU
 *
 * Description:
 *  This module defines data types, functions, lemma, and theorems to describe
 *  the basic architecture of the virtual machine that the formalism describes.
 *
 * Note:
 *  Some of the code for MMU and MMUSet comes from "Software Foundations" by
 *  Benjamin Pierce et. al.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.

(* Load SVAOS specific modules *)
Require Export Memory.
Require Export TLB.

(*
 * Define an MMU.  An MMU maps virtual addresses to physical address; it also
 * defines permissions for access through the virtual address.   For
 * simplicity, I will have the MMU map addresses at byte granularity.
 *)
Definition MMU := list TLBTy.
Definition emptyMMU := nil : list TLBTy.
Definition getTLB (n : nat) (mmu : MMU) := nth n mmu emptyTLB.
Fixpoint updateTLB (virt:nat) (tlb:TLBTy) (mmu:MMU) : MMU :=
  match mmu with
  | nil => nil
  | h :: t => 
    match virt with
    | O => tlb :: t
    | S n' => h :: updateTLB n' tlb t
    end
  end.

(*
 * Define a set of MMUs indexed by address space identifier (ASID).  This maps
 * an ASID to an MMU.
 *)
Definition MMUSet := list MMU.
Definition emptyMMUSet := nil : MMUSet.
Definition getMMU (asid : nat) (mmu : MMUSet) := nth asid mmu emptyMMU.
Fixpoint updateMMU (virt:nat) (asid : nat) (tlb:TLBTy) (mmus:MMUSet) : MMUSet :=
  match mmus with
  | nil => nil
  | h :: t => 
    match asid with
    | O => (updateTLB virt tlb h) :: t
    | S n' => h :: updateMMU virt n' tlb t
    end
  end.

(*
 * Function: can[Read|Write|Exec]
 *
 * Description:
 *   This function takes an MMU and a virtual address and determines if the
 *   virtual address permits read/write/execute permission.
 *
 * Inputs:
 *   va  - The virtual address that is being accessed.
 *   mmu - The MMU.
 *)
Definition canRead  (va : nat) (mmu : MMU) : Prop := TLBPermitsRead  (getTLB va mmu).
Definition canWrite (va : nat) (mmu : MMU) : Prop := TLBPermitsWrite (getTLB va mmu).
Definition canExec  (va : nat) (mmu : MMU) : Prop := TLBPermitsExec  (getTLB va mmu).

(*
 * Function: vLookup
 *
 * Description:
 *   Lookup the specified value via the MMU.
 *)
Definition vLookup (va : nat) (mmu : MMU) (st : store) :=
  lookup (getPhysical (getTLB va mmu)) st.

Definition vaLookup (va : nat) (asid : nat) (mmu : MMU) (st : store) :=
  lookup (getPhysical (getTLB va mmu)) st.

(*
Definition vaLookup (va : nat) (asid : nat) (mmus : MMUSet) (st : store) :=
  lookup (getPhysical (getTLB va (getMMU asid mmus))) st.
*)

(*
 * Lemma: noTLBinMMU
 *
 * Description:
 *  Prove that getting any value out of an empty TLB generates emptyTLB.
 *)
Lemma noTLBinMMU : forall (v : nat),
(getTLB v nil) = emptyTLB.
Proof.
intros.
induction v.
auto.
unfold getTLB.
simpl.
auto.
Qed.

(*
 * Lemma: updateEmptyMMU
 *
 * Description:
 *   Updating an empty MMU is the same as doing nothing.
 *)
Lemma updateEmptyMMU: forall (v : nat) (tlb : TLBTy), updateTLB v tlb nil = nil.
intros.
induction v.
auto.
auto.
Qed.

Lemma oneOrAnother : forall (v : nat) (tlb a : TLBTy) (mmu : MMU),
(updateTLB v tlb (a :: mmu) = tlb :: mmu) \/
(updateTLB v tlb (a :: mmu) = a :: (updateTLB (pred v) tlb mmu)).
Proof.
intros.
destruct v.

(* Handle the case when the virtual address is zero *)
left.
auto.

(* Handle the case in which the virtual address is non-zero *)
right.
simpl.
auto.
Qed.

Lemma skipTLB: forall (n : nat) (tlb : TLBTy) (mmu : MMU),
(getTLB (S n) (tlb :: mmu)) = (getTLB n (mmu)).
Proof.
intros.
unfold getTLB.
simpl.
reflexivity.
Qed.

Theorem sameMMULookup : forall (mmu : MMU) (n m : nat) (tlb : TLBTy),
 n <> m -> getTLB (n) (mmu) = getTLB (n) (updateTLB m tlb mmu).
Proof.
intro.
induction mmu.

(* Induction case 1 *)
intros.
rewrite -> updateEmptyMMU.
auto.

(* Induction case 2 *)
intros.
destruct n.
destruct m.

(* Destruct case 1 *)
contradiction H.
auto.

(* Destruct case 2 *)
simpl.
unfold getTLB.
simpl.
auto.

(* Destruct case 3 *)
destruct m.
unfold getTLB.
simpl.
auto.

rewrite -> skipTLB.
simpl.
rewrite -> skipTLB.
apply IHmmu.
auto.
Qed.

(*
 * Theorem: sameMMURead
 *
 * Description:
 *   Prove that looking up a value in the virtual memory does not depend on
 *   whether the TLB for another virtual address has been modified.
 *)
Theorem sameMMURead : forall (n m : nat) (tlb : TLBTy) (mmu : MMU) (ds : store),
 n <> m -> vLookup (n) mmu ds = vLookup (n) (updateTLB m tlb mmu) ds.
Proof.
intros.
unfold vLookup.
rewrite <- sameMMULookup.
auto.
apply H.
Qed.

Theorem diffTLBImpliesDiffVAs : forall (v1 v2 : nat) (mmu : MMU),
((getTLB v1 mmu) <> (getTLB v2 mmu)) -> v1 <> v2.
Proof.
intros.
contradict H.
rewrite -> H.
reflexivity.
Qed.

Theorem sameMMUPerms : forall (n m : nat) (tlb : TLBTy) (mmu : MMU),
 n <> m -> canWrite n mmu = canWrite n (updateTLB m tlb mmu).
Proof.
intros.
induction mmu.
unfold updateTLB.
simpl.
rewrite -> updateEmptyMMU.
auto.
destruct n.
destruct m.
contradiction H.
reflexivity.
simpl.
unfold canWrite.
unfold getTLB.
simpl.
auto.



destruct m.
simpl.
unfold canWrite.
unfold getTLB.
simpl.
auto.

unfold canWrite.
simpl.

rewrite -> skipTLB.
rewrite -> skipTLB.
assert (n <> m).
contradict H.
auto.
rewrite <- sameMMULookup.
auto.
auto.
Qed.

(*
 * Theorem: tlbSet
 *
 * Description:
 *  Prove that if there is a mapping for a virtual address in a TLB, then
 *  updating the MMU with the same virtual to physical mapping does not change
 *  the value of the TLB in the MMU.
 *)
Theorem tlbSet : forall (v : nat) (tlb : TLBTy) (mmu : MMU),
definedTLB (getTLB v mmu) -> getTLB v (updateTLB v tlb mmu) = tlb.
Proof.
intros.
generalize dependent tlb.
generalize dependent v.
induction mmu.

(* Induction case 1 *)
intros.
rewrite -> noTLBinMMU in H.
contradiction H.

(* Induction case 2 *)
intros.
destruct v.
auto.
simpl.
unfold getTLB.
simpl.
unfold getTLB in IHmmu.
apply IHmmu.
apply H.
Qed.

Lemma updateEmptyMMUS: forall (v asid : nat) (tlb : TLBTy), updateMMU v asid tlb nil = nil.
intros.
induction asid.
auto.
auto.
Qed.

Lemma noMMUinMMUS : forall (asid : nat),
(getMMU asid nil) = emptyMMU.
Proof.
intros.
induction asid.
auto.
unfold getMMU.
simpl.
auto.
Qed.

Lemma skipMMU: forall (asid : nat) (mmu : MMU) (mmus : MMUSet),
(getMMU (S asid) (mmu :: mmus)) = (getMMU asid mmus).
Proof.
intros.
unfold getTLB.
simpl.
reflexivity.
Qed.

Theorem sameMMUSet : forall (mmus : MMUSet) (v asid : nat) (tlb : TLBTy),
updateTLB v tlb (getMMU asid mmus) = getMMU asid (updateMMU v asid tlb mmus).
Proof.
intro.
induction mmus.

(* Case 1 *)
intros.
rewrite -> updateEmptyMMUS.
rewrite -> noMMUinMMUS.
rewrite -> updateEmptyMMU.
auto.

(* Case 2 *)
intros.
destruct asid.

(* Case 2a *)
auto.

(* Case 2b *)
rewrite -> skipMMU.
simpl.
rewrite -> skipMMU.
apply IHmmus.
Qed.

(*
 * Theorem: sameVALookup
 *
 * Description:
 *  This theorem shows that changing a mapping for one virtual address in a set
 *  of MMUs does not change the value returned for other virtual addresses
 *  within the same address space.
 *)
Theorem sameVALookup : forall (mmus : MMUSet) (v v0 asid : nat) (tlb : TLBTy),
v <> v0 -> (getTLB v (getMMU asid mmus)) = getTLB v (getMMU asid (updateMMU v0 asid tlb mmus)).
Proof.
intro.
induction mmus.


(* Case 1 *)
intros.
rewrite -> updateEmptyMMUS.
auto.

(* Case 2 *)
intros.
destruct asid.

(* Case 2a *)
unfold getMMU.
simpl.
apply sameMMULookup.
auto.

(* Case 2b *)
rewrite -> skipMMU.
simpl.
rewrite -> skipMMU.
apply IHmmus.
auto.
Qed.
