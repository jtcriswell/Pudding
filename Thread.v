(*
 * Module: Thread
 *
 * Description:
 *  This module defines an SVA Thread that is used in the small-step semantics.
 *
 * Note:
 *  Some of the code for the ThreadList comes from "Software Foundations" by
 *  Benjamin Pierce et. al.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import Bool.
Require Import List.

(* Load SVA Library Modules *)
Require Export IC.

(*
 * Define an SVA thread which includes the following fields:
 *
 *  o A boolean flag indicating whether the state can be swapped on to the CPU
 *  o A program counter value
 *  o A stack of interrupt contexts for interrupts
 *  o A stack of interrupt contexts for saving interrupt contexts
 *)
Inductive SVAThread : Type :=
  | Thread : bool ->
             nat ->
             ICStack ->
             ICStack ->
             SVAThread.
Definition emptyThread := Thread false 0 nil nil.

(*
 * Define a set of SVAThreads.
 *)
Definition ThreadList := list SVAThread.
Definition emptyTL := nil : list SVAThread.
Definition getThread (id : nat) (t : ThreadList) := nth id t emptyThread.
Fixpoint updateThread (id:nat) (thread:SVAThread) (tl:ThreadList) : ThreadList :=
  match tl with
  | nil => nil
  | h :: t => 
    match id with
    | O => thread :: t
    | S n' => h :: updateThread n' thread t
    end
  end.

Definition getThreadPC (t : SVAThread) :=
  match t with
  | Thread valid PC stack istack => PC
end.

Definition canThreadSwap (t : SVAThread) :=
  match t with
  | Thread canSwap PC stack istack => canSwap
end.

Definition getThreadICL (t : SVAThread) :=
  match t with
  | Thread canSwap PC stack istack => stack
  end.

Definition getThreadSICL (t : SVAThread) :=
  match t with
  | Thread canSwap PC stack istack => istack
  end.

Definition getThreadICList (id : nat) (tl : ThreadList) :=
  getThreadICL (getThread id tl).

Definition getThreadSICList (id : nat) (tl : ThreadList) :=
  getThreadSICL (getThread id tl).

Definition threadOnCPU (newpc : nat) (t : SVAThread) :=
  match t with
  | Thread canSwap PC stack istack => Thread true newpc stack istack
end.

Definition threadOffCPU (t : SVAThread) :=
  match t with
  | Thread canSwap PC stack istack => Thread false 0 stack istack
end.

Definition pushSIC (tid : nat) (tl : ThreadList) :=
  updateThread  tid
                (Thread
                  false
                  (getThreadPC (getThread tid tl))
                  (getThreadICList tid tl)
                  (push
                    (itop (getThreadICList tid tl))
                    (getThreadSICList tid tl)))
                tl.

Definition popSIC (tid : nat) (tl : ThreadList) :=
  updateThread  tid
                (Thread
                  false
                  (getThreadPC (getThread tid tl))
                  (push
                    (itop (getThreadSICList tid tl))
                    (pop (getThreadICList tid tl)))
                  (pop (getThreadSICList tid tl)))
                tl.

Definition pushIC (Reg PC SP: nat) (tid : nat) (tl : ThreadList) :=
  updateThread  tid
                (Thread
                  false
                  (getThreadPC (getThread tid tl))
                  (push (IC Reg PC SP 0) (pop (getThreadICList tid tl)))
                  (getThreadSICList tid tl))
                tl.
(*
 * Theorem: updateMaintainListLength
 *
 * Description:
 *  Prove that updating an element in a thread list does not modify
 *  its length.
 *)
Theorem updateMaintainsListLength: forall (tid : nat) (t :SVAThread) (tl :ThreadList),
length tl = length (updateThread tid t tl).
Proof.
intros.
generalize dependent tid.
induction tl.

(* Case 1: Base case: empty list *)
intros.
simpl.
unfold updateThread.
destruct tid.
auto.
auto.

(* Case 2: Induction case: non-empty thread list *)
intros.
simpl.
destruct tid.

unfold updateThread.
simpl.
auto.

unfold updateThread.
simpl.
auto.
Qed.


