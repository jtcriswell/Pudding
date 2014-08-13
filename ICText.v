(*
 * Module: ICText
 *
 * Description:
 *  This file provides functions and theorems about how the program counters in
 *  Interrupt Contexts relate to a configuration's text section.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.

(* Load SVAOS specific modules *)
Require Export Semantics.

(*
 * Function: ICInText
 *
 * Description:
 *  Determine whether the specified Interrupt Context is within the text
 *  section.  Note that both the Interrupt Context's current program counter
 *  and the virtual address before the program counter must be mapped into
 *  the code section.
 *)
Definition ICInText (ic : InterruptContext) (cs ce : nat) (mmu : MMU) :=
  cs <= (getPhysical (getTLB (getICPC ic) mmu)) <= ce /\
  cs <= (getPhysical (getTLB (pred (getICPC ic)) mmu)) <= ce.

(*
 * Function: ICListInText
 *
 * Description:
 *  Determine whether all Interrupt Contexts in a list are within the text
 *  section.
 *)
Fixpoint ICListInText (icl : list InterruptContext) (cs ce : nat) (mmu : MMU) :=
  match icl with
  | nil => True
  | h :: t => (ICInText h cs ce mmu) /\ (ICListInText t cs ce mmu)
  end.

(*
 * Function: ThreadICsInText
 *
 * Description:
 *  Determine whether all Interrupt Contexts in all the threads in a thread
 *  list have their program counters in the text segment.
 *)
Fixpoint ThreadICsInText (tl : ThreadList) (c : config) :=
  match tl with
  | nil => True
  | h :: t => (ICListInText (getThreadICL h) (getTextStart c) (getTextEnd c) (getCMMU c)) /\ (ThreadICsInText t c)
  end.

Fixpoint ThreadSICsInText (tl : ThreadList) (c : config) :=
  match tl with
  | nil => True
  | h :: t => (ICListInText (getThreadSICL h) (getTextStart c) (getTextEnd c) (getCMMU c)) /\ (ThreadSICsInText t c)
  end.

(*
 * Function: AreAllThreadICsInText
 *
 * Description:
 *  Determine whether all Interrupt Contexts in all the threads in a thread
 *  list have their program counters in the text segment.  This is equivalent
 *  to ThreadICsInText.
 *)
Definition AreAllThreadICsInText (tl : ThreadList) (c : config) :=
forall (t : SVAThread), (In t tl) -> (ICListInText (getThreadICL t) (getTextStart c) (getTextEnd c) (getCMMU c)).

Definition AreAllThreadICsInText2 (tl : ThreadList) (mmu : MMU) (cs ce: nat) :=
forall (t : SVAThread), (In t tl) -> (ICListInText (getThreadICL t) cs ce mmu).

Definition AreAllThreadSICsInText (tl : ThreadList) (c : config) :=
forall (t : SVAThread), (In t tl) -> (ICListInText (getThreadSICL t) (getTextStart c) (getTextEnd c) (getCMMU c)).

Definition addrNotInIC (v : nat) (ic : InterruptContext) :=
  ((getICPC ic) <> v) /\ ((pred (getICPC ic)) <> v).

Fixpoint addrNotInICL (v : nat) (icl : ICStack) :=
  match icl with
  | nil => True
  | h :: t => (addrNotInIC v h) /\ (addrNotInICL v t)
  end.

Fixpoint addrNotInTLICL (v : nat) (tl : ThreadList) :=
  match tl with
  | nil => True
  | h :: t => (addrNotInICL v (getThreadICL h)) /\ (addrNotInTLICL v t)
  end.

Definition addrInICL (v : nat) (icl : ICStack) :=
  forall (ic : InterruptContext), (In ic icl) -> not (addrNotInIC v ic).

(*
 * Function: noWritePCIC
 *
 * Description:
 *  Determine whether the program counter in the interrupt context is writeable.
 *)
Definition noWritePCIC (ic : InterruptContext) (mmu : MMU) :=
  (not (canWrite (getICPC ic) mmu)) /\
  (not (canWrite (pred (getICPC ic)) mmu)).

(*
 * Function: noWritePCICL
 *
 * Description:
 *  Determine whether all Interrupt Contexts in a list have non-writeable
 *  program counters.
 *)
Fixpoint noWritePCICL (icl : list InterruptContext) (mmu : MMU) :=
  match icl with
  | nil => True
  | h :: t => (noWritePCIC h mmu) /\ (noWritePCICL t mmu)
  end.

(*
 * Function: noWriteTLPC
 *
 * Description:
 *  Determine whether all Interrupt Contexts in all the threads in a thread
 *  list have non-writeable program counters.
 *)
Fixpoint noWriteTLPC (tl : ThreadList) (mmu : MMU) :=
  match tl with
  | nil => True
  | h :: t => (noWritePCICL (getThreadICL h) mmu) /\ (noWriteTLPC t mmu)
  end.

(*
 ******************************************************************************
 * Theorems
 ******************************************************************************
 *)

(*
 * Theorem: areAllImpliesAll
 *
 * Description:
 *  This theorem shows that ThreadICsInText implies AreAllThreadICsInText.
 *)
Theorem areAllImpliesAll: forall (tl : ThreadList) (c : config),
ThreadICsInText tl c -> AreAllThreadICsInText tl c.
Proof.
intros.
induction tl.

(* Case 1: Empty thread list *)
unfold AreAllThreadICsInText.
intros.
unfold In in H0.
contradiction.

(* Case 2: Induction step *)
unfold ThreadICsInText in H.
destruct H as [H1 H2].
fold ThreadICsInText in H2.
unfold AreAllThreadICsInText.
intros.
destruct H.

(* Case 2a: First thread *)
rewrite <- H.
auto.

(* Case 2b: The thread is not the first thread in the thread list *)
apply IHtl.
auto.
auto.
Qed.

(*
 * Theorem: areAllIffAll
 *
 * Description:
 *  This theorem shows that ThreadICsInText are AreAllThreadICsInText are
 *  equivalent.
 *)
Theorem areAllIffAll: forall (tl : ThreadList) (c : config),
ThreadICsInText tl c <-> AreAllThreadICsInText tl c.
Proof.
intros.
split.
apply areAllImpliesAll.
intros.
induction tl.

(* Case 1: Empty thread list *)
simpl.
auto.

(* Case 2: Induction step *)
unfold ThreadICsInText.
split.
unfold AreAllThreadICsInText in H.
apply H.
simpl.
auto.

fold ThreadICsInText.
apply IHtl.
unfold AreAllThreadICsInText in H.
unfold AreAllThreadICsInText.
intros.
apply H.
unfold In.
right.
apply H0.
Qed.

Theorem SICareAllImpliesAll: forall (tl : ThreadList) (c : config),
ThreadSICsInText tl c -> AreAllThreadSICsInText tl c.
Proof.
intros.
induction tl.

(* Case 1: Empty thread list *)
unfold AreAllThreadSICsInText.
intros.
unfold In in H0.
contradiction.

(* Case 2: Induction step *)
unfold ThreadSICsInText in H.
destruct H as [H1 H2].
fold ThreadSICsInText in H2.
unfold AreAllThreadSICsInText.
intros.
destruct H.

(* Case 2a: First thread *)
rewrite <- H.
auto.

(* Case 2b: The thread is not the first thread in the thread list *)
apply IHtl.
auto.
auto.
Qed.

Theorem SICareAllIffAll: forall (tl : ThreadList) (c : config),
ThreadSICsInText tl c <-> AreAllThreadSICsInText tl c.
Proof.
intros.
split.
apply SICareAllImpliesAll.
intros.
induction tl.

(* Case 1: Empty thread list *)
simpl.
auto.

(* Case 2: Induction step *)
unfold ThreadSICsInText.
split.
unfold AreAllThreadSICsInText in H.
apply H.
simpl.
auto.

fold ThreadSICsInText.
apply IHtl.
unfold AreAllThreadSICsInText in H.
unfold AreAllThreadSICsInText.
intros.
apply H.
unfold In.
right.
apply H0.
Qed.

(*
 * Theorem: ICListInTextImpliesICInText
 *
 * Description:
 *  Prove that if ICListInText holds for an entire list of interrupt contexts,
 *  then it must hold for an individual interrupt context within the list.
 *)
Theorem ICListInTextImpliesICInText:
forall (icl : list InterruptContext)
       (ic : InterruptContext)
       (cs ce : nat)
       (mmu : MMU),
(ICListInText icl cs ce mmu)
->
((In ic icl) -> (ICInText ic cs ce mmu)).
Proof.
intros.
induction icl.

(* Case 1: Base case: Empty thread list *)
unfold In in H0.
contradiction.

(* Case 2: Induction case: Non-empty thread list *)
unfold ICListInText in H.
destruct H as [H1 H2].
fold ICListInText in H2.

unfold In in H0.
destruct H0.

(* Case 2a: IC is first in list *)
rewrite <- H.
auto.

(* Case 2b: IC is in the rest of the list *)
apply IHicl.
auto.
auto.
Qed.

(*
 * Theorem: noWriteTLPCForAll
 *
 * Description:
 *  This theorem states that if noWriteTLPC holds for a longer thread list,
 *  then it also holds for the same thread list minus its first element.
 *)
Theorem noWriteTLPCForAll:
forall (mmu : MMU) (t : SVAThread) (tl : ThreadList),
(noWriteTLPC (t :: tl) mmu) -> (noWriteTLPC tl mmu).
Proof.
intros c t.
induction tl.

(* Case 1: Base case (empty list) *)
intros.
simpl.
auto.

(* Case 2: Induction case *)
unfold noWriteTLPC.
split.
apply H.
fold noWriteTLPC.
fold noWriteTLPC in H.
apply IHtl.
simpl.
split.
apply H.
apply H.
Qed.

Theorem notInPCICL : forall (c : config) (v : nat),
(ThreadICsInText (getThreadList c) c) /\
(getPhysical (getTLB v (getCMMU c)) < (getTextStart c) \/
  (getTextEnd c) < getPhysical (getTLB v (getCMMU c)))
->
addrNotInTLICL v (getThreadList c).
Proof.
intros c.
induction (getThreadList).

(* Case 1: Base case: empty thread list *)
intros.
unfold addrNotInTLICL.
auto.

(* Case 2: Induction case *)
intros.
destruct H as [H2 H1].
simpl in H1.
simpl in H2.
unfold addrNotInTLICL.
split.

(* Case 2a: Deal with the first thread in the list *)
induction getThreadICL.

(* Case 2a1: Empty Interrupt Context list *)
unfold addrNotInICL.
auto.

(* Case 1a2: Non-empty Interrupt Context list *)
unfold addrNotInICL.
split.
unfold addrNotInIC.
destruct H2 as [H2 H3].
unfold ICListInText in H2.
destruct H2 as [H2 H4].
fold ICListInText in H4.
unfold ICInText in H2.
destruct H2 as [H2 predH2].
destruct H2 as [H5 H6].
split.
contradict H1.
rewrite <- H1.
contradict H1.
destruct H1 as [H11 | H12].
apply lt_not_le in H11.
contradiction.
apply lt_not_le in H12.
contradiction.

destruct predH2 as [predH2 predH3].
contradict H1.
rewrite <- H1.
contradict H1.
destruct H1 as [H11 | H12].
apply lt_not_le in H11.
contradiction.
apply lt_not_le in H12.
contradiction.

(* Case 2b: Deal with the read of the thread list *)
fold addrNotInTLICL.
apply IHi.
split.
apply H2.
apply H2.
fold addrNotInTLICL.
apply IHt.
split.
apply H2.
auto.
Qed.

(*
 * Theorem: moreThreadICsInText
 *
 * Description:
 *  Show that having one less thread in a thread list maintains ThreadICsInText.
 *)
Theorem moreThreadICsInText:
forall (mmu: MMU)
       (ds : store)
       (Reg : tm)
       (PC SP : nat)
       (cfg : list nat)
       (cs ce : nat)
       (st : list Stack)
       (asid tid ntid : nat)
       (tl : ThreadList)
       (gvs gve : nat)
       (gl : list nat)
       (th : nat)
       (t : SVAThread),
ThreadICsInText tl
  (C mmu ds Reg PC SP cfg cs ce st asid tid ntid (t :: tl) gvs gve gl th) ->
ThreadICsInText tl
  (C mmu ds Reg PC SP cfg cs ce st asid tid ntid tl gvs gve gl th).
Proof.
intros.
induction tl.

(* Case 1: Base case: The thread list is empty *)
auto.

(* Case 2: Induction case *)
intros.
apply areAllIffAll.
apply areAllImpliesAll in H.
apply H.
Qed.

(*
 * Theorem: addThreadICsInText
 *
 * Description:
 *)
Theorem addThreadICsInText: forall (c : config) (t : SVAThread),
(ThreadICsInText (t :: (getThreadList c)) (setThreadList (t :: getThreadList c) c))
->
(ThreadICsInText (getThreadList c) c).
Proof.
intros.
unfold ThreadICsInText in H.
destruct H as [H1 H2].
fold ThreadICsInText in H2.
destruct c.
simpl in H1.
simpl in H2.
unfold ICListInText in H1.
unfold ThreadICsInText.
simpl.
fold ThreadICsInText.
apply moreThreadICsInText with (t := t).
auto.
Qed.

(*
 * Theorem: threadOnICListInText
 *
 * Description:
 *  Show that swapping a thread on to the CPU does not invalidate whether
 *  ICListInText holds on the Interrupt Context list.
 *)
Theorem threadOnICListInText:
forall (tl : ThreadList) (cs ce : nat) (mmu : MMU) (id : nat) (pc : nat),
ICListInText (getThreadICL (getThread id tl)) cs ce mmu ->
ICListInText (getThreadICL (threadOnCPU pc (getThread id tl))) cs ce mmu.
Proof.
intros.
generalize dependent id.
induction tl.

(* Case 1: Base case: empty list *)
intros.
destruct id.
auto.
auto.

(* Case 2: Induction case: non-empty list *)
intros.
destruct id.

(* Case 2a: Swapping off first element *)
unfold getThread.
simpl.
unfold getThread in H.
simpl in H.
destruct a.
simpl.
simpl in H.
auto.

(* Case 2b: Swapping off second or later element *)
unfold getThread in H.
simpl in H.
unfold getThread.
simpl.
apply IHtl.
auto.
Qed.

(*
 * Theorem: threadOffICListInText
 *
 * Description:
 *  Show that swapping a thread off of the CPU does not invalidate whether
 *  ICListInText holds on the Interrupt Context list.
 *)
Theorem threadOffICListInText:
forall (tl : ThreadList) (cs ce : nat) (mmu : MMU) (id : nat),
ICListInText (getThreadICL (getThread id tl)) cs ce mmu ->
ICListInText (getThreadICL (threadOffCPU (getThread id tl))) cs ce mmu.
Proof.
intros.
generalize dependent id.
induction tl.

(* Case 1: Base case: empty list *)
intros.
destruct id.
auto.
auto.

(* Case 2: Induction case: non-empty list *)
intros.
destruct id.

(* Case 2a: Swapping off first element *)
unfold getThread.
simpl.
unfold getThread in H.
simpl in H.
destruct a.
simpl.
simpl in H.
auto.

(* Case 2b: Swapping off second or later element *)
unfold getThread in H.
simpl in H.
unfold getThread.
simpl.
apply IHtl.
auto.
Qed.

(*
 * Theorem: threadOnSICListInText
 *
 * Description:
 *  Show that swapping a thread on to the CPU does not invalidate whether
 *  ICListInText holds on the saved Interrupt Context list.
 *)
Theorem threadOnSICListInText:
forall (tl : ThreadList) (cs ce : nat) (mmu : MMU) (id : nat) (pc : nat),
ICListInText (getThreadSICL (getThread id tl)) cs ce mmu ->
ICListInText (getThreadSICL (threadOnCPU pc (getThread id tl))) cs ce mmu.
Proof.
intros.
generalize dependent id.
induction tl.

(* Case 1: Base case: empty list *)
intros.
destruct id.
auto.
auto.

(* Case 2: Induction case: non-empty list *)
intros.
destruct id.

(* Case 2a: Swapping off first element *)
unfold getThread.
simpl.
unfold getThread in H.
simpl in H.
destruct a.
simpl.
simpl in H.
auto.

(* Case 2b: Swapping off second or later element *)
unfold getThread in H.
simpl in H.
unfold getThread.
simpl.
apply IHtl.
auto.
Qed.

(*
 * Theorem: threadOffSICListInText
 *
 * Description:
 *  Show that swapping a thread off of the CPU does not invalidate
 *  whether ICListInText holds on the saved Interrupt Context list.
 *)
Theorem threadOffSICListInText:
forall (tl : ThreadList) (cs ce : nat) (mmu : MMU) (id : nat),
ICListInText (getThreadSICL (getThread id tl)) cs ce mmu ->
ICListInText (getThreadSICL (threadOffCPU (getThread id tl))) cs ce mmu.
Proof.
intros.
generalize dependent id.
induction tl.

(* Case 1: Base case: empty list *)
intros.
destruct id.
auto.
auto.

(* Case 2: Induction case: non-empty list *)
intros.
destruct id.

(* Case 2a: Swapping off first element *)
unfold getThread.
simpl.
unfold getThread in H.
simpl in H.
destruct a.
simpl.
simpl in H.
auto.

(* Case 2b: Swapping off second or later element *)
unfold getThread in H.
simpl in H.
unfold getThread.
simpl.
apply IHtl.
auto.
Qed.

Theorem getNWTLPC: forall (c : config),
(textNotWriteable c) /\ (AreAllThreadICsInText (getThreadList c) c) ->
(noWriteTLPC (getThreadList c) (getCMMU c)).
Proof.
intros.
destruct H as [H1 H2].
destruct c.
simpl in H1.
unfold AreAllThreadICsInText in H2.
simpl in H2.
simpl.
induction t0.

(* Case 1: Base case: Empty thread list *)
unfold noWriteTLPC.
auto.

(* Case 2: Induction case: Non-empty thread list *)
unfold noWriteTLPC.
split.
assert (ICListInText (getThreadICL a) n1 n2 m).
apply H2.
unfold In.
auto.
induction (getThreadICL a).

(* Case 2a: Base case: Thread's ICL is empty *)
auto.

(* Case 2b: Induction case: Thread's ICL is not empty *)
unfold noWritePCICL.
split.
unfold noWritePCIC.
split.
apply H1.
unfold ICListInText in H.
destruct H as [H3 H].
fold ICListInText in H.
apply H3.
apply H1.
unfold ICListInText in H.
destruct H as [H3 H].
fold ICListInText in H.
apply H3.


fold noWritePCICL.
apply IHi.
unfold ICListInText in H.
destruct H as [H3 H].
fold ICListInText in H.
auto.

fold noWriteTLPC.
apply IHt0.
intros.
apply H2.
apply in_cons.
auto.
Qed.
