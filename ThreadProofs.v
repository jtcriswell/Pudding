(*
 * Module: ThreadProofs
 *
 * Description:
 *  Prove useful theorems about threads and the semantics of SVA-OS.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.

(* Load SVAOS specific modules *)
Require Export Semantics.

(*
 * Theorem: updateEmptyThreadList
 *
 * Description:
 *  Prove that updating an empty thread list yields an empty thread list.  I
 *  would think that this would be obvious, but apparently Coq needs to be
 *  convinced.
 *)
Theorem updateEmptyThreadList: forall (tid : nat) (t : SVAThread),
updateThread tid t nil = nil.
Proof.
intros.
destruct tid.
auto.
unfold updateThread.
auto.
Qed.

(*
 * Theorem: updateDifferentThread
 *
 * Description:
 *  Show that updating a thread ID in a thread list will return the same thread
 *  for threads with a different thread ID.
 *)
Theorem updateDifferentThread : forall (tid ntid : nat)
                                       (t : SVAThread)
                                       (tl : ThreadList),
tid <> ntid -> (getThread tid tl) = (getThread tid (updateThread ntid t tl)).
Proof.
intros.
generalize dependent tid.
generalize dependent ntid.
induction tl.

(* Case 1: Base case *)
intros.
destruct ntid.

(* Case 1a: Updating first thread *)
auto.

(* Case 1b: Updating not the first thread *)
auto.

(* Case 2: Induction case *)
intros.
destruct tid.
destruct ntid.

(* Case 2a: Get first, update first *)
contradiction H.
auto.

(* Case 2b: Get first, update not first *)
simpl.
unfold getThread.
auto.

(* Case 2c: Get not first, update not first *)
unfold getThread.
simpl.
destruct ntid.

simpl.
auto.

simpl.
apply IHtl.
contradict H.
rewrite -> H.
auto. 
Qed.

(*
 * Theorem: addValidThread
 *
 * Description:
 *  Show that adding a valid thread to a valid thread list yields a valid
 *  thread list.
 *)
Theorem addValidThread : forall (t   : SVAThread)
                                (tl  : ThreadList)
                                (cfg : list nat)
                                (mmu : MMU)
                                (ds  : store),
(validThread t cfg mmu ds) /\
(validThreadList tl cfg mmu ds) -> validThreadList (t :: tl) cfg mmu ds.
Proof.
intros.
destruct H as [H1 H2].
unfold validThreadList.
split.

(* Case 1 *)
auto.

(* Case 2 *)
auto.
Qed.

(*
 * Theorem: replaceValidThread
 *
 * Description:
 *  Show that replacing a thread in a thread list with another valid thread
 *  keeps the entire thread list valid.
 *)
Theorem replaceValidThread : forall (t : SVAThread)
                                    (tl  : ThreadList)
                                    (cfg : list nat)
                                    (mmu : MMU)
                                    (ds  : store)
                                    (n   : nat),
(validThread t cfg mmu ds) /\ (validThreadList tl cfg mmu ds)
-> 
validThreadList (updateThread n t tl) cfg mmu ds.
Proof.
intros t tl mmu cfg ds.
induction tl.

(* Cases 1 and 2 *)
intros.
destruct H as [H1 H2].
induction n.
auto.
auto.

(* Case 3 *)
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
fold validThreadList in H3.

assert (validThreadList (a :: tl) mmu cfg ds).
apply addValidThread.
auto.

destruct n.
simpl.
auto.

unfold updateThread.
simpl.
fold updateThread.
auto.
Qed.

(*
 * Theorem: validThreadMMU
 *
 * Description:
 *  This theorem shows that modifying the mapping for an address that is not
 *  the PC in an SVAThread does not make the thread invalid.
 *)
Theorem validThreadMMU : forall (t : SVAThread)
                                (c1 : config)
                                (tlb : TLBTy)
                                (v p : nat),
(validConfig c1) /\
(validThread t (getCFG c1) (getCMMU c1) (getStore c1)) /\
(((canThreadSwap t) = true) -> (v <> (getThreadPC t)) /\ (v <> ((getThreadPC t) - 1)))
-> 
(validThread t (getCFG c1) (updateTLB v tlb (getCMMU c1)) (getStore c1)).
Proof.
intros.
destruct c1.
simpl.
simpl in H.
destruct H as [H1 H].
destruct H as [H2 H].
destruct t.
destruct b.

(* Case 1: The thread holds valid processor state *)
simpl in H.
unfold validThread in H2.
unfold validThread.
destruct H as [H3 H4].
auto.
assert ((vLookup (n9 - 1) (updateTLB v tlb m) s) = (vLookup (n9 - 1) m s)).
rewrite <- sameMMURead.
auto.
auto.
rewrite -> H.
auto.

(* Case 2: The thread holds no valid state *)
auto.
Qed.

(*
 * Theorem: validThreadStore
 *
 * Description:
 *  This theorem shows that a thread is still valid if there is a write to a
 *  virtual address other then the program counter value within the tread.
 *)
Theorem validThreadStore : forall (t : SVAThread) (c : config) (v : nat) (n : tm),
((validConfig c) /\
(validThread t (getCFG c) (getCMMU c) (getStore c)) /\
(threadInText t (getCFG c) (getCMMU c) (getTextStart c) (getTextEnd c)) /\
(((canThreadSwap t) = true) ->
  (v <> (getThreadPC t)) /\
  (v <> ((getThreadPC t) - 1)) /\
  (not (In v (getCFG c))))) /\
(textMappedOnce c)
->
(validThread t (getCFG c) (getCMMU c) (replace (getPhysical (getTLB v (getCMMU c))) n (getStore c))).
Proof.
intros.
destruct c.
simpl.
simpl in H.
destruct t.
destruct b.

(* Case 1: The thread holds valid processor state *)
simpl in H.
destruct H as [H H1].
destruct H as [H H2].
destruct H2 as [H3 H2].
destruct H2 as [H4 H2].
destruct H4 as [H10 H11].
unfold validThread.
destruct H3 as [H5 | H6].
destruct H11 as [H12 | H13].
left.
auto.
left.
auto.
destruct H11 as [H12 | H13].
left.
auto.
right.
unfold vLookup in H6.
unfold vLookup.
rewrite <- sameRead.
auto.

apply H1.
rewrite <- pred_of_minus.
split.
auto.


destruct H2 as [H8 H2].
auto.
rewrite <- pred_of_minus in H2.
apply not_eq_sym.
apply H2.

(* Case 2: The thread holds no valid processor state *)
unfold validThread.
auto.
Qed.

(*
 * Theorem: threadsAlwaysValid
 *
 * Description:
 *  Prove that if the threads in a configuration are valid, then they remain
 *  valid after a step in the semantics is taken.
 *)
Theorem threadsAlwaysValid : forall (c1 c2 : config),
(validCFG c1 (getCFG c1)) /\ (validConfig c1) /\ (textNotWriteable c1) /\
(validThreadList (getThreadList c1) (getCFG c1) (getCMMU c1) (getStore c1)) /\
(getTextStart c1) <= (getPhysical (getTLB (getPC c1) (getCMMU c1))) <= (getTextEnd c1) /\
(threadListInText (getThreadList c1)
  (getCFG c1)(getCMMU c1) (getTextStart c1) (getTextEnd c1)) /\
(textMappedOnce c1) /\
(c1 ==> c2)
->
(validThreadList (getThreadList c2) (getCFG c2) (getCMMU c2) (getStore c2)).
Proof.
intros.
destruct H as [vcfg H].
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H4 H3].
destruct H3 as [H9 H3].
destruct H3 as [HA H3].
destruct H3 as [HE H3].
destruct H3.
destruct c.

(* Case 1 *)
auto.

(* Case 2 *)
auto.

(* Case 3 *)
simpl.
simpl in H1.
simpl in H2.
simpl in H4.
simpl in H9.
simpl in HA.
destruct H as [H5 H6].
destruct H6 as [H6 H7].
destruct H7 as [H7 H8].
induction tl.

(* Case 3a *)
auto.

(* Case 3b *)
destruct HA as [HA HB].
fold threadListInText in HB.
unfold validThreadList.
split.
destruct a.
destruct b.

(* Case 3ba: The first thread can be swapped *)
unfold threadInText in HA.
destruct HA as [HA HC].
destruct HC as [HC | HC].
unfold validThread.
left.
auto.


assert (n <> n0).
contradict HA.
rewrite <- HA.
contradict HA.

assert (~ canWrite n MMU).
apply H2.
auto.
contradiction.

assert (CFG = (getCFG (C MMU DS Reg PC SP CFG cs ce st asid tid ntid
          ((Thread true n0 i i0) :: tl) gvs gve gl th))).
auto.
assert (MMU = (getCMMU (C MMU DS Reg PC SP CFG cs ce st asid tid ntid
          ((Thread true n0 i i0) :: tl) gvs gve gl th))).
auto.
assert (DS = (getStore (C MMU DS Reg PC SP CFG cs ce st asid tid ntid
          (Thread true n0 i i0 :: tl) gvs gve gl th))).
auto.
rewrite -> H0.
rewrite -> H3.
rewrite -> H10.
apply validThreadStore.
simpl.
split.
split.
auto.
split.
unfold validThreadList in H4.
destruct H4.
unfold validThread in H4.
apply H4.
split.
auto.
split.
auto.
split.
contradict H7.
rewrite -> H7.
apply H2.
rewrite <- pred_of_minus.
unfold threadInText in HA.
destruct HA as [HA HD].
apply HC.
simpl in IHtl.
simpl in vcfg.
unfold validCFG in vcfg.
apply cfg23 in vcfg.
simpl in vcfg.
unfold validCFG3 in vcfg.
assert ((In n CFG) -> (cs <= getPhysical (getTLB n MMU) <= ce)).
apply vcfg.
contradict H12.
assert (cs <= getPhysical (getTLB n MMU) <= ce).
apply vcfg.
auto.
assert (not (canWrite n MMU)).
apply H2.
auto.
contradiction.
auto.


(* Case 3bb: The first thread cnnot be swapped *)
auto.
fold validThreadList.
apply IHtl.
auto.
unfold validThreadList in H4.
destruct H4.
fold validThreadList in H0.
auto.
auto.
auto.

(* Case 4 *)
auto.

(* Case 5 *)
auto.

(* Case 6 *)
auto.

(* Case 7 *)
simpl.
simpl in H1.
simpl in H2.
simpl in H4.
simpl in H9.
simpl in HA.
destruct H as [H10 H].
destruct H as [H11 H].
destruct H as [H12 H].
destruct H as [H13 H].
destruct H as [H14 H].
destruct H as [H15 H].
destruct H as [H16 H].
induction tl.

(* Case 7a: Show that it's true for an empty thread list *)
auto.

(* Case 7b: Show that it's true for an existing list *)
unfold validThreadList.
split.

(* Case 7b1: Show that it's true for the first thread in the list *)
unfold validThreadList in H4.
destruct H4.
fold validThreadList in H3.
destruct a.
destruct b.

(* Case 7b1a: Show that it's true for the first thread in the list if it's swappable *)


(* Detour: Show that n <> v *)
assert (n <> v).
unfold threadListInText in HA.
destruct HA as [HB HA].
fold threadListInText in HA.
unfold threadInText in HB.
simpl in HB.
destruct HB as [HB HD].
rewrite -> H12 in H14.
contradict HB.
rewrite -> HB.
contradict HB.
destruct HB.
destruct H14.
contradict H4.
apply lt_not_le.
auto.
contradict H5.
apply lt_not_le.
auto.

(* Detour: Show that v <> (n - 1) *)
unfold threadListInText in HA.
destruct HA as [HB HA].
fold threadListInText in HA.
unfold threadInText in HB.
destruct HB as [HB HC].
destruct HC as [valid1 | valid2].
unfold validThread.
left.
auto.

assert (v <> (pred n)).
destruct HB as [HD HB].
rewrite -> H12 in H14.

contradict valid2.
rewrite <- valid2.
contradict valid2.
destruct valid2.
destruct H14.
contradict H7.
apply le_not_lt.
auto.

contradict H6.
apply lt_not_le.
auto.

(* Back from detour: Prove case 7b1b *)
assert (CFG = (getCFG (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th))).
auto.
assert (MMU = (getCMMU (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th))).
auto.
assert (DS = (getStore (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th))).
auto.
rewrite -> H6.
rewrite -> H7.
rewrite -> H8.
apply validThreadMMU.
auto.
simpl.
split.
apply H1.
unfold validThread in H0.
split.
apply H0.
intro.
split.
apply not_eq_sym.
apply H4.

(* Handle the case where we need that v <> n - 1 *)
rewrite <- pred_of_minus.
auto.

(* Case 7b1b: Show that it's true if the first thread is not swappable *)
auto.

(* Case 7b2 *)
fold validThreadList.
apply IHtl.
auto.
destruct H4.
fold validThreadList in H3.
auto.
destruct HA.
fold threadListInText in H3.
auto.
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
simpl.
apply replaceValidThread.
simpl in H1.
simpl in H2.
simpl in H4.
destruct H as [H5 H6].
destruct H6 as [H6 H7].
destruct H7 as [H7 H8].
split.
unfold validThread.
auto.
auto.

(* Case 13 *)
simpl.
apply replaceValidThread.
split.
destruct getThread.
destruct getThread.
unfold threadOnCPU.
unfold validThread.
right.
simpl.
rewrite <- minus_n_O.
unfold vLookup.
unfold vaLookup in H.
destruct H as [H17 H].
destruct H as [H18 H].
auto.
apply replaceValidThread.
split.
destruct getThread.
unfold threadOffCPU.
unfold validThread.
auto.
auto.

(* Case 14 *)
simpl.
simpl in HA.
apply replaceValidThread.
split.
unfold validThread.
auto.
auto.

(* Case 15 *)
simpl.
simpl in HA.
simpl in H4.
simpl in H9.
simpl in H1.
apply replaceValidThread.
split.
unfold validThread.
auto.
auto.

(* Case 16 *)
auto.

(* Case 17 *)
simpl.
unfold pushSIC.
apply replaceValidThread.
split.

(* Case 17a *)
unfold validThread.
auto.

(* Case 17b *)
auto.

(* Case 18 *)
simpl.
unfold popSIC.
apply replaceValidThread.
split.

(* Case 18a *)
simpl.
auto.

(* Case 18b *)
auto.

(* Case 19 *)
simpl.
unfold pushIC.
apply replaceValidThread.
split.

(* Case 19a *)
unfold validThread.
auto.

(* Case 19b *)
auto.
Qed.

(*
 * Theorem: getThreadExtraList
 *
 * Description:
 *  Prove that fetching a thread from the second element on in a list is the
 *  same as fetching the element from the list without its first element.
 *)
Theorem getThreadExtraList: forall (n : nat) (t : SVAThread) (tl : ThreadList),
(getThread (S n) (t :: tl)) = (getThread n tl).
Proof.
intros.
unfold getThread.
simpl.
auto.
Qed.

(*
 * Theorem: getThreadImpliesIn
 *
 * Description:
 *  Prove that if a thread fetched from a thread list is in that thread list,
 *  then it is in a list with an additional element on the front of the thread
 *  list.
 *)
Theorem getThreadImpliesIn: forall (n : nat) (t : SVAThread) (tl : ThreadList),
In (getThread n tl) tl -> In (getThread n tl) (t :: tl).
Proof.
intros.
generalize dependent t.
generalize dependent n.
induction tl.

(* Case 1: Base case *)
contradiction.

(* Case 2: Induction case *)
intros.
destruct n.

unfold getThread.
simpl.
auto.

unfold getThread.
simpl.
unfold getThread in H.
simpl in H.
destruct H.

right.
left.
auto.

right.
right.
auto.
Qed.

(*
 * Theorem: updateThreadStillThere
 *
 * Description:
 *  Prove that if a thread with a particular thread ID is in a thread list,
 *  then there is still a thread for that ID after any thread in the list is
 *  updated to have a new value.
 *)
Theorem updateThreadStillThere: forall (t : SVAThread)
                                       (tl : ThreadList)
                                       (tid ntid : nat),
(In (getThread tid tl) tl) /\ (tid < length tl) ->
(In (getThread tid (updateThread ntid t tl)) (updateThread ntid t tl)).
Proof.
intros.
destruct H as [H1 H2].
assert (tid < length (updateThread ntid t tl)).
rewrite <- updateMaintainsListLength.
auto.
apply nth_In.
auto.
Qed.

(*
 * Theorem: threadIDsAlwaysValid
 *
 * Description:
 *  Show that the relationship between the current thread ID and the next
 *  thread ID always holds.
 *)
Theorem threadIDsAlwaysValid: forall (c1 c2 : config),
(c1 ==> c2) /\ (validThreadIDs c1) -> (validThreadIDs c2).
Proof.
intros.
destruct H as [H1 H2].
destruct H1.

(* Case 1 *)
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

(* Case: svaInitStack *)
simpl.
simpl in H2.
rewrite <- updateMaintainsListLength.
split.
apply H2.
apply H.

(* Case: svaSwap *)
simpl.
rewrite <- updateMaintainsListLength.
rewrite <- updateMaintainsListLength.
split.
apply H.
apply H2.

(* Case: trap *)
simpl.
rewrite <- updateMaintainsListLength.
auto.

(* Case: iret *)
simpl.
rewrite <- updateMaintainsListLength.
auto.

(* Case: svaRegisterTrap *)
auto.

(* Case: svaSaveIcontext *)
simpl.
unfold pushSIC.
rewrite <- updateMaintainsListLength.
auto.

(* Case: svaLoadIContext *)
simpl.
unfold popSIC.
rewrite <- updateMaintainsListLength.
auto.

(* Case: svaPushFunction *)
simpl.
unfold pushIC.
rewrite <- updateMaintainsListLength.
auto.
Qed.

(*
 * Theorem: threadAlwaysThere
 *
 * Description:
 *  This theorem shows that if the current thread is in the thread list, it is
 *  still there after a step is taken in the semantics.
 *)
Theorem threadAlwaysThere: forall (c1 c2 : config),
(c1 ==> c2) /\
(validThreadIDs c1) /\
(In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1))
->
(In (getThread (getCurrThread c2) (getThreadList c2)) (getThreadList c2)).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H3 H2].
destruct H1.
destruct c.
simpl in H2.

(* Cases 1 - 13 *)
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

(* Case 14: svaInitStack *)
simpl.
simpl in H2.
apply updateThreadStillThere.
split.
auto.
apply H3.

(* Case 15: svaSwap *)
auto.

(* Case 16: trap *)
simpl.
simpl in H2.
apply updateThreadStillThere.
split.
apply updateThreadStillThere.
split.
apply nth_In.
apply H.
apply H.
rewrite <- updateMaintainsListLength.
apply H.
simpl.
simpl in H2.
apply updateThreadStillThere.
split.
auto.
apply H3.

(* Case 17: iret *)
simpl.
simpl in H2.
apply updateThreadStillThere.
split.
auto.
apply H3.

(* Case 18: svaRegisterTrap *)
auto.

(* Case 19: svaSaveIcontext *)
unfold pushSIC.
simpl.
simpl in H2.
apply updateThreadStillThere.
split.
auto.
apply H3.

(* Case 20: svaLoadIcontext *)
unfold popSIC.
simpl.
simpl in H2.
apply updateThreadStillThere.
split.
auto.
apply H3.

(* Case 21: svaPushFunction *)
unfold pushSIC.
simpl.
simpl in H2.
apply updateThreadStillThere.
split.
auto.
apply H3.
Qed.
