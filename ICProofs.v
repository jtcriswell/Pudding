(*
 * Module: ICProofs
 *
 * Description:
 *  Prove useful theorems about interrupt contexts.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.

(* Load SVAOS specific modules *)
Require Export Semantics.
Require Export ICText.

(*
 * Function: goodPCIC
 *
 * Description:
 *  Determine whether the program counter in an interrupt context has a value
 *  consistent with a control-flow integrity policy.
 *)
Definition goodPCIC (ic : InterruptContext)
                    (cfg : list nat)
                    (mmu : MMU)
                    (ds : store) :=
  (In (getICPC ic) cfg) \/
  ((vLookup ((getICPC ic) - 1) mmu ds) = trap) \/
  ((getICPC ic) = 0).

(*
 * Function: goodPCICL
 *
 * Description:
 *  Determine whether the program counters in a list of interrupt contexts has
 *  a value consistent with a control-flow integrity policy.
 *)
Fixpoint goodPCICL (icl : ICStack)
                   (cfg : list nat)
                   (mmu : MMU)
                   (ds : store) :=
   match icl with
   | nil => True
   | h :: t => (goodPCIC h cfg mmu ds) /\ (goodPCICL t cfg mmu ds)
 end.

(*
 * Function: goodPCInIC
 *
 * Description:
 *  Determine whether all the Interrupt Contexts for the thread have a
 *  program counter that is either a valid function target or follows a trap
 *  instruction.
 *)
Definition goodPCInIC (t : SVAThread)
                      (cfg : list nat)
                      (mmu : MMU)
                      (ds : store) :=
  (goodPCICL (getThreadICL t) cfg mmu ds).

Definition goodPCInSIC (t : SVAThread)
                       (cfg : list nat)
                       (mmu : MMU)
                       (ds : store) :=
  (goodPCICL (getThreadSICL t) cfg mmu ds).

(*
 * Function: goodPCInTL
 *
 * Description:
 *  Determine whether all threads in a thread list satisfy goodPCInIC.
 *)
Fixpoint goodPCInTL (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) :=
  match tl with
  | nil => True
  | h :: t => (goodPCInIC h cfg mmu ds) /\ (goodPCInTL t cfg mmu ds)
  end.

Fixpoint goodSPCInTL (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) :=
  match tl with
  | nil => True
  | h :: t => (goodPCInSIC h cfg mmu ds) /\ (goodSPCInTL t cfg mmu ds)
  end.

(*
 * Function: goodPCInConfigIC
 *
 * Description:
 *  Convenience wrapper for goodPCInTL.
 *)
Definition goodPCInConfigIC (c : config) :=
  goodPCInTL (getThreadList c) (getCFG c) (getCMMU c) (getStore c).

Definition goodPCInConfigSIC (c : config) :=
  goodSPCInTL (getThreadList c) (getCFG c) (getCMMU c) (getStore c).

(*
 * Theorem: popInText
 *
 * Description:
 *  Show that popping an element off of an interrupt context list does not
 *  change whether ICListInText holds.
 *)
Theorem popInText: forall (icl : list InterruptContext)
                          (cs ce : nat)
                          (mmu : MMU),
ICListInText icl cs ce mmu ->
ICListInText (pop icl) cs ce mmu.
Proof.
intros.
induction icl.

(* Case 1: Base case: empty list *)
auto.

(* Case 2: Induction case: non-empty list *)
unfold ICListInText in H.
destruct H as [H1 H2].
fold ICListInText in H2.
unfold pop.
auto.
Qed.

(*
 * Theorem: addPCInICThread
 *
 * Description:
 *  Show that if goodPCInIC holds for a thread and a list of threads, then it
 *  also holds for a new list with the singular thread prepended.
 *)
Theorem addPCInICThread: forall (t : SVAThread) (tid f : nat) (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store),
(goodPCInIC t cfg mmu ds) /\ goodPCInTL tl cfg mmu ds ->
goodPCInTL (t :: tl) cfg mmu ds.
Proof.
intros.
destruct H as [H1 H2].
induction tl.

(* Case 1: Base case *)
unfold goodPCInTL.
split.
auto.
auto.

(* Case 2: Inductive case *)
unfold goodPCICL.
split.
auto.
split.
destruct H2 as [H2 H3].
auto.
fold goodPCInTL.
destruct H2 as [H2 H3].
auto.
Qed.

(*
 * Theorem: replacePCInICThread
 *
 * Description:
 *   Show that replacing a thread for which goodPCInIC holds does not change
 *   whether goodPCInIC holds for all elements of a thread list.
 *)
Theorem replacePCInICThread: forall (t : SVAThread) (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (tid : nat),
(goodPCInIC t cfg mmu ds) /\ goodPCInTL tl cfg mmu ds ->
goodPCInTL (updateThread tid t tl) cfg mmu ds.
Proof.
intros t tl cfg mmu ds.
induction tl.

(* Case 1: Base case *)
intros.
destruct H as [H1 H2].
induction tid.
auto.
auto.

(* Case 2 *)
intros.
destruct H as [H2 H3].
destruct tid.

(* Case 2a *)
simpl.
unfold goodPCInTL in H3.
destruct H3 as [H3 H4].
auto.

(* Case 2b *)
simpl.
destruct H3 as [H3 H4].
auto.
Qed.

(*
 * Theorem: replacePCInSICThread
 *
 * Description:
 *   Show that replacing a thread for which goodPCInSIC holds does not change
 *   whether goodPCInSIC holds for all elements of a thread list.
 *)
Theorem replacePCInSICThread: forall (t : SVAThread) (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (tid : nat),
(goodPCInSIC t cfg mmu ds) /\ goodSPCInTL tl cfg mmu ds ->
goodSPCInTL (updateThread tid t tl) cfg mmu ds.
Proof.
intros t tl cfg mmu ds.
induction tl.

(* Case 1: Base case *)
intros.
destruct H as [H1 H2].
induction tid.
auto.
auto.

(* Case 2 *)
intros.
destruct H as [H2 H3].
destruct tid.

(* Case 2a *)
simpl.
unfold goodSPCInTL in H3.
destruct H3 as [H3 H4].
auto.

(* Case 2b *)
simpl.
destruct H3 as [H3 H4].
auto.
Qed.

Theorem goodPCInItop : forall (icl : ICStack) (cfg : list nat) (mmu : MMU) (ds : store),
  goodPCICL icl cfg mmu ds -> goodPCIC (itop icl) cfg mmu ds.
Proof.
intros.
destruct icl.

(* Case 1: Base case: list of interrupt contexts is empty *)
unfold itop.
simpl.
unfold goodPCIC.
right.
right.
auto.

(* Case 2: Induction case: non-empty list of interrupt contexts *)
unfold itop.
simpl.
destruct H as [H1 H2].
auto.
Qed.

(*
 * Theorem: pcInICLWrite
 *
 * Description:
 *  Show that modifying a virtual address not used as a PC within an Interrupt
 *  Context does not modify whether all the Interrupt Context PCs are good.
 *)
Theorem pcInICLWrite:
forall (icl : ICStack) (cfg : list nat) (mmu : MMU) (ds : store) (n : tm) (v : nat) (cs ce : nat),
((addrNotInICL v icl) /\ (goodPCICL icl cfg mmu ds) /\
(ICListInText icl cs ce mmu) /\
(not (cs <= (getPhysical (getTLB v mmu)) <= ce))) ->
(goodPCICL icl cfg mmu (replace (getPhysical (getTLB v mmu)) n ds)).
Proof.
intros.
generalize dependent n.
generalize dependent v.
induction icl.

(* Case 1: Base case: empty Interrupt Context list *)
intros.
unfold goodPCICL.
auto.

(* Case 2: Induction case: Non-empty Interrupt Context list *)
intros.
destruct H as [H1 H2].
unfold goodPCICL.
split.

(* Case 2a: Handle the first Interrupt Context in the list *)
unfold addrNotInICL in H1.
destruct H1 as [H1 H3].
fold addrNotInICL in H3.
unfold addrNotInIC in H1.
unfold goodPCIC.
destruct H1 as [H4 H5].
unfold goodPCICL in H2.
destruct H2 as [H1 H2].
fold goodPCICL in H2.
unfold goodPCIC in H1.
destruct H1 as [H1 H6].
destruct H1 as [H10 | H11].
left.
auto.
destruct H11 as [H11 | H12].
right.
left.
unfold vLookup.
unfold vLookup in H11.
rewrite <- sameRead.
rewrite -> H11.
auto.
rewrite <- pred_of_minus.

(* Show that the PC isn't in the text segment *)
destruct H2 as [H2 H7].
unfold ICListInText in H2.
destruct H2 as [H2 H12].
fold ICListInText in H12.
unfold ICInText in H2.
destruct H2 as [H20 H21].
contradict H21.
rewrite -> H21.
apply H7.
right.
right.
auto.

fold goodPCICL.
apply IHicl.
unfold addrNotInICL in H1.
split.
apply H1.
unfold goodPCICL in H2.
split.
apply H2.
split.
apply H2.
apply H2.
Qed.

(*
 * Theorem: pcInTLWrite 
 *
 * Description:
 *  This theorem states that the program counter within all the interrupt
 *  contexts of a thread list remains good even if a virtual address is written
 *  (so long as that virtual address is not a program counter value within
 *  the interrupt contexts within the thread list).
 *)
Theorem pcInTLWrite :
forall (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (n : tm) (v : nat) (cs ce : nat),
((addrNotInTLICL v tl) /\ (goodPCInTL tl cfg mmu ds) /\
(AreAllThreadICsInText2 tl mmu cs ce) /\
(not (cs <= (getPhysical (getTLB v mmu)) <= ce)))
->
goodPCInTL tl cfg mmu (replace (getPhysical (getTLB v mmu)) n ds).
Proof.
intros tl cfg mmu ds.
induction tl.

(* Case 1: Base case: empty thread list *)
intros.
unfold goodPCInTL.
auto.

(* Case 2: Induction case: non-empty thread list *)
intros.
destruct H as [H1 H2].
unfold goodPCInTL.
split.
apply pcInICLWrite with (cs := cs) (ce := ce).
split.
unfold addrNotInTLICL in H1.
apply H1.
unfold goodPCInTL in H2.
split.
apply H2.
split.
apply H2.
unfold In.
left.
auto.
apply H2.
fold goodPCInTL.
destruct H2 as [H2 H3].
assert (AreAllThreadICsInText2 tl mmu cs ce).
unfold  AreAllThreadICsInText2.
unfold  AreAllThreadICsInText2 in H3.
intros.
apply H3.
unfold In.
right.
auto.
apply IHtl with (cs := cs) (ce := ce).
split.
unfold addrNotInTLICL in H1.
apply H1.
unfold goodPCInTL in H2.
destruct H2 as [H2 H4].
split.
apply H4.
split.
apply H.
apply H3.
Qed.

(*
 * Theorem: swapOnPCIC
 *
 * Description:
 *  Show that the modifications for changing the swap state of a thread does
 *  not whether the thread list as a whole is true for goodPCInIC.
 *)
Theorem swapOnPCIC: forall (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (pc : nat) (tid : nat),
goodPCInTL tl cfg mmu ds ->
goodPCInIC (threadOnCPU pc (getThread tid tl)) cfg mmu ds.
Proof.
intros tl cfg mmu ds pc.
induction tl.

(* Case 1: Base case of tl *)
destruct tid.
auto.
auto.

(* Case 2: Induction case of tl *)
intros.
destruct H as [H1 H2].
fold goodPCInTL in H2.
destruct tid.

(* Case 2a: Updating first thread *)
unfold getThread.
simpl.
destruct a.
unfold threadOnCPU.
auto.

(* Case 2b: Updating second or later thread *)
unfold getThread.
simpl.
unfold getThread in IHtl.
auto.
Qed.

(*
 * Theorem: swapOffPCIC
 *
 * Description:
 *  Show that the modifications for changing the swap state of a thread does
 *  not whether the thread list as a whole is true for goodPCInIC.
 *)
Theorem swapOffPCIC: forall (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (tid : nat),
goodPCInTL tl cfg mmu ds ->
goodPCInIC (threadOffCPU (getThread tid tl)) cfg mmu ds.
Proof.
intros tl cfg mmu ds.
induction tl.

(* Case 1: Base case of tl *)
destruct tid.
auto.
auto.

(* Case 2: Induction case of tl *)
intros.
destruct H as [H1 H2].
fold goodPCInTL in H2.
destruct tid.

(* Case 2a: Updating first thread *)
unfold getThread.
simpl.
destruct a.
unfold threadOffCPU.
auto.

(* Case 2b: Updating second or later thread *)
unfold getThread.
simpl.
unfold getThread in IHtl.
auto.
Qed.

(*
 * Theorem: swapOnPCSIC
 *
 * Description:
 *  Show that the modifications for changing the swap state of a thread does
 *  not whether the thread list as a whole is true for goodPCInSIC.
 *)
Theorem swapOnPCSIC: forall (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (pc : nat) (tid : nat),
goodSPCInTL tl cfg mmu ds ->
goodPCInSIC (threadOnCPU pc (getThread tid tl)) cfg mmu ds.
Proof.
intros tl cfg mmu ds pc.
induction tl.

(* Case 1: Base case of tl *)
destruct tid.
auto.
auto.

(* Case 2: Induction case of tl *)
intros.
destruct H as [H1 H2].
fold goodPCInTL in H2.
destruct tid.

(* Case 2a: Updating first thread *)
unfold getThread.
simpl.
destruct a.
unfold threadOnCPU.
auto.

(* Case 2b: Updating second or later thread *)
unfold getThread.
simpl.
unfold getThread in IHtl.
auto.
Qed.

(*
 * Theorem: swapOffPCSIC
 *
 * Description:
 *  Show that the modifications for changing the swap state of a thread does
 *  not whether the thread list as a whole is true for goodPCInSIC.
 *)
Theorem swapOffPCSIC: forall (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (tid : nat),
goodSPCInTL tl cfg mmu ds ->
goodPCInSIC (threadOffCPU (getThread tid tl)) cfg mmu ds.
Proof.
intros tl cfg mmu ds.
induction tl.

(* Case 1: Base case of tl *)
destruct tid.
auto.
auto.

(* Case 2: Induction case of tl *)
intros.
destruct H as [H1 H2].
fold goodPCInTL in H2.
destruct tid.

(* Case 2a: Updating first thread *)
unfold getThread.
simpl.
destruct a.
unfold threadOffCPU.
auto.

(* Case 2b: Updating second or later thread *)
unfold getThread.
simpl.
unfold getThread in IHtl.
auto.
Qed.


(*
 * Theorem: popGoodPCICL
 *
 * Description:
 *  This theorem states that if a thread list has good program counter values,
 *  then so does the same thread list with the top-most element removed.
 *)
Theorem popGoodPCICL: forall (tl : ThreadList) (cfg : list nat) (mmu : MMU) (ds : store) (tid : nat),
goodPCICL (getThreadICList tid tl) cfg mmu ds ->
goodPCICL (pop (getThreadICList tid tl)) cfg mmu ds.
Proof.
intros tl cfg mmu ds.
induction tl.

(* Case 1: Base case for tl *)
intros.
destruct tid.
auto.
auto.

(* Case 2: Induction case for tl *)
intros.
destruct tid.

(* Case 2a: First thread in tl *)
unfold getThreadICList.
unfold getThread.
simpl.
unfold getThreadICList  in H.
unfold getThread in H.
simpl in H.
destruct getThreadICL.
auto.
unfold pop.
unfold goodPCICL in H.
destruct H as [H1 H2].
auto.

(* Case 2a: Other thread in tl *)
unfold getThreadICList.
unfold getThread.
simpl.
unfold getThreadICList  in H.
unfold getThread in H.
simpl in H.

apply IHtl.
auto.
Qed.

(*
 * Theorem: GoodPCICL
 *
 * Description:
 *  Show that having good program counters in all a thread list's interrupt
 *  contexts means that grabbing any thread's list of interrupt contexts will
 *  yield a list of interrupt contexts with good program counter values.
 *)
Theorem GoodPCICL: forall (tl : ThreadList)
                          (cfg : list nat)
(mmu : MMU)
(ds : store)
(tid : nat),
goodPCInTL tl cfg mmu ds -> goodPCICL (getThreadICList tid tl) cfg mmu ds.
Proof.
intros tl cfg mmu ds.
induction tl.

(* Case 1: Base case: empty thread list *)
intros.
destruct tid.
auto.
auto.

(* Case 2: Induction case: non-empty thread list *)
intros.
destruct tid.
unfold getThreadICList.
unfold getThread.
simpl.
destruct H as [H1 H2].
auto.

unfold getThreadICList.
unfold getThread.
simpl.
destruct H as [H1 H2].
fold goodPCInTL in H2.
apply IHtl.
auto.
Qed.

Theorem GoodPCSICL: forall (tl : ThreadList)
                           (cfg : list nat)
(mmu : MMU)
(ds : store)
(tid : nat),
goodSPCInTL tl cfg mmu ds -> goodPCICL (getThreadSICList tid tl) cfg mmu ds.
Proof.
intros tl cfg mmu ds.
induction tl.

(* Case 1: Base case: empty thread list *)
intros.
destruct tid.
auto.
auto.

(* Case 2: Induction case: non-empty thread list *)
intros.
destruct tid.
unfold getThreadSICList.
unfold getThread.
simpl.
destruct H as [H1 H2].
auto.

unfold getThreadSICList.
unfold getThread.
simpl.
destruct H as [H1 H2].
fold goodSPCInTL in H2.
apply IHtl.
auto.
Qed.

Theorem updateMMUICL : forall (t : SVAThread) (tlb : TLBTy) (cfg : list nat)
(mmu : MMU) (ds : store) (v : nat),
(addrNotInICL v (getThreadICL t)) /\
(goodPCInIC t cfg mmu ds) ->
(goodPCInIC t cfg (updateTLB v tlb mmu) ds).
Proof.
intros t tlb cfg mmu ds.
unfold goodPCInIC.
induction getThreadICL.


(* Case 1: Base case: Empty interrupt context list *)
intros.
unfold goodPCICL.
auto.

(* Case 2: Induction case: Non-empty interrupt context list *)
(* Note: Change definition to include that v <> PC - 1 *)
intros.
destruct H as [H1 H2].
unfold goodPCICL in H2.
destruct H2 as [H2 H3].
fold goodPCICL in H3.
unfold goodPCICL.
split.

(* Case 2a: Is the first thread in the list good? *)
unfold goodPCIC.
unfold goodPCIC in H2.
destruct H2 as [H4 | H5 ].
left.
auto.
destruct H5 as [H5 | H6].
right.
left.
unfold vLookup.
unfold vLookup in H5.
rewrite <- sameMMULookup.
auto.
unfold addrNotInICL in H1.
destruct H1 as [H1 H2].
unfold addrNotInIC in H1.
destruct H1 as [H1 H4].
rewrite <- pred_of_minus.
auto.
auto.

(* Case 2b: Is the rest of the tread list good? *)
fold goodPCICL.
apply IHi.
split.
destruct H1 as [H1 H4].
auto.
auto.
Qed.


Theorem updateMMUCIC : forall (tl : ThreadList) (tlb : TLBTy) (cfg : list nat) (mmu : MMU) (ds : store) (v :nat),
(addrNotInTLICL v tl) /\ (goodPCInTL tl cfg mmu ds) ->
(goodPCInTL tl cfg (updateTLB v tlb mmu) ds).
Proof.
intros tl tbl cfg mmu ds.
induction tl.

(* Case 1: Base case: Empty thread list *)
intros.
unfold goodPCInTL.
auto.

(* Case 2: Induction case: Non-empty thread list *)
intros.
destruct H as [H1 H2].
unfold goodPCInTL in H2.
destruct H2 as [H2 H3].
fold goodPCInTL in H3.

unfold goodPCInTL.
split.
apply updateMMUICL.
split.
unfold addrNotInTLICL in H1.
apply H1.
auto.

fold goodPCInTL.
apply IHtl.
split.
unfold addrNotInTLICL in H1.
destruct H1 as [H1 H4].
fold addrNotInTLICL in H4.
auto.
auto.
Qed.

(*
 * Theorem: pcInIC
 *
 * Description:
 *  This theorem shows that the PC in the top-most Interrupt Context for each
 *  thread is either a valid function target or follows a trap instruction for
 *  every instruction.
 *)
Theorem pcInIC: forall (c1 c2 : config),
(c1 ==> c2) /\
(goodPCInConfigIC c1) /\
(validConfig c1) /\
(textNotWriteable c1) /\
(ThreadICsInText (getThreadList c1) c1) /\
((getTextStart c1) <= (getPhysical (getTLB (getPC c1) (getCMMU c1))) <= (getTextEnd c1)) /\
(validCFG c1 (getCFG c1)) /\
(goodPCInConfigSIC c1) /\
(noWriteTLPC (getThreadList c1) (getCMMU c1))
-> (goodPCInConfigIC c2).
Proof.
intros.
destruct H as [step inv].
destruct inv as [inv valid].
destruct valid as [valid norw].
unfold goodPCInConfigIC.
unfold goodPCInConfigIC in inv.
destruct step.
destruct c.
simpl in inv.

(* Cases 1: ldi *)
auto.

(* Case 2: lda *)
auto.

(* Case 3: sta *)
simpl.
simpl in inv.
simpl in norw.

(* Use pcInTLWrite to show that the PCs are still good *)
apply pcInTLWrite with (cs := cs) (ce := ce).
split.

(*
 * Show that the write doesn't modify a value within the Interrupt Context
 * List
 *)
destruct norw as [norw1 norw2].
destruct norw2 as [norw3 norw2].
destruct norw2 as [norw4 norw2].
destruct norw2 as [norw5 norw2].
destruct norw2 as [norw6 norw2].
induction tl.
unfold addrNotInTLICL.
auto.
unfold addrNotInTLICL.
split.
destruct inv as [inv1 inv2].
fold goodPCInTL in inv2.
unfold goodPCInIC in inv1.
unfold noWriteTLPC in norw2.
destruct norw2 as [norw7 norw2].
induction getThreadICL.
unfold addrNotInICL.
auto.
unfold addrNotInICL.
split.
unfold addrNotInIC.
unfold noWritePCICL in norw7.
destruct norw7 as [norw7 norw8].
fold noWriteTLPC in norw2.
fold noWritePCICL in norw8.
unfold noWritePCIC in norw7.
simpl in norw7.
destruct norw7 as [wr1 wr2].
split.
contradict wr1.
rewrite -> wr1.
apply H.
contradict wr2.
rewrite -> wr2.
apply H.
fold addrNotInICL.
apply IHi.
unfold goodPCICL in inv1.
apply inv1.
fold noWriteTLPC in IHi.
unfold goodPCICL in inv1.
destruct inv1 as [inv1 inv3].
fold goodPCICL in inv3.
unfold noWritePCICL in norw7.
apply norw7.
fold noWriteTLPC.
auto.
fold addrNotInTLICL.
apply IHtl.
unfold goodPCInTL in inv.
apply inv.
auto.
apply addThreadICsInText with (t := a) (c := (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)).
simpl.
auto.
unfold validCFG.
simpl.
unfold validCFG in norw5.
apply norw5.
unfold goodPCInConfigSIC in norw6.
simpl in norw6.
unfold goodPCInConfigSIC.
simpl.
apply norw6.
destruct inv as [inv1 inv2].
fold goodPCInTL in inv2.
unfold validConfig in valid.
unfold ThreadICsInText in norw3.
destruct norw3 as [norw3a norw3b].
fold ThreadICsInText in norw3b.
unfold validCFG in norw5.
simpl in norw5.
unfold goodPCInConfigSIC in norw6.
simpl in norw6.
unfold noWriteTLPC in norw2.
destruct norw2 as [norw2a norw2b].
fold noWriteTLPC in norw2b.
auto.
split.
auto.
rewrite -> areAllIffAll in norw.
unfold AreAllThreadICsInText in norw.
simpl in norw.
split.
unfold AreAllThreadICsInText2.
apply norw.
destruct norw as [norw1 norw2].
destruct H as [H1 H].
destruct H as [H2 H].
destruct H as [H3 H].
contradict H3.
apply norw1.
auto.

(* Cases 4-6 *)
auto.
auto.
auto.

(* Case 7 *)
simpl.
simpl in inv.
simpl in norw.
destruct norw as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 H5].
apply updateMMUCIC.
split.

destruct H as [H10 H11].
destruct H11 as [H12 H11].
destruct H11 as [H13 H11].
destruct H11 as [H14 H11].
destruct H11 as [H15 H11].
destruct H11 as [H16 H11].
rewrite -> H13 in H15.
assert (tl = getThreadList ((C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th))).
simpl.
auto.
apply notInPCICL with (c := (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)).
simpl.
split.
auto.
apply H15.
auto.

(* Cases 8-13 *)
auto.
auto.
auto.
auto.
auto.
auto.

(* Case 14: svaInitStack *)
simpl.
simpl in inv.
simpl in norw.
destruct norw as [H1 norw].
destruct norw as [H2 norw].
destruct norw as [H3 norw].
destruct norw as [H4 norw].
destruct norw as [H5 norw].

(* Prove a potentially helpful fact *)
assert (AreAllThreadICsInText tl (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)).
apply areAllImpliesAll.
auto.

apply replacePCInICThread.

(* Split this into two cases *)
split.

(* Case a: Show that goodPCInIC holds *)
unfold goodPCInIC.
unfold getThreadICL.
unfold goodPCICL.
split.
apply goodPCInItop.
unfold goodPCInTL in inv.
apply GoodPCICL.
auto.
auto.

(* Case b: Show that goodPCInTL holds *)
auto.

(* Case 15 *)
simpl.
simpl in inv.
apply replacePCInICThread.
split.

(* Case 15a *)
apply swapOnPCIC.
auto.

(* Case 15b *)
apply replacePCInICThread.
split.

(* Case 15b1 *)
apply swapOffPCIC.
auto.

(* Case 15b2 *)
auto.

(* Case 16 *)
simpl.
apply replacePCInICThread.
split.

(* Case 16a *)
unfold push.
unfold goodPCInIC.
simpl.
split.
unfold goodPCIC.
right.
simpl.
rewrite <- minus_n_O.
destruct H as [H1 H2].
unfold vLookup.
unfold vaLookup in H2.
left.
apply H2.

(* Case 16b *)
unfold getThreadList in inv.
unfold getCMMU in inv.
unfold getCFG in inv.
simpl in inv.
unfold goodPCInTL in inv.
apply GoodPCICL.
auto.

(* Case 17 *)
auto.

(* Case 18 *)
simpl.
apply replacePCInICThread.
split.
unfold goodPCInIC.
simpl.
apply popGoodPCICL.
apply GoodPCICL.
auto.
auto.

(* Case 19 *)
simpl.
simpl in inv.
induction tl.

(* Case 19a *)
destruct tid.
unfold pushSIC.
auto.
unfold pushSIC.
auto.

(* Case 19b *)
simpl in IHtl.
destruct tid.
simpl.
auto.
destruct inv as [inv1 inv2].
fold goodPCInTL in inv2.
simpl.
split.
auto.
auto.

(* Case 20 *)
simpl.
apply replacePCInICThread.
split.

simpl.
unfold goodPCInIC.
unfold getThreadICL.
apply GoodPCICL.
auto.
auto.

(* Case 20 *)
simpl.
unfold popSIC.
apply replacePCInICThread.
split.

(* Case 20a *)
unfold goodPCInIC.
simpl.
split.
apply goodPCInItop.
apply GoodPCSICL.
simpl in norw.
destruct norw as [norw H1].
destruct H1 as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 H5].
unfold goodPCInConfigSIC in H4.
simpl in H4.
auto.
apply popGoodPCICL.
apply GoodPCICL.
simpl in inv.
auto.

(* Case 20b *)
auto.

(* Case 21 *)
simpl.
simpl in inv.
simpl norw.
unfold pushIC.
apply replacePCInICThread.
split.

(* Case 21a *)
unfold push.
unfold goodPCInIC.
simpl.
split.

(* Case 21a1 *)
unfold goodPCIC.
unfold getICPC.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
left.
auto.

(* Case 21a2 *)
apply popGoodPCICL.
apply GoodPCICL.
auto.

(* Case 21b *)
auto.
Qed.

(*
 * Theorem: updateThreadICL
 *
 * Description:
 *  This theorem shows that modifying a thread in a thread list with
 *  so that it contains a new thread with its ICs in the text segment
 *  maintains the invariant that all threads in the thread list have
 *  all of their ICs in the thread list.
 *)
Theorem updateThreadICL:
forall (t : SVAThread) (tl : ThreadList) (tid : nat) (c : config),
(AreAllThreadICsInText tl c) /\
(tid < length tl) /\
(ICListInText (getThreadICL t) (getTextStart c) (getTextEnd c) (getCMMU c))
->
(AreAllThreadICsInText (updateThread tid t tl) c).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
generalize dependent tid.
induction tl.

(* Case 1: Update an empty list *)
intros.
destruct tid.
auto.
auto.

(* Case 2: Update a non-empty list *)
intros.
destruct tid.

(* Case 2a: Update the first element of a non-empty list *)
unfold updateThread.
apply areAllImpliesAll.
unfold ThreadICsInText.
split.
auto.
fold ThreadICsInText.
apply areAllIffAll in H1.
unfold ThreadICsInText in H1.
destruct H1 as [H1 H4].
fold ThreadICsInText in H4.
auto.

(* Case 2b: Update the second (or later) element of a non-empty list *)
simpl in H2.
apply lt_S_n in H2.
unfold updateThread.
apply areAllImpliesAll.
unfold ThreadICsInText.
split.
apply H1.
unfold In.
auto.

fold ThreadICsInText.
fold updateThread.
apply areAllIffAll.
apply IHtl.
apply areAllIffAll in H1.
unfold ThreadICsInText in H1.
destruct H1 as [H1 H4].
fold ThreadICsInText in H4.
apply areAllIffAll.
auto.
auto.
Qed.

(*
 * Theorem: updateThreadSICL
 *
 * Description:
 *  This theorem shows that modifying a thread in a thread list with
 *  so that it contains a new thread with its SICs in the text segment
 *  maintains the invariant that all threads in the thread list have
 *  all of their ICs in the thread list.
 *)
Theorem updateThreadSICL:
forall (t : SVAThread) (tl : ThreadList) (tid : nat) (c : config),
(AreAllThreadSICsInText tl c) /\
(tid < length tl) /\
(ICListInText (getThreadSICL t) (getTextStart c) (getTextEnd c) (getCMMU c))
->
(AreAllThreadSICsInText (updateThread tid t tl) c).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
generalize dependent tid.
induction tl.

(* Case 1: Update an empty list *)
intros.
destruct tid.
auto.
auto.

(* Case 2: Update a non-empty list *)
intros.
destruct tid.

(* Case 2a: Update the first element of a non-empty list *)
unfold updateThread.
apply SICareAllImpliesAll.
unfold ThreadICsInText.
split.
auto.
fold ThreadICsInText.
apply SICareAllIffAll in H1.
unfold ThreadSICsInText in H1.
destruct H1 as [H1 H4].
fold ThreadSICsInText in H4.
auto.

(* Case 2b: Update the second (or later) element of a non-empty list *)
simpl in H2.
apply lt_S_n in H2.
unfold updateThread.
apply SICareAllImpliesAll.
unfold ThreadSICsInText.
split.
apply H1.
unfold In.
auto.

fold ThreadSICsInText.
fold updateThread.
apply SICareAllIffAll.
apply IHtl.
apply SICareAllIffAll in H1.
unfold ThreadSICsInText in H1.
destruct H1 as [H1 H4].
fold ThreadSICsInText in H4.
apply SICareAllIffAll.
auto.
auto.
Qed.

Theorem updateMMUICInText:
forall (cs ce : nat) (mmu : MMU) (tlb : TLBTy) (v : nat) (ic : InterruptContext),
(addrNotInIC v ic) /\ (ICInText ic cs ce mmu) -> (ICInText ic cs ce (updateTLB v tlb mmu)).
Proof.
intros.
destruct H as [H1 H2].
unfold ICInText.
split.
unfold addrNotInIC in H1.
destruct H1 as [H3 H4].
rewrite <- sameMMULookup.
apply H2.
auto.
rewrite <- sameMMULookup.
apply H2.
apply H1.
Qed.

Theorem updateMMUICListInText:
forall (cs ce : nat) (mmu : MMU) (tlb : TLBTy) (v : nat) (icl : list InterruptContext),
(addrNotInICL v icl) /\ (ICListInText icl cs ce mmu) -> (ICListInText icl cs ce (updateTLB v tlb mmu)).
Proof.
intros.
destruct H as [H1 H2].
induction icl.

(* Case 1: Base case: Empty Interrupt Context List *)
auto.

(* Case 2: Induction case: Non-empty Interrupt Context List *)
unfold addrNotInICL in H1.
destruct H1 as [H1 H3].
fold addrNotInICL in H3.

unfold ICListInText in H2.
destruct H2 as [H2 H4].
fold ICListInText in H4.

unfold ICListInText.
split.
apply updateMMUICInText.
auto.
fold ICListInText.
apply IHicl.
auto.
auto.
Qed.

Theorem goodSICImpliesOut: forall (v cs ce : nat) (mmu : MMU) (icl : list InterruptContext),
(ICListInText icl cs ce mmu) /\
(getPhysical (getTLB v mmu) < cs \/ ce < getPhysical (getTLB v mmu))
->
(addrNotInICL v icl).
Proof.
intros.
destruct H as [H1 H2].
induction icl.

(* Case 1: Base case: Empty Interrupt Context list *)
auto.

(* Case 2: Induction case: Non-empty Interrupt Context list *)
unfold ICListInText in H1.
destruct H1 as [H3 H4].
fold ICListInText in H4.

unfold addrNotInICL.
fold addrNotInICL.
split.

destruct a.
unfold addrNotInIC.
simpl.
unfold ICInText in H3.
simpl in H3.
destruct H3 as [H5 H6].
split.

contradict H2.
rewrite <- H2.
apply and_not_or.
split.
apply le_not_lt.
apply H5.
apply le_not_lt.
apply H5.

contradict H2.
rewrite <- H2.
apply and_not_or.
split.
apply le_not_lt.
apply H6.
apply le_not_lt.
apply H6.

apply IHicl.
auto.
Qed.

Theorem goodTLImpliesGoodICL:
forall (t : SVAThread) (tl : ThreadList) (v : nat),

(In t tl) /\ (addrNotInTLICL v tl) -> addrNotInICL v (getThreadICL t).
Proof.
intros.
destruct H as [H1 H2].
induction tl.

(* Case 1: Base Case: Empty thread list *)
simpl in H1.
contradiction.

(* Case 2: Induction case: Non-empty thread list *)
unfold addrNotInTLICL in H2.
destruct H2 as [H2 H3].
fold addrNotInTLICL in H3.
simpl in H1.
destruct H1.

rewrite <- H.
auto.

apply IHtl.
auto.
auto.
Qed.

(*
 * Theorem: stayICInText
 *
 * Description:
 *  Show that executing an instruction keeps all of the program counters in all
 *  the interrupt contexts within the text segment.
 *)
Theorem stayICInText: forall (c1 c2 : config),
(c1 ==> c2) /\
(pcInText c1) /\
(AreAllThreadICsInText (getThreadList c1) (c1)) /\
(validThreadIDs c1) /\
(validCFG c1 (getCFG c1)) /\
(In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
(textMappedLinear c1) /\
(AreAllThreadSICsInText (getThreadList c1) (c1))
->
(AreAllThreadICsInText (getThreadList c2) (c2)).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 cfg].
destruct cfg as [cfg inThread].
destruct inThread as [inThread tml].
destruct tml as [tml sic].
destruct H1.

(* Cases 1 - 6 *)
destruct c.
auto.
auto.
auto.
auto.
auto.
auto.

(* Case 7: map *)
simpl.
unfold AreAllThreadICsInText.
simpl.
simpl in H3.
simpl in H2.
simpl in inThread.
simpl in tml.
simpl in sic.
simpl in cfg.
unfold AreAllThreadICsInText in H3.
simpl in H3.
intros.
apply updateMMUICListInText.
split.
assert (addrNotInTLICL v (getThreadList (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th))).
apply notInPCICL.
simpl.
split.
apply areAllIffAll.
auto.
destruct H as [I1 H].
destruct H as [I2 H].
destruct H as [I3 H].
destruct H as [I4 H].
destruct H as [I5 H].
rewrite -> I3 in I5.
auto.
unfold getThreadList in H1.

apply goodTLImpliesGoodICL with (tl := tl).
split.
auto.
auto.
auto.

(* Cases 8 - 13 *)
auto.
auto.
auto.
auto.
auto.
auto.

(* Case 14: svaInitStack *)
simpl.
simpl in H3.
apply updateThreadICL.
split.
simpl.
unfold AreAllThreadICsInText.
simpl.
unfold AreAllThreadICsInText in H3.
simpl in H3.
apply H3.
split.
destruct H as [H H1].
destruct H1 as [H1 H5].
destruct H4 as [H4 H6].
auto.
simpl.
unfold getThreadICList.
assert (In (getThread tid tl) tl).
apply nth_In.
apply H4.
split.
unfold ICInText.
apply ICListInTextImpliesICInText with (icl := (getThreadICL (getThread tid tl))).
apply H3.
apply H0.
auto.
apply nth_In.
apply H.
auto.

(* Case 15: svaSwap *)
simpl in H2.
simpl in H3.
simpl in inThread.
simpl in cfg.
apply updateThreadICL.
split.
simpl.
apply updateThreadICL.
split.
simpl.
unfold AreAllThreadICsInText.
simpl.
auto.
split.
apply H.
simpl.
apply threadOffICListInText.
apply H3.
apply nth_In.
apply H.
split.
rewrite <- updateMaintainsListLength with (t := (threadOffCPU (getThread vr tl))).
apply H4.
simpl.
apply threadOnICListInText.
auto.

(* Case 16: trap *)
simpl in H2.
simpl in H3.
simpl in inThread.
apply updateThreadICL.
split.
simpl.
unfold AreAllThreadICsInText.
simpl.
apply H3.
split.
apply H4.
simpl.
split.
unfold ICInText.
simpl.
split.
unfold textMappedLinear in tml.
simpl in tml.
assert (cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
      vlookup PC
        (C MMU DS (val r) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) =
      jmp).
apply tml.
auto.
destruct H0.
auto.
destruct H as [H H5].
contradict H0.
unfold vlookup.
simpl.
unfold vaLookup in H5.
unfold vLookup.
rewrite -> H5.
discriminate.
apply H2.
apply H3.
apply inThread.

(* Case 17: iret *)
simpl in H2.
simpl in H3.
simpl in inThread.
simpl.
apply updateThreadICL.
split.
simpl.
unfold AreAllThreadICsInText.
simpl.
apply H3.
split.
apply H4.
simpl.
apply popInText.
apply H3.
auto.

(* Case 18: svaRegisterTrap *)
auto.

(* Case 19: svaSaveIcontext *)
simpl in H2.
simpl in H3.
simpl in cfg.
unfold pushSIC.
apply updateThreadICL.
simpl.
split.
unfold AreAllThreadICsInText.
simpl.
auto.
split.
apply H4.
apply H3.
apply nth_In.
apply H4.

(* Case 20: svaLoadIcontext *)
simpl.
unfold popSIC.
apply updateThreadICL.
split.
simpl.
unfold AreAllThreadICsInText.
simpl.
auto.
split.
apply H4.
simpl.
split.
apply ICListInTextImpliesICInText with (icl := (getThreadSICList tid tl)).
apply sic.
apply inThread.
apply nth_In.
apply H.
apply popInText.
apply H3.
simpl.
auto.

(* Case 21: svaPushFunction *)
unfold pushIC.
simpl.
apply updateThreadICL.
split.
unfold AreAllThreadICsInText.
simpl.
simpl in H2.
unfold validThreadIDs in H4.
apply H3.
split.
apply H4.
simpl.
split.
unfold ICInText.
simpl.
simpl in H2.
simpl in cfg.
unfold validCFG in cfg.
simpl in cfg.
split.
destruct H as [canExec H].
destruct H as [inst H].
apply cfg23 in cfg.
unfold validCFG3 in cfg.
apply cfg.
auto.
apply cfg23 in cfg.
apply cfg.
apply H.
unfold AreAllThreadICsInText in H3.
simpl in H3.
unfold getThreadICList.
assert (In (getThread tid tl) tl).
apply nth_In.
apply H4.
apply popInText.
auto.
Qed.

(*
 * Theorem: staySICInText
 *
 * Description:
 *  Show that executing an instruction keeps all of the program counters in all
 *  the saved interrupt contexts within the text segment.
 *)
Theorem staySICInText: forall (c1 c2 : config),
(c1 ==> c2) /\
(pcInText c1) /\
(AreAllThreadICsInText (getThreadList c1) (c1)) /\
(validThreadIDs c1) /\
(validCFG c1 (getCFG c1)) /\
(In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
(textMappedLinear c1) /\
(AreAllThreadSICsInText (getThreadList c1) (c1))
->
(AreAllThreadSICsInText (getThreadList c2) (c2)).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 cfg].
destruct cfg as [cfg inThread].
destruct inThread as [inThread tml].
destruct tml as [tml sic].
destruct H1.

(* Cases 1 - 6 *)
destruct c.
auto.
auto.
auto.
auto.
auto.
auto.

(* Case 7: map *)
simpl.
unfold AreAllThreadSICsInText.
simpl.
simpl in H3.
simpl in H2.
simpl in inThread.
simpl in tml.
simpl in sic.
simpl in cfg.
unfold AreAllThreadSICsInText in sic.
simpl in sic.
intros.
apply updateMMUICListInText.
split.
apply goodSICImpliesOut with (cs := cs) (ce := ce) (mmu := MMU).
split.
apply sic.
auto.
destruct H as [I1 H].
destruct H as [I2 H].
destruct H as [I3 H].
destruct H as [I4 H].
destruct H as [I5 H].
rewrite -> I3 in I5.
auto.
apply sic.
auto.

(* Cases 8 - 13 *)
auto.
auto.
auto.
auto.
auto.
auto.

(* Case 14: svaInitStack *)
simpl.
simpl in H3.
apply updateThreadSICL.
split.
simpl.
unfold AreAllThreadSICsInText.
simpl.
unfold AreAllThreadSICsInText in H3.
simpl in H3.
apply sic.
split.
destruct H as [H H1].
destruct H1 as [H1 H5].
destruct H4 as [H4 H6].
auto.
simpl.
auto.

(* Case 15: svaSwap *)
simpl in H2.
simpl in H3.
simpl in inThread.
simpl in cfg.
apply updateThreadSICL.
split.
simpl.
apply updateThreadSICL.
split.
simpl.
unfold AreAllThreadSICsInText.
simpl.
auto.
split.
apply H.
simpl.
apply threadOffSICListInText.
apply sic.
apply nth_In.
apply H.
split.
rewrite <- updateMaintainsListLength with (t := (threadOffCPU (getThread vr tl))).
apply H4.
simpl.
apply threadOnSICListInText.
auto.

(* Case 16: trap *)
simpl in H2.
simpl in H3.
simpl in inThread.
apply updateThreadSICL.
split.
simpl.
unfold AreAllThreadSICsInText.
simpl.
apply sic.
split.
apply H4.
simpl.
apply sic.
apply inThread.

(* Case 17: iret *)
simpl in H2.
simpl in H3.
simpl in inThread.
simpl.
apply updateThreadSICL.
split.
simpl.
unfold AreAllThreadSICsInText.
simpl.
apply sic.
split.
apply H4.
simpl.
apply sic.
auto.

(* Case 18: svaRegisterTrap *)
auto.

(* Case 19: svaSaveIcontext *)
simpl.
unfold pushSIC.
apply updateThreadSICL.
split.
simpl.
unfold AreAllThreadSICsInText.
simpl.
auto.
split.
apply H4.
simpl.
split.
apply ICListInTextImpliesICInText with (icl := (getThreadICList tid tl)).
apply H3.
apply inThread.
apply nth_In.
apply H.
apply sic.
auto.

(* Case 20: svaLoadIcontext *)
unfold popSIC.
simpl.
apply updateThreadSICL.
split.
simpl.
unfold AreAllThreadSICsInText.
simpl.
auto.
split.
apply H4.
simpl.
apply popInText.
apply sic.
auto.

(* Case 21: svaPushFunction *)
unfold pushIC.
simpl.
apply updateThreadSICL.
split.
unfold AreAllThreadSICsInText.
simpl.
apply sic.
split.
apply H4.
simpl.
apply sic.
apply inThread.
Qed.
