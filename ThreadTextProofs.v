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
Require Export InvProofs.
Require Export ICProofs.

(*
 * Theorem: addThreadInText
 *
 * Description:
 *  Show that adding a thread that is in the text segment yields a thread list
 *  that is also in the text segment.
 *)
Theorem addThreadInText : forall (t     : SVAThread)
                                 (tl    : ThreadList)
                                 (cfg   : list nat)
                                 (mmu   : MMU)
                                 (cs ce : nat),
(threadInText t cfg mmu cs ce) /\
(threadListInText tl cfg mmu cs ce) -> threadListInText (t :: tl) cfg mmu cs ce.
Proof.
intros.
destruct H as [H1 H2].
unfold threadListInText.
split.

(* Case 1 *)
auto.

(* Case 2 *)
auto.
Qed.

(*
 * Theorem: replaceThreadInText
 *
 * Description:
 *  Show that replacing a thread in a thread list with another thread
 *  in the text segment keeps the entire thread list in the text segment.
 *)
Theorem replaceThreadInText : forall (t : SVAThread)
                                     (tl  : ThreadList)
                                     (cfg : list nat)
                                     (mmu : MMU)
                                     (cs ce n   : nat),
(threadInText t cfg mmu cs ce) /\ (threadListInText tl cfg mmu cs ce)
->
threadListInText (updateThread n t tl) cfg mmu cs ce.
Proof.
intros t tl cfg mmu cs ce.
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
fold threadListInText in H3.

assert (threadListInText (a :: tl) cfg mmu cs ce).
apply addThreadInText.
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
 * Theorem: textInThreadMMU
 *
 * Description:
 *  This theorem shows that modifying the mapping for an address that is not
 *  the PC in an SVAThread does not move the thread outside the text segment.
 *)
Theorem textInThreadMMU : forall (t : SVAThread)
                                 (cfg : list nat)
                                 (tlb : TLBTy)
                                 (mmu : MMU)
                                 (v cs ce : nat),
(threadInText t cfg mmu cs ce) /\
(((canThreadSwap t) = true) ->
  (v <> (getThreadPC t)) /\
  (not (In (getThreadPC t) cfg) -> v <> ((getThreadPC t) - 1)))
-> 
(threadInText t cfg (updateTLB v tlb mmu) cs ce).
Proof.
intros.
destruct H as [H1 H2].
destruct t.
destruct b.

(* Case 1: The thread holds valid processor state *)
unfold canThreadSwap in H2.
destruct H2.
auto.
simpl in H0.
unfold threadInText.
rewrite <- sameMMULookup.
split.
apply H1.
unfold threadInText in H1.
destruct H1 as [H1 H2].
apply imply_to_or in H0.
destruct H2 as [H2 | H2].
left.
auto.
destruct H0 as [H0 | H0].
apply NNPP in H0.
left.
auto.
right.
rewrite <- sameMMULookup.
auto.
rewrite <- pred_of_minus in H0.
apply not_eq_sym.
apply H0.
unfold getThreadPC in H.
apply not_eq_sym.
auto.

(* Case 2: The thread holds no valid state *)
auto.
Qed.


(*
 * Theorem: TLAlwaysInText
 *
 * Description:
 *  Show that the thread list stays within the text segment.
 *)
Theorem TLAlwaysInText: forall (c1 c2 : config),
(c1 ==> c2) /\
(threadListInText
  (getThreadList c1) (getCFG c1) (getCMMU c1) (getTextStart c1) (getTextEnd c1)) /\
(validCFG c1 (getCFG c1)) /\
(textMappedLinear c1) /\
(pcInText c1)
->
(threadListInText
  (getThreadList c2) (getCFG c2) (getCMMU c2) (getTextStart c2) (getTextEnd c2)).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 cfg].
destruct cfg as [cfg line].
destruct line as [line pct].
destruct H1.
destruct c.

(* Cases 1 - 6 *)
auto.
auto.
auto.
auto.
auto.
auto.

(* Case 7 *)
simpl.
simpl in H2.
destruct H as [H10 H].
destruct H as [H11 H].
destruct H as [H12 H].
destruct H as [H13 H].
destruct H as [H14 H].
destruct H as [H15 H].
destruct H as [H16 H].
induction tl.

(* Case 7a: Base case: empty thread list *)
auto.

(* Case 7b: Induction case: non-empty thread list *)
simpl in cfg.
simpl in IHtl.
unfold threadListInText.
split.

(* Case 7b1: Show that the first thread is in the text segment *)
unfold threadListInText in H2.
destruct H2 as [H2 H3].
fold threadListInText in H3.
apply textInThreadMMU.
split.

(* Case 7b1a: Show that the thread was valid before the MMU change. *)
auto.

(* Case 7b1b: Show that if the thread is valid, the map is not changing the PC value *)
destruct a.
destruct b.
simpl.
intros.
destruct H0.
unfold threadInText in H2.
destruct H2 as [H4 H5].
rewrite -> H12 in H14.
split.

(* Case 7b1b: Show that the map argument isn't the PC in the thread *)
contradict H14.
rewrite -> H14.
apply and_not_or.
split.
apply le_not_lt.
apply H4.
apply le_not_lt.
apply H4.

(* Case 7b1b: Show that if the thread was swapped, v isn't the previous address *)
rewrite <- pred_of_minus.
apply or_to_imply.
destruct H5.
left.
contradict H0.
auto.
right.
contradict H0.
rewrite <- H0.
contradict H0.
destruct H14 as [H14a | H14b].
destruct H0.
apply le_not_lt in H0.
contradiction.
destruct H0.
apply le_not_lt in H1.
contradiction.

(* Case 7b1c: The thread has not valid PC *)
simpl.
intros.
contradict H0.
auto.

fold threadListInText.
apply IHtl.
destruct H2 as [H2 H20].
auto.
auto.
auto.
auto.

(* Case 8 - 13 *)
auto.
auto.
auto.
auto.
auto.
auto.

(* Case 14 *)
simpl.
simpl in H2.
apply replaceThreadInText.
split.
simpl.
split.
simpl in cfg.
unfold validCFG in cfg.
simpl in cfg.
assert (validCFG3 CFG MMU cs ce).
apply cfg23.
auto.
unfold validCFG3 in H0.
apply H0.
apply H.
left.
apply H.
auto.

(* Case 15 *)
simpl.
simpl in H2.
apply replaceThreadInText.
split.

(* Case 15a: threadOnCPU is in Text *)
unfold textMappedLinear in line.
simpl in line.
unfold pcInText in pct.
simpl in pct.
assert ((cs <= getPhysical (getTLB (S PC) MMU) <= ce) \/
vlookup PC
         (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) =
       jmp).
apply line.
auto.
destruct H0.
destruct getThread.
destruct getThread.
simpl.
split.
auto.
right.
auto.
destruct H as [exec swap].
destruct swap as [swap canswap].
unfold vlookup in H0.
simpl in H0.
unfold vaLookup in swap.
unfold vLookup in H0.
contradict H0.
rewrite -> swap.
discriminate.

(* Case 15b: threadOffCPU is in Text *)
apply replaceThreadInText.
split.
destruct getThread.
unfold threadOffCPU.
simpl.
auto.
auto.

(* Case 17 *)
simpl.
apply replaceThreadInText.
split.
simpl.
auto.
auto.

(* Case 18 *)
simpl.
apply replaceThreadInText.
split.
simpl.
auto.
auto.

(* Case 19 *)
auto.

(* Case 20 *)
simpl.
unfold pushSIC.
apply replaceThreadInText.
split.

(* Case 20a *)
simpl.
auto.

(* Case 20b *)
auto.

(* Case 21 *)
simpl.
unfold popSIC.
apply replaceThreadInText.
split.

(* Case 21a *)
simpl.
auto.

(* Case 21b *)
auto.

(* Case 22 *)
simpl.
unfold pushIC.
apply replaceThreadInText.
split.

(* Case 22a *)
simpl.
auto.

(* Case 22b *)
auto.
Qed.

(*
 * Theorem: stayLinear
 *
 * Description:
 *  Prove that if the text segment is mapped linearly, then it stays that way.
 *)
Theorem stayLinear: forall (c1 c2 : config),
(c1 ==> c2) /\
(textMappedLinear c1) /\
(pcInText c1) /\
(validConfig c1) /\
(textNotWriteable c1) /\
(textMappedOnce c1) /\
(validCFG c1 (getCFG c1))
->
(textMappedLinear c2).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 H5].
destruct H5 as [H5 H6].
destruct H6 as [H6 H7].
destruct H1.
destruct c.

(* Case 1 - *)
auto.
auto.

(* Case 3: sta *)
unfold textMappedLinear.
simpl.
intros.
destruct H as [HA H].
destruct H as [HB H].
destruct H as [HC H].
unfold textMappedLinear in H2.
simpl in H2.
assert (cs <= getPhysical (getTLB (S v) MMU) <= ce \/
     vlookup v
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
auto.
destruct H1 as [H1 | H1].

(* Case 3a: Left-hand side *)
left.
auto.

(* Case 3b: Right-hand side *)
right.
assert (n <> v).
unfold textNotWriteable in H5.
assert (not (canWrite v MMU)).
apply H5.
auto.
contradict HC.
rewrite -> HC.
auto.
unfold vlookup.
unfold vLookup.
simpl.
rewrite <- sameRead.
unfold vlookup in H1.
unfold vLookup in H1.
auto.

(* Case 3: Prove remaining odds and ends *)
auto.

(* Case 4 - 6*)
auto.
auto.
auto.

(* Case 7: map *)
unfold textMappedLinear.
simpl.
intros.
destruct H as [HA H].
destruct H as [HB H].
destruct H as [HC H].
destruct H as [HD H].
destruct H as [HE H].
rewrite -> HC in HE.
unfold textNotWriteable in H5.
unfold textMappedOnce in H6.
unfold textMappedLinear in H2.
simpl in H2.

(* Assert that we're not modifying anything within the code segment *)
assert (v0 <> v).
contradict H0.
rewrite -> H0.
rewrite -> tlbSet.
contradict HD.
apply and_not_or.
split.
apply le_not_lt.
apply HD.
apply le_not_lt.
apply HD.
apply H.

(* Remove the changes made by the MMU *)
rewrite <- sameMMULookup in H0.

(* Assert the useful information from the linear mapping *)
assert (cs <= getPhysical (getTLB (S v0) MMU) <= ce \/
     vlookup v0
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
auto.

(* Prove the left half of the theorem *)
destruct H8 as [H8 | H8].
left.
rewrite <- sameMMULookup.
auto.

(* Aside: show that S v0 <> v *)
contradict HE.
rewrite <- HE.
apply and_not_or.
split.
apply le_not_lt.
apply H8.
apply le_not_lt.
apply H8.

(* Prove the right half of the theorem *)
right.
unfold vlookup.
unfold vLookup.
simpl.
unfold vlookup in H8.
unfold vLookup in H8.
simpl in H8.
rewrite <- sameMMULookup.
apply H8.
auto.
auto.

(* Case 8 - 21 *)
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
Qed.

Theorem TLInTextToT: forall (tl : ThreadList) (cfg : list nat) (mmu : MMU) (cs ce : nat) (id : nat) ,
threadListInText tl cfg mmu cs ce -> threadInText (getThread id tl) cfg mmu cs ce.
Proof.
intros tl cfg mmu cs ce.
induction tl.

(* Case 1: Base case: empty list *)
intros.
destruct id.
auto.
auto.

(* Case 2: Induction case: non-empty thread list *)
intros.
induction id.
unfold getThread.
simpl.
unfold threadListInText in H.
destruct H as [H1 H2].
fold threadListInText in H2.
auto.

(* Case 2a: Do the induction *)
unfold threadListInText in H.
destruct H as [H1 H2].
fold threadListInText in H2.
apply IHtl.
auto.
Qed.

(*
 * Theorem: stayPCInText
 *
 * Description:
 *  Prove that if the PC is in the text segment, then it stays there.
 *
 * Notes:
 *  This is invariant PCT in the Oakland 2014 paper text.
 *)
Theorem stayPCInText: forall (c1 c2 : config),
(c1 ==> c2) /\
(textMappedLinear c1) /\
(pcInText c1) /\
(validConfig c1) /\
(textNotWriteable c1) /\
(textMappedOnce c1) /\
(validCFG c1 (getCFG c1)) /\
(In (getTH c1) (getCFG c1)) /\
(threadListInText (getThreadList c1)
  (getCFG c1)(getCMMU c1) (getTextStart c1) (getTextEnd c1)) /\
(AreAllThreadICsInText (getThreadList c1) c1) /\
(In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1))
->
(pcInText c2).
Proof.
intros.

(* Split the preconditions into separate hypotheses *)
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 H5].
destruct H5 as [H5 H6].
destruct H6 as [H6 H7].
destruct H7 as [H7 TH].
destruct TH as [TH TLT].
destruct TLT as [TLT ICText].
destruct ICText as [ICText goodThreadID].

(* Continue on with the proof *)
destruct H1.
destruct c.

(* Case 1: ldi *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert (n2 <= getPhysical (getTLB (S n0) m) <= n3 \/
     vlookup n0 (C m s t n0 n1 l n2 n3 l0 n4 n5 n6 t0 n7 n8 l1 n9) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold getInsn in H0.
unfold vlookup in H0.
unfold vlookup.
simpl.
unfold vLookup in H0.
unfold vLookup.
simpl in H0.
rewrite -> H0.
discriminate.

(* Case 2: lda *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
destruct H0.
unfold vlookup.
simpl.
unfold vaLookup in H0.
unfold vLookup.
rewrite -> H0.
discriminate.

(* Case 3: sta *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
destruct H0.
unfold vlookup.
simpl.
unfold vaLookup in H0.
unfold vLookup.
rewrite -> H0.
discriminate.

(* Case 4: add *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS (val v) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
rewrite -> H0.
discriminate.

(* Case 5: sub *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS (val v) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
rewrite -> H0.
discriminate.

(* Case 6: jmp *)
unfold pcInText.
simpl.
unfold validCFG in H7.
apply cfg23 in H7.
simpl in H7.
unfold validCFG3 in H7.
apply H7.
apply H.

(* Case 7: map *)
unfold pcInText.
simpl.
simpl in TH.
simpl in TLT.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
rewrite <- sameMMULookup.
auto.
destruct H as [HA H].
destruct H as [HB H].
destruct H as [HC H].
destruct H as [HD H].
destruct H as [HE H].
destruct H as [HF H].
rewrite -> HC in HE.
contradict HE.
rewrite <- HE.
apply and_not_or.
split.
apply le_not_lt.
apply H0.
apply le_not_lt.
apply H0.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 H10].
rewrite -> H0.
discriminate.

(* Case 8: svaDeclareStack *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 H10].
rewrite -> H0.
discriminate.

(* Case 9: jeq *)
unfold pcInText.
simpl.
unfold validCFG in H7.
apply cfg23 in H7.
simpl in H7.
unfold validCFG3 in H7.
apply H7.
apply H.

(* Case 10: jeq *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 H10].
rewrite -> H0.
discriminate.

(* Case 11: jne *)
unfold pcInText.
simpl.
unfold validCFG in H7.
apply cfg23 in H7.
simpl in H7.
unfold validCFG3 in H7.
apply H7.
apply H.

(* Case 12: jne *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 H10].
rewrite -> H0.
discriminate.

(* Case 13: svaLoadPGTable *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
rewrite -> H0.
discriminate.

(* Case 14: svaInitStack *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
destruct H0 as [H0 HA].
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
rewrite -> H0.
discriminate.

(* Case 15: svaSwap *)
unfold pcInText.
simpl.
simpl in TLT.
simpl in TH.
assert (threadInText (getThread vr tl) CFG MMU cs ce).
apply TLInTextToT.
auto.
destruct getThread.
destruct b.

(* Case in which the thread is swappable *)
unfold threadInText in H0.
destruct H0 as [H0 H1].
unfold getThreadPC.
auto.

(* Case in which the thread is not swappable *)
unfold canThreadSwap in H.
destruct H.
destruct H1.
destruct H8 as [H8 H100].
contradict H8.
auto.

(* Case 16: trap *)
unfold pcInText.
simpl.
unfold validCFG in H7.
apply cfg23 in H7.
simpl in H7.
unfold validCFG3 in H7.
apply H7.
apply TH.

(* Case 17: iret *)
unfold pcInText.
simpl.
destruct H as [H8 H].
destruct H as [H9 H].
destruct H as [H len].
rewrite -> H.
unfold textMappedLinear in H2.
simpl in H2.
simpl in goodThreadID.
unfold AreAllThreadICsInText in ICText.
simpl in ICText.

assert (ICListInText (getThreadICList tid tl) cs ce MMU).
apply ICText.
auto.
unfold itop.
destruct (getThreadICList tid tl).
simpl in len.
contradict len.
apply le_not_lt.
auto.
simpl.
unfold ICListInText in H0.
destruct H0 as [H0 H00].
fold ICListInText in H00.
apply H0.

(* Case 18: svaRegisterTrap *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 H10].
rewrite -> H0.
discriminate.

(* Case 19: svaSaveIContext *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 NE].
rewrite -> H0.
discriminate.

(* Case 20: svaLoadIContext *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 sic].
rewrite -> H0.
discriminate.

(* Case 21: svaPushFunction *)
unfold pcInText.
simpl.
unfold textMappedLinear in H2.
simpl in H2.
assert ( cs <= getPhysical (getTLB (S PC) MMU) <= ce \/
     vlookup PC
       (C MMU DS (val f) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) = jmp).
apply H2.
apply H3.
destruct H0.
auto.
contradict H0.
destruct H.
unfold vlookup.
simpl.
unfold vLookup.
unfold vaLookup in H0.
destruct H0 as [H0 H10].
rewrite -> H0.
discriminate.
Qed.

