(*
 * Module: SVAOS
 *
 * Description:
 *  Prove that a simple CFI policy is maintained for the semantics of our
 *  language.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.

(* Load SVAOS specific modules *)
Require Import Semantics.
Require Import ICProofs.

(*
 * Theorem: threadIsValid
 *
 * Description:
 *   This theorem proves that if a thread list is valid, then any thread
 *   fetched from the list is valid.
 *)
Theorem threadIsValid: forall (cfg : list nat) (mmu : MMU) (ds : store) (tl : ThreadList) (n : nat),
validThreadList tl cfg mmu ds -> validThread (getThread n tl) cfg mmu ds.
Proof.
intros cfg mmu ds tl.
induction tl.

(* Case 1 *)
intros.
unfold getThread.
destruct n.

(* Case 1a *)
auto.

(* Case 1b *)
auto.

(* Case 2 *)
auto.

(* Case 3 *)
intros.
inversion H.
destruct n.

(* Case 3a *)
unfold getThread.
simpl.
auto.

(* Case 3b *)
fold validThreadList in H1.
assert (validThreadList (a :: tl) cfg mmu ds).
unfold validThreadList.
split.
auto.
fold validThreadList.
auto.
apply IHtl.
auto.
Qed.

(*
 * Theorem: cfisafe
 *
 * Description:
 *  Prove that the program counter always moves to the next instruction
 *  or is changed to a value that is within the list of acceptable
 *  targets.
 *)
Theorem cfisafe : forall c1 c2 : config,
  c1 ==> c2 /\
  (validThreadList (getThreadList c1) (getCFG c1) (getCMMU c1) (getStore c1)) /\
  (In (getTH c1) (getCFG c1))
  ->
  (getPC c2) = (getPC c1 + 1) \/
  (In (getPC c2) (getCFG c1)) \/
  ((vlookup (minus (getPC c2) 1) c2) = svaSwap) \/
  ((getPC c2) = (getICPC (itop (getThreadICList (getCurrThread c1) (getThreadList c1))))).
Proof.
intros c1 c2.
intro H.
destruct H.
destruct H.
destruct c.

(* First induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Second induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Third induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Fourth induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Subtraction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Fifth induction case *)
right.
left.
simpl.
destruct H as [H1 H2].
apply H2.

(* Sixth induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Seventh induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Eighth induction case *)
right.
left.
simpl.
destruct H as [H1 H2].
apply H2.

(* Addition to case 8: jeq fallthrough *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Ninth induction case *)
right.
left.
simpl.
destruct H as [H1 H2].
apply H2.

(* Addition to case 9: jne fallthrough *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Tenth induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
auto.

(* Case 11 *)
left.
simpl.
rewrite -> plus_comm.
simpl.
auto.

(* Case 12 *)
simpl.
simpl in H0.
right.
unfold vlookup.
unfold vLookup.
simpl.
destruct H0 as [H0 TH].
assert (validThread (getThread vr tl) CFG MMU DS).
apply threadIsValid.
auto.

destruct H.
destruct H2.
destruct getThread.
unfold validThread in H1.
unfold canThreadSwap in H3.
destruct H3 as [H3 H4].
rewrite -> H3 in H1.
simpl.
unfold vLookup in H1.
destruct H1.
left.
auto.
right.
auto.

(* Case 13 *)
simpl.
right.
left.
simpl in H0.
apply H0.

(* Case 14 *)
simpl.
right.
right.
simpl in H0.
right.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
destruct H3 as [H3 H4].
auto.

(* Case 15 *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Case 16 *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Case 17 *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Case 18 *)
simpl.
left.
rewrite -> plus_comm.
auto.
Qed.

(*
 * Theorem: cfisafe2
 *
 * Description:
 *  Prove that the program counter always moves to the next instruction
 *  or is changed to a value that is within the list of acceptable
 *  targets.
 *)
Theorem cfisafe2 : forall c1 c2 : config,
  c1 ==> c2 /\
  (validThreadList (getThreadList c1) (getCFG c1) (getCMMU c1) (getStore c1)) /\
  (In (getTH c1) (getCFG c1)) /\
  (pcInText c1) /\
  (validThreadIDs c1) /\
  (validCFG c1 (getCFG c1)) /\
  (In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
  (textMappedLinear c1) /\
  (AreAllThreadICsInText (getThreadList c1) (c1)) /\
  (AreAllThreadSICsInText (getThreadList c1) (c1)) /\
  (validConfig c1) /\
  (textNotWriteable c1) /\
  (textMappedOnce c1) /\
  (threadListInText (getThreadList c1) (getCFG c1) (getCMMU c1) 
  (getTextStart c1) (getTextEnd c1)) /\
  (goodPCInConfigIC c1) /\
  (goodPCInConfigSIC c1)
  ->
  (getPC c2) = (getPC c1 + 1) \/
  (In (getPC c2) (getCFG c1)) \/
  ((vlookup (minus (getPC c2) 1) c2) = svaSwap) \/
  ((vlookup (minus (getPC c2) 1) c2) = trap) \/
  ((getPC c2) = 0).
Proof.
intros c1 c2.
intro H.
destruct H as [H I].
destruct I as [I1 I].
destruct I as [I2 I].
destruct I as [I3 I].
destruct I as [I4 I].
destruct I as [I5 I].
destruct I as [I6 I].
destruct I as [I7 I].
destruct I as [I8 I].
destruct I as [I9 I].
destruct I as [I10 I].
destruct I as [I11 I].
destruct I as [I12 I].
destruct I as [I13 I].
destruct I as [I14 I].

assert (goodPCInConfigIC c2).
apply pcInIC with (c1 := c1).
repeat (split ; auto).
apply areAllIffAll.
auto.
auto.
apply getNWTLPC.
repeat (split ; auto).

destruct H.
destruct c.

(* First induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Second induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Third induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Fourth induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Subtraction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Fifth induction case *)
right.
left.
simpl.
destruct H as [HA HB].
apply HB.

(* Sixth induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Seventh induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
reflexivity.

(* Eighth induction case *)
right.
left.
simpl.
apply H.

(* Addition to case 8: jeq fallthrough *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Ninth induction case *)
right.
left.
simpl.
apply H.

(* Addition to case 9: jne fallthrough *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Tenth induction case *)
left.
simpl.
rewrite -> plus_comm.
simpl.
auto.

(* Case 11 *)
left.
simpl.
rewrite -> plus_comm.
simpl.
auto.

(* Case 12: svaSwap *)
simpl.
simpl in H0.
right.
unfold vlookup.
unfold vLookup.
simpl.
assert (validThread (getThread vr tl) CFG MMU DS).
apply threadIsValid.
auto.

destruct H.
destruct H2.
destruct getThread.
unfold validThread in H1.
unfold canThreadSwap in H3.
destruct H3 as [H3 H4].
rewrite -> H3 in H1.
simpl.
unfold vLookup in H1.
destruct H1.
left.
auto.
right.
auto.

(* Case 13 *)
simpl.
right.
left.
apply I2.

(* Case 14 *)
simpl.
right.
assert (goodPCICL (getThreadICList tid tl) CFG MMU DS).
apply GoodPCICL.
auto.
destruct H as [H20 H].
destruct H as [H21 H].
destruct H as [H22 H].
rewrite -> H22.
simpl.
unfold vlookup.
simpl.
apply goodPCInItop in H1.
unfold goodPCIC in H1.
destruct H1.
left.
auto.
destruct H1.
right.
right.
left.
auto.
right.
right.
right.
auto.

(* Case 15 *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Case 16 *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Case 17 *)
simpl.
left.
rewrite -> plus_comm.
auto.

(* Case 18 *)
simpl.
left.
rewrite -> plus_comm.
auto.
Qed.


(*
 * Theorem: NXText
 *
 * Description:
 *   Prove that fetching an instruction through a virtual address never changes 
 *   even though stores can modify physical memory and the MMU can remap pages.
 *)
Theorem NXText : forall (c1 c2     : config)
                        (v         : nat),
(getTextStart c1) <= (getPhysical (getTLB v (getCMMU c1))) <= (getTextEnd c1) /\
(validConfig c1) /\
(textNotWriteable c1) /\
(textMappedOnce c1) /\
c1 ==> c2
-> (vLookup v (getCMMU c1) (getStore c1)) =
   (vLookup v (getCMMU c2) (getStore c2)).
Proof.
intros.
destruct H as [h1 H].
destruct H as [h2 H].
destruct H as [h3 H].
destruct H as [h4 H].

(* Prove that several properties hold on the final configuration *)
(*
assert (validConfig c2).
apply alwaysValid with c1.
auto.
assert (textNotWriteable c2).
apply neverWriteText with c1.
auto.
assert (textMappedOnce c2).
apply neverMapTextTwice with c1.
auto.
*)

(* Prove by induction on the proof tree *)
destruct H.
destruct c.


(* Induction case 1 *)
auto.

(* Induction case 2 *)
auto.

(* Induction case 3 *)
simpl.
unfold vLookup.
simpl in h1.
simpl in h2.
simpl in h3.
destruct H.
destruct H0.

(*
 * Need to show that the two physical addresses must be different.  This is
 * because the address written cannot be in the text segment while the address
 * checked is within the text segment.  The address written cannot be within
 * the text segment because the text segment is not writeable.
 *)
assert (getPhysical (getTLB v MMU) <> getPhysical (getTLB n MMU)).

(* Detour: show that v is not writeable *)
simpl in h4.
assert (~ canWrite v MMU).
apply h3.
auto.


(* Back from detour: show that the two physical addresses must be different *)
assert (v <> n).
contradict H2.
rewrite -> H2.
apply H1.
apply h4.
auto.

(* Resume the proof of induction case 3 *)
rewrite <- sameRead.
auto.
apply H2.

(* Induction case 4 *)
auto.

(* Induction case 5 *)
auto.

(* Subtraction case *)
auto.

(* Induction case 6 *)
simpl.
destruct H as [h5 H].
destruct H as [h6 H].
destruct H as [h7 H].
destruct H as [h8 H].
destruct H as [h9 H].
rewrite -> h7 in h9.

simpl in h1.
simpl in h2.
simpl in h3.
simpl in h4.

assert (v <> v0).
destruct h9 as [ha | hb].

(* Case: getPhysical (getTLB v0 MMU) < cs *)
contradict ha.
apply le_not_lt.
rewrite <- ha.
apply h1.

(* Case: ce < getPhysical (getTLB v0 MMU) *)
contradict hb.
apply le_not_lt.
rewrite <- hb.
apply h1.

apply sameMMURead.
apply H0.

(* Induction case 7 *)
auto.

(* Induction case 8 *)
auto.
auto.

(* Induction case 9 *)
auto.
auto.

(* Induction case 10 *)
auto.

(* Induction case 11 *)
auto.

(* Induction case 12 *)
auto.

(* Induction case 13 *)
auto.

(* Induction case 14 *)
auto.

(* Induction case 15 *)
auto.

(* Induction case 16 *)
auto.

(* Induction case 17 *)
auto.

(* Induction case 18 *)
auto.
Qed.
