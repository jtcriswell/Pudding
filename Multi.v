(*
 * Module: Multi
 *
 * Description:
 *  Prove a simple CFI policy on the transitive closure of the small-step
 *  transition relation.
 *)

(* Load Coq Standard Library modules *)
Require Import Semantics.
Require Import SVAOS.
Require Import List.
Require Import Relations.
Require Import ICText.
Require Import ICProofs.
Require Import ThreadProofs.
Require Import ThreadTextProofs.

(*
 * Define the multi function which creates multi-step relations.
 *)
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                 R x y -> multi R y z -> multi R x z.

(*
Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].
*)

Definition multistep := multi step.
Notation " t '==>*' t' " := (multistep t t') (at level 40).

(*
 * Theorem: TransConditionsHold
 *
 * Description:
 *  This theorem shows that all of our very important conditions on the
 *  configuration holds over the transitive closure of the step relation.
 *)
Theorem TransConditionsHold: forall (c1 c2 : config),
  (pcInText c1) /\
  (validThreadIDs c1) /\
  (validCFG c1 (getCFG c1)) /\
  (In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
  (textMappedLinear c1) /\
  (AreAllThreadICsInText (getThreadList c1) (c1)) /\
  (AreAllThreadSICsInText (getThreadList c1) (c1)) /\
  (validThreadList (getThreadList c1) (getCFG c1) (getCMMU c1) (getStore c1)) /\
  (In (getTH c1) (getCFG c1)) /\
  (validConfig c1) /\
  (textNotWriteable c1) /\
  (textMappedOnce c1) /\
  (threadListInText (getThreadList c1) (getCFG c1) (getCMMU c1)
  (getTextStart c1) (getTextEnd c1)) /\
  (c1 ==>* c2)
->
  (pcInText c2) /\
  (validThreadIDs c2) /\
  (validCFG c2 (getCFG c2)) /\
  (In (getThread (getCurrThread c2) (getThreadList c2)) (getThreadList c2)) /\
  (textMappedLinear c2) /\
  (AreAllThreadICsInText (getThreadList c2) (c2)) /\
  (AreAllThreadSICsInText (getThreadList c2) (c2)) /\
  (validThreadList (getThreadList c2) (getCFG c2) (getCMMU c2) (getStore c2)) /\
  (In (getTH c2) (getCFG c2)) /\
  (validConfig c2) /\
  (textNotWriteable c2) /\
  (textMappedOnce c2) /\
  (threadListInText (getThreadList c2) (getCFG c2) (getCMMU c2)
  (getTextStart c2) (getTextEnd c2)).
Proof.
intros.
destruct H as [H1 H].
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
destruct H as [H5 H].
destruct H as [H6 H].
destruct H as [H7 H].
destruct H as [H8 H].
destruct H as [H9 H].
destruct H as [H10 H].
destruct H as [H11 H].
destruct H as [H12 H].
destruct H as [H13 H].
induction H.
repeat (split ; auto).
split.
apply IHmulti.
apply stayPCInText with (c1 := x).
repeat (split ; auto).
apply threadIDsAlwaysValid with (c1 := x).
repeat (split ; auto).
unfold validCFG.
apply cfg32.
apply alwaysValidCFG with (c1 := x).
unfold validCFG in H3.
apply cfg23 in H3.
auto.
apply threadAlwaysThere with (c1 := x).
repeat (split ; auto).
apply stayLinear with (c1 := x).
repeat (split ; auto).
apply stayICInText with (c1 := x).
repeat (split ; auto).
apply staySICInText with (c1 := x).
repeat (split ; auto).
apply threadsAlwaysValid with (c1 := x).
repeat (split ; auto).
apply alwaysGoodTH with (c1 := x).
repeat (split ; auto).
apply alwaysValid with (c1 := x).
auto.
apply neverWriteText with (c1 := x).
auto.
apply neverMapTextTwice with (c1 := x).
repeat (split ; auto).
apply TLAlwaysInText with (c1 :=x).
repeat (split ; auto).

apply IHmulti.
apply stayPCInText with (c1 := x).
repeat (split ; auto).
apply threadIDsAlwaysValid with (c1 := x).
repeat (split ; auto).
unfold validCFG.
apply cfg32.
apply alwaysValidCFG with (c1 := x).
unfold validCFG in H3.
apply cfg23 in H3.
auto.
apply threadAlwaysThere with (c1 := x).
repeat (split ; auto).
apply stayLinear with (c1 := x).
repeat (split ; auto).
apply stayICInText with (c1 := x).
repeat (split ; auto).
apply staySICInText with (c1 := x).
repeat (split ; auto).
apply threadsAlwaysValid with (c1 := x).
repeat (split ; auto).
apply alwaysGoodTH with (c1 := x).
repeat (split ; auto).
apply alwaysValid with (c1 := x).
auto.
apply neverWriteText with (c1 := x).
auto.
apply neverMapTextTwice with (c1 := x).
repeat (split ; auto).
apply TLAlwaysInText with (c1 :=x).
repeat (split ; auto).
Qed.

Theorem TranthreadsAlwaysValid: forall (c1 c2 : config),
(validCFG c1 (getCFG c1)) /\ (validConfig c1) /\ (textNotWriteable c1) /\
(validThreadList (getThreadList c1) (getCFG c1) (getCMMU c1) (getStore c1)) /\
(getTextStart c1) <= (getPhysical (getTLB (getPC c1) (getCMMU c1))) <= (getTextEnd c1) /\
(threadListInText (getThreadList c1)
  (getCFG c1)(getCMMU c1) (getTextStart c1) (getTextEnd c1)) /\
(textMappedOnce c1) /\
(pcInText c1) /\
(textMappedLinear c1) /\
(In (getTH c1) (getCFG c1)) /\
(AreAllThreadICsInText (getThreadList c1) c1) /\
(In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
(validThreadIDs c1) /\
(AreAllThreadSICsInText (getThreadList c1) (c1)) /\
(c1 ==>* c2)
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
destruct H3 as [pc H3].
destruct H3 as [tml H3].
destruct H3 as [inth H3].
destruct H3 as [goodic H3].
destruct H3 as [inThread H3].
destruct H3 as [validTIDs H3].
destruct H3 as [goodsic H3].
induction H3.
auto.
assert (validThreadList (getThreadList y) (getCFG y) (getCMMU y) (getStore y)).
apply threadsAlwaysValid with (c1 := x).
repeat (split ; auto).
apply IHmulti.
unfold validCFG.
apply cfg32.
apply alwaysValidCFG with (c1 := x).
unfold validCFG in vcfg.
apply cfg23 in vcfg.
auto.
apply alwaysValid with (c1 := x).
auto.
apply neverWriteText with (c1 := x).
auto.
apply threadsAlwaysValid with (c1 := x).
repeat (split ; auto).
apply stayPCInText with (c1 := x).
repeat (split ; auto).
apply TLAlwaysInText with (c1 :=x).
repeat (split ; auto).
apply neverMapTextTwice with (c1 := x).
repeat (split ; auto).
apply stayPCInText with (c1 := x).
repeat (split ; auto).
apply stayLinear with (c1 := x).
repeat (split ; auto).
apply alwaysGoodTH with (c1 := x).
repeat (split ; auto).
apply stayICInText with (c1 := x).
repeat (split ; auto).
unfold validThreadList in H4.
repeat (split ; auto).
apply threadAlwaysThere with (c1 := x).
repeat (split ; auto).
apply threadIDsAlwaysValid with (c1 := x).
repeat (split ; auto).
apply staySICInText with (c1 := x).
repeat (split ; auto).
Qed.

Theorem TransalwaysGoodTH: forall (c1 c2 : config),
(c1 ==>* c2) /\
(In (getTH c1) (getCFG c1)) ->
(In (getTH c2) (getCFG c2)).
Proof.
intros.
destruct H as [H1 H2].
induction H1.
auto.
apply IHmulti.
apply alwaysGoodTH with (c1 := x).
repeat (split ; auto).
Qed.

(*
 * Theorem: Transcfisafe
 *
 * Description:
 *  Prove that the cfisafe theorem is true over the transitive closure of the
 *  step relation.
 *)
Theorem Transcfisafe : forall (c1 c2 c3 c4: config),
  (pcInText c1) /\
  (validThreadIDs c1) /\
  (validCFG c1 (getCFG c1)) /\
  (In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
  (textMappedLinear c1) /\
  (AreAllThreadICsInText (getThreadList c1) (c1)) /\
  (AreAllThreadSICsInText (getThreadList c1) (c1)) /\
  (validThreadList (getThreadList c1) (getCFG c1) (getCMMU c1) (getStore c1)) /\
  (In (getTH c1) (getCFG c1)) /\
  (validConfig c1) /\
  (textNotWriteable c1) /\
  (textMappedOnce c1) /\
  (threadListInText (getThreadList c1) (getCFG c1) (getCMMU c1)
  (getTextStart c1) (getTextEnd c1)) /\
  (c1 ==>* c3) /\
  (c3 ==> c4) /\
  (c4 ==>* c2)
  ->
  (getPC c4) = (getPC c3 + 1) \/
  (In (getPC c4) (getCFG c3)) \/
  ((vlookup (minus (getPC c4) 1) c4) = svaSwap) \/
  ((getPC c4) = (getICPC (itop (getThreadICList (getCurrThread c3) (getThreadList c3))))).
Proof.
intros.
destruct H as [I1 I].
destruct I as [I2 I].
destruct I as [I3 I].
destruct I as [I4 I].
destruct I as [I5 I].
destruct I as [I6 I].
destruct I as [I7 I].
destruct I as [I8 I].
destruct I as [I9 I].
destruct I as [I10 I].
destruct I as [I13 I].
destruct I as [I14 I].
destruct I as [I15 I].
destruct I as [I16 I].
destruct I as [I17 I].
apply cfisafe.
split.
auto.
split.
apply TranthreadsAlwaysValid with (c1 := c1).
repeat (split ; auto).
apply TransalwaysGoodTH with (c1 := c1).
repeat (split ; auto).
Qed.

Theorem TranspcInIC: forall (c1 c2 : config),
(c1 ==>* c2) /\
(goodPCInConfigIC c1) /\
(validConfig c1) /\
(textNotWriteable c1) /\
(ThreadICsInText (getThreadList c1) c1) /\
((getTextStart c1) <= (getPhysical (getTLB (getPC c1) (getCMMU c1))) <= (getTextEnd c1)) /\
(validCFG c1 (getCFG c1)) /\
(goodPCInConfigSIC c1) /\
(noWriteTLPC (getThreadList c1) (getCMMU c1)) /\
(AreAllThreadICsInText (getThreadList c1) c1) /\
(validThreadIDs c1) /\
(In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
(textMappedLinear c1) /\
(AreAllThreadSICsInText (getThreadList c1) c1) /\
(textMappedOnce c1) /\
(In (getTH c1) (getCFG c1)) /\
(threadListInText (getThreadList c1) (getCFG c1) (getCMMU c1)
  (getTextStart c1) (getTextEnd c1)) 
->
(goodPCInConfigIC c2).
Proof.
intros.
destruct H as [H1 H].
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
destruct H as [H5 H].
destruct H as [H6 H].
destruct H as [H7 H].
destruct H as [H8 H].
destruct H as [H9 H].
destruct H as [HA H].
destruct H as [HB H].
destruct H as [HC H].
destruct H as [HD H].
destruct H as [HE H].
destruct H as [HF H].
destruct H as [HG H].
induction H1.

(* Case 1: No step *)
auto.

(* Case 2: Induction step *)
apply IHmulti.
apply pcInIC with (c1 := x).
repeat (split ; auto).
apply alwaysValid with (c1 := x).
repeat (split ; auto).
apply neverWriteText with (c1 := x).
repeat (split ; auto).
apply areAllIffAll.
apply stayICInText with (c1 := x).
repeat (split ; auto).
apply stayPCInText with (c1 := x).
repeat (split ; auto).
unfold validCFG.
apply cfg32.
apply alwaysValidCFG with (c1 := x).
unfold validCFG in H7.
apply cfg23 in H7.
auto.
admit.
apply getNWTLPC.
repeat (split ; auto).
apply neverWriteText with (c1 := x).
repeat (split ; auto).
apply stayICInText with (c1 := x).
repeat (split ; auto).
apply stayICInText with (c1 := x).
repeat (split ; auto).
apply threadIDsAlwaysValid with (c1 := x).
repeat (split ; auto).
apply threadAlwaysThere with (c1 := x).
repeat (split ; auto).
apply stayLinear with (c1 := x).
repeat (split ; auto).
apply staySICInText with (c1 := x).
repeat (split ; auto).
apply neverMapTextTwice with (c1 := x).
repeat (split ; auto).
apply alwaysGoodTH with (c1 := x).
repeat (split ; auto).
apply TLAlwaysInText with (c1 :=x).
repeat (split ; auto).
Qed.

(*
 * Theorem: Transcfisafe2
 *
 * Description:
 *  Prove that the cfisafe2 theorem is true over the transitive closure of the
 *  step relation.
 *)
Theorem Transcfisafe2 : forall (c1 c2 c3 c4: config),
  (pcInText c1) /\
  (validThreadIDs c1) /\
  (validCFG c1 (getCFG c1)) /\
  (In (getThread (getCurrThread c1) (getThreadList c1)) (getThreadList c1)) /\
  (textMappedLinear c1) /\
  (AreAllThreadICsInText (getThreadList c1) (c1)) /\
  (AreAllThreadSICsInText (getThreadList c1) (c1)) /\
  (validThreadList (getThreadList c1) (getCFG c1) (getCMMU c1) (getStore c1)) /\
  (In (getTH c1) (getCFG c1)) /\
  (validConfig c1) /\
  (textNotWriteable c1) /\
  (textMappedOnce c1) /\
  (threadListInText (getThreadList c1) (getCFG c1) (getCMMU c1)
  (getTextStart c1) (getTextEnd c1)) /\
  (goodPCInConfigIC c1) /\
  (goodPCInConfigSIC c1) /\
  (c1 ==>* c3) /\
  (c3 ==> c4) /\
  (c4 ==>* c2)
  ->
  (getPC c4) = (getPC c3 + 1) \/
  (In (getPC c4) (getCFG c3)) \/
  ((vlookup (minus (getPC c4) 1) c4) = svaSwap) \/
  ((vlookup (minus (getPC c4) 1) c4) = trap) \/
  ((getPC c4) = 0).
Proof.
intros.
destruct H as [I1 I].
destruct I as [I2 I].
destruct I as [I3 I].
destruct I as [I4 I].
destruct I as [I5 I].
destruct I as [I6 I].
destruct I as [I7 I].
destruct I as [I8 I].
destruct I as [I9 I].
destruct I as [I10 I].
destruct I as [I13 I].
destruct I as [I14 I].
destruct I as [I15 I].
destruct I as [I16 I].
destruct I as [I17 I].
destruct I as [I18 I].
destruct I as [I19 I].
apply cfisafe2.
split.
auto.
split.
apply TransConditionsHold with (c1 := c1).
repeat (split ; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split ; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split ; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TransConditionsHold with (c1 := c1).
repeat (split; auto).
split.
apply TranspcInIC with (c1 := c1).
repeat (split; auto).
apply areAllIffAll.
auto.
apply getNWTLPC.
auto.
admit.
Qed.

(*
 * Theorem: TranNXText
 *
 * Description:
 *   Prove that NXText holds over the transitive closure.
 *)
Theorem TranNXText : forall (c1 c2 : config) (v : nat),
(getTextStart c1) <= (getPhysical (getTLB v (getCMMU c1))) <= (getTextEnd c1) /\
(validConfig c1) /\
(textNotWriteable c1) /\
(textMappedOnce c1) /\
c1 ==>* c2
-> (vLookup v (getCMMU c1) (getStore c1)) =
   (vLookup v (getCMMU c2) (getStore c2)).
Proof.
intros.
destruct H as [H1 H].
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
induction H.

(* Case 1 *)
auto.

(* Case 2 *)
assert ((vLookup v (getCMMU x) (getStore x)) = (vLookup v (getCMMU y) (getStore y))).
apply NXText.
auto.
rewrite <- IHmulti.
apply H5.

(* Show that the intermediate configuration y is in the text section *)
apply alwaysInText with x.
auto.

(* Show that the intermediate configuration y is valid *)
apply alwaysValid with x.
auto.

(* Show that the intermediate configuration y has a non-writeable text section *)
apply neverWriteText with x.
auto.

(* Show that the intermediate configuration y has its text section only mapped once *)
apply neverMapTextTwice with x.
auto.
Qed.

