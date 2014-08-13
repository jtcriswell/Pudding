(*
 * Module: Semantics
 *
 * Description:
 *  Define the small-step semantics for a simple assembly language.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.

(* Load SVAOS specific modules *)
Require Export Config.

(*
 * Define the small-step semantics for this little language.
 * The first two "arguments" are the initial and final state
 * and the final result is a proposition indicating whether
 * the transition can take place.
 *)
Reserved Notation " t '==>' t' " (at level 40).

Inductive step : config -> config -> Prop :=
  | ST_LoadImm    : forall c n,
      (canExecConfig c) /\ ((getInsn c) = ldi n) ->
      c ==> (setReg (incPC c) n)
  | ST_Load       : forall MMU DS Reg PC SP CFG n cs ce st asid tid ntid tl
                    gvs gve gl th t,
      (canExec PC MMU) /\ (vaLookup PC asid MMU DS) = lda n /\
      (canRead n MMU)  /\ (vaLookup n asid MMU DS = t) /\
      ((n < gvs) \/ (n > gve)) ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS t (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Store      : forall MMU DS Reg PC SP CFG n cs ce st asid tid ntid tl
                    gvs gve gl th,
      (canExec PC MMU) /\ (vaLookup PC asid MMU DS) = sta n /\
      (canWrite n MMU) /\
      ((n < gvs) \/ (n > gve)) ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU (replace (getPhysical (getTLB n MMU)) Reg DS) Reg (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Add        : forall MMU DS PC SP CFG n cs ce st asid tid ntid tl
                    gvs gve gl th v,
      (canExec PC MMU) /\ (vaLookup PC asid MMU DS) = add n ->
      (C MMU DS (val v) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS (val (v + n)) (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Sub        : forall MMU DS PC SP CFG n cs ce st asid tid ntid tl
                    gvs gve gl th v,
      (canExec PC MMU) /\ (vaLookup PC asid MMU DS) = sub n ->
      (C MMU DS (val v) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS (val (v - n)) (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Jmp        : forall MMU DS PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th v,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = jmp) /\ (In v CFG) ->
      (C MMU DS (val v) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS (val v) v SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Map        : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl tlb
                    v p gvs gve gl th,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = map v tlb) /\
      (p = getPhysical (getTLB v MMU)) /\
      (((getPhysical tlb) < cs) \/ (ce < (getPhysical tlb))) /\
      ((p < cs) \/ (ce < p)) /\
      ((v < gvs) \/ (gve < v)) /\
      (not (In (getPhysical tlb) gl)) /\
      (definedTLB (getTLB v MMU))
      ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C (updateTLB v tlb MMU) DS Reg (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_DeclareStack : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl
                      s e ps pe gvs gve gl th,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = svaDeclareStack s e) /\
      (ps = getPhysical (getTLB s MMU)) /\
      (pe = getPhysical (getTLB e MMU)) /\
      ((ps < cs) \/ (ce < ps)) /\
      ((pe < cs) \/ (ce < pe)) /\
      (0 < s < e)
      ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS Reg (S PC) SP CFG cs ce ((s,e) ::st) asid tid ntid tl gvs gve gl th)
  | ST_Jeq1       : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl n
                    gvs gve gl th,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = jeq n) /\ (In n CFG) /\
      (Reg = (val 0)) ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS Reg n SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Jeq2       : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl n
                    gvs gve gl th,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = jeq n) /\
      (Reg <> (val 0)) ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS Reg (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Jne1       : forall MMU DS PC SP CFG cs ce st asid tid ntid tl n
                    gvs gve gl th vr,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = jne n) /\ (In n CFG) /\
      (vr < 0) ->
      (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS (val vr) n SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_Jne2       : forall MMU DS PC SP CFG cs ce st asid tid ntid tl n
                    gvs gve gl th vr,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = jne n) /\
      (not (vr < 0)) ->
      (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th)
      ==>
      (C MMU DS (val vr) (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th)
  | ST_LoadPGTable: forall MMU DS PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th vr,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = svaLoadPGTable) ->
      (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS (val vr) (S PC) SP CFG cs ce st vr tid ntid tl gvs gve gl th)
  | ST_InitStack  : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl f
                    gvs gve gl th,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = svaInitStack f) /\
      (In f CFG) /\
      (S ntid < length tl) /\
      (0 < length (getThreadICList tid tl)) ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS (val ntid) (S PC) SP CFG cs ce st asid tid (S ntid)
        (updateThread ntid (Thread true f ((itop (getThreadICList tid tl)) :: nil) nil) tl) gvs gve gl th)
  | ST_Swap       : forall MMU DS PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th vr,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = svaSwap) /\
      ((canThreadSwap (getThread vr tl)) = true) /\
      (vr < length tl)
      ->
      (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS (val tid) (getThreadPC (getThread vr tl)) SP CFG cs ce st asid vr ntid
        (updateThread tid (threadOnCPU (S PC) (getThread tid tl))
          (updateThread vr (threadOffCPU (getThread vr tl)) tl)) gvs gve gl th)
  | ST_Trap       : forall MMU DS PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th r,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = trap) ->
      (C MMU DS (val r) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS (val r) th SP CFG cs ce st asid tid ntid
        (updateThread tid
          (Thread false 0 (push (IC r (S PC) SP 0) (getThreadICList tid tl)) (getThreadSICList tid tl)) tl)
        gvs gve gl th)
  | ST_IRet       : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th popPC,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = iret) /\
      (popPC = (getICPC (itop (getThreadICList tid tl)))) /\
      (0 < length (getThreadICList tid tl))
      ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS Reg popPC SP CFG cs ce st asid tid ntid
        (updateThread tid
          (Thread false 0 (pop (getThreadICList tid tl)) (getThreadSICList tid tl)) tl)
        gvs gve gl th)
  | ST_SVARegTrap : forall MMU DS PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th vr,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = svaRegisterTrap) /\
      (In vr CFG) ->
      (C MMU DS (val vr) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS (val vr) (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl vr)
  | ST_svaSaveIC  : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = svaSaveIcontext) /\
      (0 < length (getThreadICList tid tl)) ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS Reg (S PC) SP CFG cs ce st asid tid ntid (pushSIC tid tl) gvs gve gl th)
  | ST_svaLoadIC  : forall MMU DS Reg PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th,
      (canExec PC MMU) /\
      ((vaLookup PC asid MMU DS) = svaLoadIcontext) /\
      (0 < length (getThreadSICList tid tl)) ->
      (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS Reg (S PC) SP CFG cs ce st asid tid ntid (popSIC tid tl) gvs gve gl th)
  | ST_svaIPushF  : forall MMU DS PC SP CFG cs ce st asid tid ntid tl
                    gvs gve gl th f a,
      (canExec PC MMU) /\ ((vaLookup PC asid MMU DS) = svaPushFunction a) /\
      (In f CFG) ->
      (C MMU DS (val f) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) ==>
      (C MMU DS (val f) (S PC) SP CFG cs ce st asid tid ntid (pushIC a f SP tid tl) gvs gve gl th)
  where " t '==>' t' " := (step t t').

(*
 * Theorem: alwaysValid
 *
 * Description:
 *   Prove that if the configuration is valid before a step is taken, it is
 *   still valid after a step is taken.
 *
 * Notes:
 *  This is invariant VC in the Oakland 2014 paper.
 *)
Theorem alwaysValid : forall (c1 c2 : config),
(validConfig c1) /\ (c1 ==> c2) -> validConfig c2.
Proof.
intros.
destruct H as [H0 H1].
destruct H1.
destruct H.
destruct c.

(* Case 1 *)
auto.

(* Case 2 *)
auto.

(* Case 3 *)
auto.

(* Case 4 *)
auto.

(* Case 5 *)
auto.

(* Case 6 *)
auto.

(* Subtraction case *)
auto.

(* Case 7 *)
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
unfold validConfig.
split.
apply H0.
split.
apply H0.
unfold stacksWellFormed.
simpl.
split.
auto.
simpl.
apply H0.

(* Case 8: jeq with reg == 0 *)
auto.

(* Case 9: jeq with reg <> 0 *)
auto.

(* Case 10: jne *)
auto.
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

(* Case 19 *)
auto.
Qed.

(*
 * Theorem: neverUnmapText
 *
 * Description:
 *   This theorem proves that we never unmap the text segment.
 *)
Theorem neverUnmapText : forall (v : nat) (c1 c2 : config),
  (c1 ==> c2) /\
  (getTextStart c1) <= (getPhysical (getTLB v (getCMMU c1))) <= (getTextEnd c1)
  ->
  getPhysical (getTLB v (getCMMU c1)) = getPhysical (getTLB v (getCMMU c2)).
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H1.
  destruct c.

  (* Case 1 *)
  auto.

  (* Case 2 *)
  auto.

  (* Case 3 *)
  auto.

  (* Case 4 *)
  auto.

  (* Case 5 *)
  auto.

  (* Subtraction Case *)
  auto.

  (* Case 6 *)
  destruct H as [H1 H].
  destruct H as [H3 H].
  destruct H as [H4 H].
  destruct H as [H5 H].
  destruct H as [H H6].
  simpl in H2.
  simpl.
  rewrite -> H4 in H.
  destruct H.
  destruct H5.

  assert (getTLB v0 MMU <> getTLB v MMU).
  contradict H.
  apply le_not_lt.
  rewrite -> H.
  apply H2.
  assert (v <> v0).
  contradict H5.
  rewrite -> H5.
  reflexivity.
  assert ((getTLB v MMU) = (getTLB v (updateTLB v0 tlb MMU))).
  apply sameMMULookup.
  apply H7.
  rewrite -> H8.
  auto.

  assert (getTLB v0 MMU <> getTLB v MMU).
  contradict H.
  apply le_not_lt.
  rewrite -> H.
  apply H2.
  assert (v <> v0).
  contradict H5.
  rewrite -> H5.
  reflexivity.
  assert ((getTLB v MMU) = (getTLB v (updateTLB v0 tlb MMU))).
  apply sameMMULookup.
  apply H7.
  rewrite -> H8.
  auto.

  assert (getTLB v0 MMU <> getTLB v MMU).
  contradict H.
  apply le_not_lt.
  rewrite -> H.
  apply H2.
  assert (v <> v0).
  destruct H5.

  contradict H0.
  rewrite -> H0.
  reflexivity.
  contradict H0.
  rewrite -> H0.
  reflexivity.
  assert ((getTLB v MMU) = (getTLB v (updateTLB v0 tlb MMU))).
  apply sameMMULookup.
  apply H7.
  rewrite -> H8.
  auto.

  (* Case 7 *)
  auto.

  (* Case 8: jeq with reg == 0 *)
  auto.

  (* Case 8b: jeq with reg <> 0 *)
  auto.

  (* Case 9: Both jne cases *)
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
 * Theorem: neverWriteText
 *
 * Description:
 *   Prove that if the text segment was not writeable before, it still isn't
 *   writeable after a step is taken.
 *
 * Notes:
 *  This is the invariant TNW in the Oakland 2014 paper.
 *)
Theorem neverWriteText : forall (c1 c2 : config),
(textNotWriteable c1) /\ (c1 ==> c2) -> textNotWriteable c2.
Proof.
intros.
destruct H as [H0 H1].
destruct H1.
destruct c.

(* Case 1 *)
auto.

(* Case 2 *)
auto.

(* Case 3 *)
auto.

(* Case 4 *)
auto.

(* Case 5 *)
auto.

(* Subtraction Case *)
auto.

(* Case 6 *)
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
(* JTC: destruct here again *)
rewrite -> H2 in H4.
simpl.
intros.
unfold textNotWriteable in H0.

(* v0 <> v.  This is because if v0 = v,
 * then getPhysical (getTLB v0 (updateTLB v tlb MMU)) = tlb, and tlb is outside
 * the code segment while getTLB v0 is within the code segment.
 *)
assert (getPhysical (getTLB v0 (updateTLB v tlb MMU)) <> getPhysical tlb).
contradict H3.
apply and_not_or.
split.
apply le_not_lt.
rewrite <- H3.
apply H6.
apply le_not_lt.
rewrite <- H3.
apply H6.
assert (getPhysical (getTLB v0 (updateTLB v tlb MMU)) <> getPhysical tlb -> v0 <> v).
intro.
contradict H7.
rewrite -> H7.
rewrite -> tlbSet.
auto.
apply H5.
assert (v0 <> v).
apply H8.
apply H7.
rewrite <- sameMMULookup in H6.
assert (not (canWrite v0 MMU)).
apply H0.
apply H6.
rewrite <- sameMMUPerms.
apply H10.
apply H9.
apply H9.

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
 * Theorem: neverMapTextTwice
 *
 * Description:
 *   This theorem proves that no matter what a program does, if the text
 *   segment was mapped once at the beginning of execution, it remains
 *   mapped once.
 *
 * Notes:
 *  This is the invariant TMAP1 in the Oakland 2014 paper.
 *)
Theorem neverMapTextTwice: forall (c1 c2 : config),
(textMappedOnce c1) /\ (c1 ==> c2) -> textMappedOnce c2.
Proof.
intros.
destruct H as [H1 H2].
destruct H2.
destruct c.

(* Case 1 *)
auto.

(* Case 2 *)
auto.

(* Case 3 *)
auto.

(* Case 4 *)
auto.

(* Case 5 *)
auto.

(* Subtraction Case *)
auto.

(* Case 6 *)
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
destruct H as [H5 H].
destruct H as [H6 H].
rewrite -> H4 in H6.

simpl.
intros.
destruct H0 as [H7 H0].
simpl in H1.

(* Prove that we never update anything pointing to the text segment;
 * we do this here so that we don't have to reprove it later when we need it
 *)
assert (getTLB v1 MMU = (getTLB v1 (updateTLB v tlb MMU))).
apply sameMMULookup.
destruct H5.
destruct H6.
destruct H7.
contradict H7.
apply lt_not_le.
rewrite -> H7.
assert (getTLB v (updateTLB v tlb MMU) = tlb).
apply tlbSet.
apply H.
rewrite -> H9.
apply H5.

(* ce < getPhysical(v) *)
destruct H7.
contradict H7.
apply lt_not_le.
rewrite -> H7.
assert (getTLB v (updateTLB v tlb MMU) = tlb).
apply tlbSet.
apply H.
rewrite -> H9.
apply H5.

(* Third v1 <> v case *)
destruct H7.
contradict H8.
apply lt_not_le.
rewrite -> H8.
assert (getTLB v (updateTLB v tlb MMU) = tlb).
apply tlbSet.
apply H.
rewrite -> H9.
apply H5.

(* Prove that getTLB v1 MMU <> get TLB v2 MMU*)
assert (getPhysical (getTLB v1 MMU) <> getPhysical (getTLB v2 MMU)).
apply H1.
split.
rewrite <- H8 in H7.
auto.
auto.

(*
 * Resume proving the theorem: We must now handle the case in which
 * we are examining an address we updated (v2 = v) or the case in
 * which we are examining some other address (v2 <> v)
 *)
assert ((v2 = v) \/ (v2 <> v)).
apply classic.

(* Detour: Prove that getTLB v (updateTLB v tlb MMU) = tlb) *)
assert (getTLB v (updateTLB v tlb MMU) = tlb).
apply tlbSet.
apply H.

(* Prove each case *)
destruct H10.

(* Case: v2 = v *)
rewrite -> H10.
rewrite -> H11.
destruct H7.
destruct H5.
apply not_eq_sym.
contradict H5.
apply le_not_lt.
rewrite -> H5.
auto.

contradict H5.
apply le_not_lt.
rewrite <- H5.
auto.

(* Case v2 <> v *)
assert (getTLB v2 (updateTLB v tlb MMU) = getTLB v2 MMU).
rewrite <- sameMMULookup.
auto.
apply H10.
rewrite <- H8.
rewrite -> H12.
apply H9.

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
 * Theorem: alwaysValidCFG
 *
 * Description:
 *  Prove that the CFG will always stay within the text segment if it starts
 *  in the text segment.
 *)
Theorem alwaysValidCFG : forall (c1 c2 : config),
(validCFG3 (getCFG c1) (getCMMU c1) (getTextStart c1) (getTextEnd c1)) /\
(c1 ==> c2) ->
(validCFG3 (getCFG c2) (getCMMU c2) (getTextStart c2) (getTextEnd c2)).
Proof.
intros.
destruct H as [H1 H2].
destruct H2.
destruct c.

(* Case 1: ldi *)
auto.

(* Case 2: lda *)
auto.

(* Case 3: sta *)
auto.

(* Case 4: add *)
auto.

(* Case 5: sub *)
auto.

(* Case 6: jmp *)
auto.

(* Case 7: map *)
simpl.
simpl in H1.
unfold validCFG3 in H1.
unfold validCFG3.
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
destruct H as [H5 H].
destruct H as [H6 H].
destruct H as [H7 H].
destruct H as [H8 H].
intros.
split.

assert (cs <= getPhysical (getTLB f MMU) <= ce).
apply H1.
auto.
rewrite -> H4 in H6.

rewrite <- sameMMULookup.
auto.
contradict H9.
rewrite -> H9.
contradict H6.
apply and_not_or.
split.
apply le_not_lt.
apply H6.
apply le_not_lt.
apply H6.

assert (cs <= getPhysical (getTLB (pred f) MMU) <= ce).
apply H1.
auto.
rewrite -> H4 in H6.

rewrite <- sameMMULookup.
auto.
contradict H9.
rewrite -> H9.
contradict H6.
apply and_not_or.
split.
apply le_not_lt.
apply H6.
apply le_not_lt.
apply H6.

(* Case 8: svaDeclareStack *)
auto.

(* Case 9: jeq *)
auto.

(* Case 10: jeq *)
auto.

(* Case 11: jne *)
auto.

(* Case 12: jne *)
auto.

(* Case 13: svaLoadPGTable *)
auto.

(* Case 14: svaInitStack *)
auto.

(* Case 15: svaSwap *)
auto.

(* Case 16: trap *)
auto.

(* Case 17: iret *)
auto.

(* Case 18: svaRegisterTrap *)
auto.

(* Case 19: svaSaveIContext *)
auto.

(* Case 20: svaLoadIContext *)
auto.

(* Case 21: svaPushFunction *)
auto.
Qed.

Theorem alwaysInText : forall (c1 c2 : config) (v : nat),
(getTextStart c1 <= getPhysical (getTLB v (getCMMU c1)) <= getTextEnd c1) /\
(c1 ==> c2) ->
(getTextStart c2 <= getPhysical (getTLB v (getCMMU c2)) <= getTextEnd c2).
Proof.
intros.
destruct H as [H1 H].
destruct H.
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
simpl in H1.
destruct H as [H10 H].
destruct H as [H11 H].
destruct H as [H12 H].
destruct H as [H13 H].
destruct H as [H14 H].
destruct H as [H15 H].
destruct H as [H16 H].
rewrite -> H12 in H14.
assert (v <> v0).
contradict H1.
rewrite -> H1.
contradict H14.
apply and_not_or.
split.
apply le_not_lt.
apply H14.
apply le_not_lt.
apply H14.
rewrite <- sameMMULookup.
auto.
auto.

(* The remaining cases *)
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
