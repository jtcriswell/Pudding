(*
 * Module: Config
 *
 * Description:
 *  This module defines the configuration that is used in the small-step
 *  semantics as well as functions that permit elements of the configuration
 *  to be extracted easily.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.

(* Load SVAOS specific modules *)
Require Export Stack.
Require Export MMU.
Require Export IC.
Require Export Thread.

(*
 * Define the configuration which includes:
 *  o The MMU (maps virtual addresses to physical addresses)
 *  o The store (stores both values and instructions)
 *  o The value of the one register in this computer
 *  o The program counter (a virtual address)
 *  o The stack pointer (a virtual address)
 *  o The list of valid jump target addresses
 *  o The first physical memory address used for the code segment
 *  o The last physical memory address used for the code segment
 *  o A list of stacks (specified by virtual addresses)
 *  o The address space identifier
 *  o The current thread identifier
 *  o The next available thread identifier
 *  o A stack of threads
 *  o The first virtual address of the ghost address space
 *  o The last virtual address of the ghost address space
 *  o The list of physical addresses mapped into ghost memory.
 *  o The address of the trap handler
 *)
Inductive config : Type :=
  | C : MMU ->
        store ->
        tm ->
        nat ->
        nat ->
        list nat ->
        nat ->
        nat ->
        list Stack ->
        nat ->
        nat ->
        nat ->
        ThreadList ->
        nat ->
        nat ->
        list nat ->
        nat ->
        config.

(* Eval simpl in (C emptyMMU emptyStore 0 0 nil 0 0). *)

(*
 * Function: getReg
 *
 * Description:
 *  Get the register out of a configuration.
 *)
Definition getReg (c : config) : tm :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => Reg
end.

(*
 * Function: getPC
 *
 * Description:
 *  Get the program counter out of a configuration.
 *)
Definition getPC (c : config) : nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => PC
end.

(*
 * Function: getCFG
 *
 * Description:
 *  Get the control-flow graph out of a configuration.
 *)
Definition getCFG (c : config) : list nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => CFG
end.

Definition getTH (c : config) : nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => th
end.

(*
 * Function: getTextStart
 *
 * Description:
 *   Get the first byte of the text segment.
 *)
Definition getTextStart (c : config) : nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => cs
end.

Definition getTextEnd (c : config) : nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => ce
end.

(*
 * Function: getStore
 *
 * Description:
 *   Get the store held within this configuration.
 *)
Definition getStore (c : config) : store :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => DS
end.

(*
 * Function: getCMMU
 *
 * Description:
 *   Get the MMU held within this configuration.
 *)
Definition getCMMU (c : config) : MMU :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => MMU
end.

Definition getGhostStart (c : config) : nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => gvs
end.

Definition getGhostEnd (c : config) : nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => gve
end.

(*
 * Function: getGhost
 *
 * Description:
 *   Get the list of ghost physical pages.
 *)
Definition getGhost (c : config) : list nat :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => gl
end.

(*
 * Function: canExec
 *
 * Description:
 *   This function determines whether the address at the specified program
 *   counter is enabled for execute access.
 *)
Definition canExecConfig (c : config) : Prop :=
  match c with 
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
      (canExec PC MMU)
end.

(*
 * Function: incPC()
 *
 * Description:
 *  Return a new configuration that has an incremented PC.
 *)
Definition incPC (c : config) : config :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
    C MMU DS Reg (S PC) SP CFG cs ce st asid tid ntid tl gvs gve gl th
end.

(*
 * Function: setReg()
 *
 * Description:
 *  Return a new configuration that has the register set to the specified
 *  value.
 *)
Definition setReg (c : config) (n : nat) : config :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
    C MMU DS (val n) PC SP CFG cs ce st asid tid ntid tl gvs gve gl th
end.

(*
 * Function: vlookup()
 *
 * Description:
 *  Read a value at a virtual address from the memory in the configuration.
 *)
Definition vlookup (vaddr : nat) (c : config) :=
  (vLookup vaddr (getCMMU c) (getStore c)).

(*
 * Function: getInsn
 *
 * Description:
 *   This function returns the instrution at the current PC in the specified
 *   configuration.
 *)
Definition getInsn (c : config) : tm := (vlookup (getPC c) c).

Definition getCurrThread (c : config) :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => tid
end.

(*
 * Function: getThreadList
 *
 * Description:
 *   Fetch the thread list within the specified configuration.
 *)
Definition getThreadList (c : config) : ThreadList :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th => tl
end.

(*
 * Function: setThreadList
 *
 * Description:
 *   Set the thread list within the specified configuration.
 *)
Definition setThreadList (ntl : ThreadList) (c : config) : config :=
  match c with
  | (C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th) =>
    (C MMU DS Reg PC SP CFG cs ce st asid tid ntid ntl gvs gve gl th)
end.

(*
 * Function: validConfig
 *
 * Description:
 *  Define a proposition that determines whether a configuration is valid.
 *  The purpose of this function is to provide basic sanity checks on the
 *  definition of a configuration; it isn't meant to show that configurations
 *  have useful properties.
 *)
Definition validConfig (c : config) : Prop :=
  match c with 
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
      (* The code segment start is lower than the code segment end *)
      (0 < cs <= ce) /\ (0 < gvs <= gve) /\ (stacksWellFormed st)
end.

(*
 * Function: validThreadIDs
 *
 * Description:
 *  This function determines whether the relationship between the current
 *  thread ID and the next thread ID holds.
 *
 * Note:
 *  This is the VTID invariant in the Criswell dissertation.
 *)
Definition validThreadIDs (c : config) : Prop :=
  match c with 
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
      (tid < length tl) /\ (ntid < length tl)
end.

(*
 * Function: validThread
 *
 * Description:
 *  Define a proposition that determines whether a thread in the thread stack
 *  is valid.  To be valid, it must either not represent saved program state,
 *  or it must represent saved program state (in which case the program counter
 *  should either be a valid CFG target or an instruction following an svaSwap
 *  instruction).
 *)
Definition validThread (t : SVAThread)
                       (cfg : list nat)
                       (mmu : MMU)
                       (ds : store) : Prop :=
  match t with
  | Thread false pc icl isl => True
  | Thread true  pc icl isl =>
      (In pc cfg) \/ ((vLookup (minus pc 1) mmu ds) = svaSwap)
  end.

Definition validCFG3 (cfg : list nat) (mmu : MMU) (cs ce : nat) :=
  forall (f : nat), (In f cfg) ->
    (cs <= (getPhysical (getTLB f mmu)) <= ce) /\
    (cs <= (getPhysical (getTLB (pred f) mmu)) <= ce).

(*
 * Function: ValidCFG2
 *
 * Description:
 *  Determine if all of the targets within a CFG are within the code segment
 *  of the configurtion.  This one takes more parameters and is used to
 *  remove uneeded parts of the configuration.
 *
 * Notes:
 *  Note that we require that the address prior to the function also be in the
 *  code segment.  We do this so that proofs which reason about traps and iret
 *  "just work."  This really is not the right way to do it; the ICInText
 *  function should be updated so that the previous instruction does not need
 *  to be in the code segment if the address is in the CFG.  However, that
 *  change requires much more refactoring than I currently have time to do, so
 *  we go with this hack.
 *)
Fixpoint validCFG2 (cfg : list nat) (mmu : MMU) (cs ce : nat) : Prop :=
  match cfg with
  | nil => True
  | n :: t =>
    cs <= (getPhysical (getTLB n mmu)) <= ce /\
    cs <= (getPhysical (getTLB (pred n) mmu)) <= ce /\
    (validCFG2 t mmu cs ce)
  end.

(*
 * Function: validCFG
 *
 * Description:
 *  Determine if all of the targets within a CFG are within the code segment
 *  of the configurtion.
 *
 * Notes:
 *  This is invariant CFGT in the Oakland 2014 paper.
 *)
Definition validCFG (c : config) (cfg : list nat) : Prop :=
  validCFG2 cfg (getCMMU c) (getTextStart c) (getTextEnd c).

(*
 * Lemma: cfg23
 *
 * Descripton:
 *  Prove that validCFG2 and validCFG3 can be used interchangably.
 *)
Lemma cfg23 : forall (cfg : list nat) (mmu : MMU) (cs ce : nat),
  validCFG2 cfg mmu cs ce -> validCFG3 cfg mmu cs ce.
Proof.
intros cfg mmu.
induction cfg.

(* Case 1: Base case: No targets in the CFG *)
intros.
unfold validCFG3.
intros.
contradiction.

(* Case 2: Induction case: targets in the CFG *)
intros.
unfold validCFG3.
intros.
unfold validCFG2 in H.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
fold validCFG2 in H3.
unfold In in H0.
destruct H0 as [I1 | I2].
rewrite <- I1.
auto.
apply IHcfg.
auto.
auto.
Qed.

(*
 * Lemma: cfg32
 *
 * Descripton:
 *  Prove that validCFG2 and validCFG3 can be used interchangably.
 *)
Lemma cfg32 : forall (cfg : list nat) (mmu : MMU) (cs ce : nat),
  validCFG3 cfg mmu cs ce -> validCFG2 cfg mmu cs ce.
Proof.
intros cfg mmu.
induction cfg.

(* Case 1: Base case: No targets in the CFG *)
intros.
unfold validCFG2.
auto.

(* Case 2: Induction case: targets in the CFG *)
intros.
unfold validCFG2.
split.
apply H.
unfold In.
auto.
split.
apply H.
unfold In.
auto.
fold validCFG2.
apply IHcfg.
unfold validCFG3 in H.
unfold validCFG3.
intros.
apply H.
apply in_cons.
auto.
Qed.

(*
 * Function: validThreadList
 *
 * Description:
 *  This function determines whether all of the threads in a thread list
 *  are valid.
 *)
Fixpoint validThreadList (tl : ThreadList)
                         (cfg : list nat)
                         (mmu : MMU)
                         (ds : store) : Prop :=
  match tl with
  | nil => True
  | h :: t => (validThread h cfg mmu ds) /\ (validThreadList t cfg mmu ds)
  end.

(*
 * Function: threadInText
 *
 * Description:
 *  Determine whether a thread's PC value is within a configuration's text
 *  segment.
 *)
Definition threadInText (t : SVAThread) (cfg : list nat) (mmu : MMU) (cs ce : nat) : Prop :=
  match t with
  | Thread false pc icl isl => True
  | Thread true  pc icl isl =>
    cs <= (getPhysical (getTLB pc mmu)) <= ce /\
    ((In pc cfg) \/ (cs <= (getPhysical (getTLB (pred pc) mmu)) <= ce))
  end.

(*
 * Function: threadListInText
 *
 * Description:
 *  This function determines whether all of the threads in a thread list
 *  are within the text segment.
 *
 * Notes:
 *  This is invariant tlText in the Oakland 2014 paper.
 *)
Fixpoint threadListInText (tl : ThreadList) (cfg : list nat) (mmu : MMU) (cs ce : nat) : Prop :=
  match tl with
  | nil => True
  | h :: t => (threadInText h cfg mmu cs ce) /\ (threadListInText t cfg mmu cs ce)
  end.

(*
 * Function: textNotWritable
 *
 * Description:
 *   This function determines whether a configuration has an unwriteable
 *   text segment.
 *)
Definition textNotWriteable (c : config) : Prop :=
  match c with 
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
      (* The code segment is not writable *)
      forall (v : nat),
      (cs <= (getPhysical (getTLB v MMU)) <= ce) -> not (canWrite v MMU)
end.

(*
 * Function: textMappedOnce
 *
 * Description:
 *   This function determines whether all of the physical memory locations
 *   within the text segment are mapped to only a single virtual address.
 *)
Definition textMappedOnce (c : config) : Prop :=
  match c with 
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
      forall (v1 v2 : nat),
      (cs <= (getPhysical (getTLB v1 MMU)) <= ce) /\ (v1 <> v2) ->
      (getPhysical (getTLB v1 MMU)) <> (getPhysical (getTLB v2 MMU))
end.

(*
 * Function: textMappedLinear
 *
 * Description:
 *  This function determines whether the text segment of a configuration is
 *  mapped in a linear fashion; if a virtual address is in the text segment,
 *  then either the next address also is or the current address is a jump.
 *
 * Notes:
 *  This is the textMappedLiner invariant in the Oakland paper.
 *)
Definition textMappedLinear (c : config) : Prop :=
  forall (v : nat),
  ((getTextStart c) <= (getPhysical (getTLB v (getCMMU c))) <= (getTextEnd c))
  ->
  ((getTextStart c) <= (getPhysical (getTLB (S v) (getCMMU c))) <= (getTextEnd c))
  \/ ((vlookup v c) = jmp).

Definition pcInText (c : config) : Prop :=
  ((getTextStart c) <= (getPhysical (getTLB (getPC c) (getCMMU c))) <= (getTextEnd c)).

(*
 * Function: makeIC
 *
 * Description:
 *  Take a configuration and create an Interrupt Context from its state.
 *)
Definition makeIC (c : config) : InterruptContext :=
  match c with
  | C MMU DS Reg PC SP CFG cs ce st asid tid ntid tl gvs gve gl th =>
    match Reg with 
    | (val n) => (IC n PC SP 0)
    | _ => (IC 0 PC SP 0)
  end
end.
