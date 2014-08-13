(*
 * Module: TLB
 *
 * Description:
 *  This module defines the functions used to represent a TLB entry.
 *)

Require Import Arith.

(*
 * Define basic inductive types for a TLB entry.
 *)
Inductive ReadTy  : Type := | Read  | NoRead.
Inductive WriteTy : Type := | Write | NoWrite.
Inductive ExecTy  : Type := | Exec  | NoExec.
Inductive TLBTy : Type :=
  | emptyTLB
  | TLB : nat -> ReadTy -> WriteTy -> ExecTy -> TLBTy.

(*
 * Function: definedTLB
 *
 * Description:
 *   Determine whether this TLB represents a defined translation from a
 *   virtual address to a physical address.
 *)
Definition definedTLB (tlb : TLBTy) :=
  match tlb with
  | emptyTLB => False
  | TLB n R W X => True
end.

(*
 * Function: getPhysical
 *
 * Description:
 *   Get the physical address out of the TLB.
 *)
Definition getPhysical (tlb : TLBTy) :=
  match tlb with
  | emptyTLB => 0
  | TLB n R W X => n
end.

(*
 * Functions for determining whether a TLB entry permits
 * read/write/execute access.
 *)
Definition TLBPermitsRead (tlb : TLBTy) : Prop :=
  match tlb with 
  | emptyTLB => False
  | TLB n Read   W X => True
  | TLB n NoRead W X => False
end.

Definition TLBPermitsWrite (tlb : TLBTy) : Prop :=
  match tlb with 
  | emptyTLB => False
  | TLB n R Write   X => True
  | TLB n R NoWrite X => False
end.

Definition TLBPermitsExec (tlb : TLBTy) : Prop :=
  match tlb with 
  | emptyTLB => False
  | TLB n R W Exec => True
  | TLB n R W NoExec => False
end.

Lemma PermitsWriteImpliesWrite : forall (n : nat) (r : ReadTy) (w : WriteTy) (e : ExecTy),
TLBPermitsWrite (TLB n r w e) -> w = Write.
intros.
induction w.
reflexivity.
contradiction H.
Qed.

