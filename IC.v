(*
 * Module: IC
 *
 * Description:
 *  This module defines the Interrupt Context that is used in the small-step
 *  semantics.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.

(*
 * Define the interrupt context.  It is a subset of the configuration and
 * includes the following fields in the following order:
 *
 *  o The machine's register
 *  o The program counter (a virtual address)
 *  o The stack pointer (a virtual address)
 *  o The privilege level
 *)
Inductive InterruptContext : Type :=
  | IC : nat ->
         nat ->
         nat ->
         nat ->
         InterruptContext.

(*
 * Define a stack of Interrupt Contexts.
 *)
Definition ICStack := list InterruptContext.
Definition emptyICStack := nil : list InterruptContext.
Definition itop (ics : ICStack) : InterruptContext := nth 0 ics (IC 0 0 0 0).
Definition push (ic : InterruptContext) (ics : ICStack) := (ic :: ics).
Definition pop  (ics : ICStack) :=
  match ics with
  | nil => nil
  | h :: t => t
end.

(*
 * Function: getICPC
 *
 * Description:
 *  Fetch the program counter value saved within an interrupt context.
 *)
Definition getICPC (ic : InterruptContext) :=
  match ic with 
  | IC Reg PC SP Priv => PC
end.
