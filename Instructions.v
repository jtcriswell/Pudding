(*
 * Module: Instructions
 *
 * Description:
 *  This module defines the various instructions that exist within the language.
 *)

Require Import TLB.
Require Import Arith.

(*
 * Inductive Type: tm
 *
 * Description:
 *   This data type represents all of the instructions that can occur in
 *   the language.  It also contains a "val" instruction which encapsulates
 *   data that can be stored in the store.
 *
 *   It's called "tm" because tm is short for "term" which is what the basic
 *   element of most small-step semantics are called.
 *
 *   This machine has a single register and has memory addressing modes.
 *
 *   val : Represents a value in memory
 *   sec : Represents a secret value in memory
 *   ldi : Load immediate value into register
 *   lda : Load value from specified address into register
 *   sta : Store value in register into specified address
 *   add : Add a constant value to the value in the register.  The result stays
 *         within the register.
 *   map : Add a TLB entry to the MMU.
 *   invalidate : Reset a TLB entry back to a default value.
 *   jmp : Jump to the address located in the register.
 *   jeq : Jump to the specified address if the register is zero.
 *   jne : Jump to the specified address if the register is negative.
 *   trap: Generate a machine trap (syscall, exception, or interrupt).
 *   iret: Return from a trap.
 *   svaDeclareStack : Declare a range of memory to be a stack.
 *   svaLoadPGTable : Load the ASID value
 *   svaInitStack   : Create and initialize a new thread
 *   svaSwap        : Switch to a new thread identified in the register
 *   svaRegisterTrap: Register a trap handler
 *   svaSaveIcontext: Save a copy of the interrupt context
 *   svaLoadIcontext: Save a copy of the interrupt context
 *   svaPushFunction: Push a function frame on to the interrupted stack
 *   jsr : Jump to the subroutine located in the register.
 *   ret : Return to the previously executed jsr instruction.
 *)
Inductive tm : Type :=
  | val  : nat -> tm
  | sec  : tm
  | ldi  : nat -> tm
  | lda  : nat -> tm
  | sta  : nat -> tm
  | add  : nat -> tm
  | sub  : nat -> tm
  | map  : nat -> TLBTy -> tm
  | jmp  : tm
  | jeq  : nat -> tm
  | jne  : nat -> tm
  | trap : tm
  | iret : tm
  | svaDeclareStack : nat -> nat -> tm
  | svaLoadPGTable : tm
  | svaInitStack : nat -> tm
  | svaSwap : tm
  | svaRegisterTrap : tm
  | svaSaveIcontext : tm
  | svaLoadIcontext : tm
  | svaPushFunction : nat -> tm
  | jsr : tm
  | ret : tm.

