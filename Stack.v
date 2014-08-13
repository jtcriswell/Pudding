(*
 * Module: Stack
 *
 * Description:
 *  This module defines a stack and functions that determine properties of
 *  stacks.
 *)

(* Load Coq Standard Library modules *)
Require Import Arith.
Require Import List.

(*
 *  Inductive Type: stack
 *
 *  Description:
 *    This type describes a stack.  A stack is just a region of memory, and
 *    this inductive type merely ensures that the stack's lower address is
 *    less than its upper address and that it doesn't use the zero address.
 *
 *  Note:
 *    This code is a modified version of the pair constructor from
 *    http://www.cis.upenn.edu/~bcpierce/sf/Lists.html#lab47.
 *)
Inductive Stack : Type :=
  stack : nat -> nat -> Stack.
Notation "( x , y )" := (stack x y).

(*
 * Define a function to indicate that a stack is well-formed.
 *)
Definition stackWellFormed (s : Stack) : Prop :=
  match s with
    (x,y) => (0 < x < y)
  end.

(*
 * Define a function that determines that all the stacks in a list are
 * well formed.
 *)
Fixpoint stacksWellFormed (sl : list Stack) : Prop :=
  match sl with
  | nil => True
  | h :: t => (stackWellFormed h) /\ stacksWellFormed (t)
  end.

(*
 * Function: within
 *
 * Description:
 *  Determine whether a value (usually a stack pointer) falls within the stack.
 *)
Definition within (n : nat) (s : Stack) : Prop :=
  match s with
    (x,y) => (x <= n <= y)
  end.

Fixpoint Within (n : nat) (sl : list Stack) : Prop :=
  match sl with
  | nil => False
  | h :: t => (within n h) \/ (Within n t)
  end.


