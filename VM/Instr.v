Set Implicit Arguments.

Require Import Ascii.


(* definition of instruction syntax *)

Inductive Instr : Set :=
| Nop : Instr
| Succeed : Instr
| Fail : Instr              
| Chr : ascii -> Instr
| Choice : nat -> Instr
| Commit : bool -> nat -> Instr.

Definition Prog := list Instr.