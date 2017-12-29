Set Implicit Arguments.

Require Import
        String
        Utils.Classes.Monad.

Section IODEF.
  Axiom IO : Type -> Type.

  Axiom retIO : forall {A : Type},  A -> IO A.

  Axiom bindIO : forall {A B : Type}, IO A -> (A -> IO B) -> IO B.

  Axiom putStrLn : string -> IO unit.

  Axiom readFile : string -> IO string.

  Axiom get_args : IO (list string).
End IODEF.

Instance monadIO : Monad IO :=
  {
    ret := fun A => @retIO A
  ; bind := fun A B => @bindIO A B
  }.