(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Interface *)
Module I.
  Definition f (α : list Value.t) : M :=
    match α with
    | [a] =>
      not implemented
    | _ => M.impossible "invalid number of parameters"
    end.
End I.
