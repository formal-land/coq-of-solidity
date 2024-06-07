(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module c.
  Definition f (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a" |),
          Value.Integer 1
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End c.
