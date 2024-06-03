(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition data : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "data" |),
          M.get_name (| "x" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
