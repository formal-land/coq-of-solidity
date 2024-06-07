(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module test.
  Definition delLocal (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "v" ],
          Value.Integer 5
        |) in
      let _ :=
        M.un_op (|
          true,
          "delete",
          M.get_name (| "v" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "res" |),
          M.get_name (| "v" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End test.
