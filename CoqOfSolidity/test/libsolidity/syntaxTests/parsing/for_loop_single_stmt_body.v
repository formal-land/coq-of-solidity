(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module test.
  Definition fun (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.define (|
          [ "i" ],
          Value.Integer 0
        |) in
      let _ :=
        M.for_ (|
          M.assign (|
            "=",
            M.get_name (| "i" |),
            Value.Integer 0
          |),
          M.bin_op (|
            "<",
            M.get_name (| "i" |),
            Value.Integer 10
          |),
          M.un_op (|
            false,
            "++",
            M.get_name (| "i" |)
          |),
          M.continue (||)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End test.
