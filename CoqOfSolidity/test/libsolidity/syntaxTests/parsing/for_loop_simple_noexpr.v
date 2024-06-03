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
          Value.Tuple [],
          Value.Tuple [],
          Value.Tuple [],
          let _ :=
            M.define (|
              [ "x" ],
              M.get_name (| "i" |)
            |) in
          let _ :=
            M.break (||) in
          let _ :=
            M.continue (||) in
          Value.Tuple []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End test.
