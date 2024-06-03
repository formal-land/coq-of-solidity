(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module A.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "b" ],
          Value.Default
        |) in
      let _ :=
        M.define (|
          [ "a" ],
          Value.Default
        |) in
      let _ :=
        M.assign (|
          "=",
          Value.Tuple [
            Value.Tuple [
              Value.Tuple [
                M.get_name (| "b" |)
              ]
            ]
          ],
          Value.Tuple [
            Value.Integer 1,
            Value.Integer 2,
            M.get_name (| "a" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End A.
