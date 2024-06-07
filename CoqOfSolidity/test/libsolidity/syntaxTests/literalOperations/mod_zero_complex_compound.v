(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module A.
  Definition a : Value.t :=
    Value.Integer 5.

  Definition  (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "%=",
          M.get_name (| "a" |),
          M.call (|
            Ty.path "uint",
            [
              M.bin_op (|
                "%",
                Value.Tuple [
                  M.bin_op (|
                    "*",
                    Value.Tuple [
                      Value.Integer 2
                    ],
                    Value.Integer 2
                  |)
                ],
                Value.Integer 4
              |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End A.
