(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition a : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.member_access (|
              M.get_name (| "x" |),
              "length"
            |),
            M.member_access (|
              M.call (|
                Ty.path "bytes16",
                [
                  M.call (|
                    Ty.path "uint128",
                    [
                      Value.Integer 2
                    ]
                  |)
                ]
              |),
              "length"
            |),
            M.bin_op (|
              "+",
              M.member_access (|
                M.get_name (| "a" |),
                "length"
              |),
              Value.Integer 7
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
