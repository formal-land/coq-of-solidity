(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [b] =>
      let _ :=
        M.define (|
          [ "c" ],
          M.call (|
            M.member_access (|
              M.get_name (| "abi" |),
              "decode"
            |),
            [
              M.get_name (| "b" |),
              Value.Tuple [
                Ty.path "address"
              ]
            ]
          |)
        |) in
      let _ :=
        M.return_ (|
          M.get_name (| "c" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
