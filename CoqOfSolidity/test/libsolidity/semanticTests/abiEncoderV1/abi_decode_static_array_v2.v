(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [data] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "abi" |),
              "decode"
            |),
            [
              M.get_name (| "data" |),
              Value.Tuple [
                M.index_access (|
                  M.index_access (|
                    Ty.path "uint256",
                    Some (Value.Integer 2)
                  |),
                  Some (Value.Integer 3)
                |)
              ]
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
