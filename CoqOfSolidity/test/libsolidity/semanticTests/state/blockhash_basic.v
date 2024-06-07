(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition genesisHash : Value.t :=
    undefined.

  Definition currentHash : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "require" |),
          [
            M.bin_op (|
              "==",
              M.member_access (|
                M.get_name (| "block" |),
                "number"
              |),
              Value.Integer 1
            |)
          ]
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "genesisHash" |),
          M.call (|
            M.get_name (| "blockhash" |),
            [
              Value.Integer 0
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "currentHash" |),
          M.call (|
            M.get_name (| "blockhash" |),
            [
              Value.Integer 1
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [blockNumber] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "blockhash" |),
            [
              M.get_name (| "blockNumber" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
