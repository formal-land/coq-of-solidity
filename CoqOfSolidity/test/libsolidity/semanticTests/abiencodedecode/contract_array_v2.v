(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "abi" |),
              "decode"
            |),
            [
              M.get_name (| "x" |),
              Value.Tuple [
                M.index_access (|
                  M.get_name (| "C" |),
                  None
                |)
              ]
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "c" ],
          M.call (|
            NewExpression Ty.array (Ty.path "C") None
,
            [
              Value.Integer 3
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "c" |),
            Some (Value.Integer 0)
          |),
          M.call (|
            M.get_name (| "C" |),
            [
              M.call (|
                Ty.path "address",
                [
                  Value.Integer 0x42
                ]
              |)
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "c" |),
            Some (Value.Integer 1)
          |),
          M.call (|
            M.get_name (| "C" |),
            [
              M.call (|
                Ty.path "address",
                [
                  Value.Integer 0x21
                ]
              |)
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "c" |),
            Some (Value.Integer 2)
          |),
          M.call (|
            M.get_name (| "C" |),
            [
              M.call (|
                Ty.path "address",
                [
                  Value.Integer 0x23
                ]
              |)
            ]
          |)
        |) in
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "abi" |),
              "encode"
            |),
            [
              M.get_name (| "c" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
