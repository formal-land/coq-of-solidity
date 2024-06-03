(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition removeSignature (α : list Value.t) : M :=
    match α with
    | [x] =>
      let _ :=
        M.return_ (|
          IndexRangeAccess M.get_name (| "x" |) Value.Integer 4 

        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [_, _, _] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [_, _] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "x" ],
          Value.Integer 0x1234
        |) in
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "this" |),
              "removeSignature"
            |),
            [
              M.call (|
                M.member_access (|
                  M.get_name (| "abi" |),
                  "encodeCall"
                |),
                [
                  M.member_access (|
                    M.get_name (| "this" |),
                    "g"
                  |),
                  Value.Tuple [
                    Value.Integer 0x1234,
                    Value.String "ab",
                    M.call (|
                      Ty.path "bytes2",
                      [
                        M.get_name (| "x" |)
                      ]
                    |)
                  ]
                ]
              |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f2 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "x" ],
          Value.Integer 0x1234
        |) in
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "this" |),
              "removeSignature"
            |),
            [
              M.call (|
                M.member_access (|
                  M.get_name (| "abi" |),
                  "encodeCall"
                |),
                [
                  M.member_access (|
                    M.get_name (| "this" |),
                    "h"
                  |),
                  Value.Tuple [
                    Value.Integer 0x1234,
                    M.call (|
                      Ty.path "uint16",
                      [
                        M.get_name (| "x" |)
                      ]
                    |)
                  ]
                ]
              |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
