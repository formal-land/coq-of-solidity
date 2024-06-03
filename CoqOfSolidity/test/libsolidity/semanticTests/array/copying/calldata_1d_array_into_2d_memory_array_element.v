(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.define (|
          [ "m" ],
          M.call (|
            NewExpression Ty.array (Ty.array (Ty.path "uint") None) None
,
            [
              Value.Integer 2
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 0)
          |),
          M.get_name (| "a" |)
        |) in
      let _ :=
        M.return_ (|
          M.get_name (| "m" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.


(* Contract *)
Module Test.
  Definition c : Value.t :=
    M.call (|
      NewExpression Ty.path "C"
,
      []
    |).

  Definition test (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "arr" ],
          M.call (|
            NewExpression Ty.array (Ty.path "uint") None
,
            [
              Value.Integer 4
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "arr" |),
            Some (Value.Integer 0)
          |),
          Value.Integer 13
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "arr" |),
            Some (Value.Integer 1)
          |),
          Value.Integer 14
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "arr" |),
            Some (Value.Integer 2)
          |),
          Value.Integer 15
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "arr" |),
            Some (Value.Integer 3)
          |),
          Value.Integer 16
        |) in
      let _ :=
        M.define (|
          [ "ret" ],
          M.call (|
            M.member_access (|
              M.get_name (| "c" |),
              "f"
            |),
            [
              M.get_name (| "arr" |)
            ]
          |)
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.member_access (|
                M.get_name (| "ret" |),
                "length"
              |),
              Value.Integer 2
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.member_access (|
                M.index_access (|
                  M.get_name (| "ret" |),
                  Some (Value.Integer 0)
                |),
                "length"
              |),
              Value.Integer 4
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.index_access (|
                M.index_access (|
                  M.get_name (| "ret" |),
                  Some (Value.Integer 0)
                |),
                Some (Value.Integer 0)
              |),
              Value.Integer 13
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.index_access (|
                M.index_access (|
                  M.get_name (| "ret" |),
                  Some (Value.Integer 0)
                |),
                Some (Value.Integer 1)
              |),
              Value.Integer 14
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.index_access (|
                M.index_access (|
                  M.get_name (| "ret" |),
                  Some (Value.Integer 0)
                |),
                Some (Value.Integer 2)
              |),
              Value.Integer 15
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.index_access (|
                M.index_access (|
                  M.get_name (| "ret" |),
                  Some (Value.Integer 0)
                |),
                Some (Value.Integer 3)
              |),
              Value.Integer 16
            |)
          ]
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.member_access (|
                M.index_access (|
                  M.get_name (| "ret" |),
                  Some (Value.Integer 1)
                |),
                "length"
              |),
              Value.Integer 0
            |)
          ]
        |) in
      let _ :=
        M.return_ (|
          Value.Bool true
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Test.
