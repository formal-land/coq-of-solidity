(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition data : Value.t :=
    undefined.

  Definition m_c : Value.t :=
    undefined.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            Value.Integer 1,
            Value.Integer 2,
            M.get_name (| "data" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            Value.Integer 5,
            Value.Integer 6
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "data" |),
            "push"
          |),
          [
            Value.Integer 3
          ]
        |) in
      let _ :=
        M.define (|
          [ "a" ],
          Value.Default
        |) in
      let _ :=
        M.define (|
          [ "b" ],
          Value.Default
        |) in
      let _ :=
        M.assign (|
          "=",
          Value.Tuple [
            M.get_name (| "a" |),
            M.get_name (| "b" |)
          ],
          M.call (|
            M.member_access (|
              M.get_name (| "this" |),
              "h"
            |),
            []
          |)
        |) in
      let _ :=
        if M.bin_op (|
          "||",
          M.bin_op (|
            "!=",
            M.get_name (| "a" |),
            Value.Integer 5
          |),
          M.bin_op (|
            "!=",
            M.get_name (| "b" |),
            Value.Integer 6
          |)
        |) then
          M.return_ (|
            Value.Integer 1
          |)
        else
          Value.Tuple [] in
      let _ :=
        M.define (|
          [ "c" ],
          M.get_name (| "m_c" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          Value.Tuple [
            M.get_name (| "a" |),
            M.get_name (| "b" |),
            M.get_name (| "c" |)
          ],
          M.call (|
            M.get_name (| "g" |),
            []
          |)
        |) in
      let _ :=
        if M.bin_op (|
          "||",
          M.bin_op (|
            "||",
            M.bin_op (|
              "!=",
              M.get_name (| "a" |),
              Value.Integer 1
            |),
            M.bin_op (|
              "!=",
              M.get_name (| "b" |),
              Value.Integer 2
            |)
          |),
          M.bin_op (|
            "!=",
            M.index_access (|
              M.get_name (| "c" |),
              Some (Value.Integer 0)
            |),
            Value.Integer 3
          |)
        |) then
          M.return_ (|
            Value.Integer 2
          |)
        else
          Value.Tuple [] in
      let _ :=
        M.assign (|
          "=",
          Value.Tuple [
            M.get_name (| "a" |),
            M.get_name (| "b" |)
          ],
          Value.Tuple [
            M.get_name (| "b" |),
            M.get_name (| "a" |)
          ]
        |) in
      let _ :=
        if M.bin_op (|
          "||",
          M.bin_op (|
            "!=",
            M.get_name (| "a" |),
            Value.Integer 2
          |),
          M.bin_op (|
            "!=",
            M.get_name (| "b" |),
            Value.Integer 1
          |)
        |) then
          M.return_ (|
            Value.Integer 3
          |)
        else
          Value.Tuple [] in
      let _ :=
        M.assign (|
          "=",
          Value.Tuple [
            M.get_name (| "a" |),
            M.get_name (| "b" |)
          ],
          Value.Tuple [
            Value.Integer 8,
            Value.Integer 9,
            Value.Integer 10,
            Value.Integer 11,
            Value.Integer 12
          ]
        |) in
      let _ :=
        if M.bin_op (|
          "||",
          M.bin_op (|
            "!=",
            M.get_name (| "a" |),
            Value.Integer 8
          |),
          M.bin_op (|
            "!=",
            M.get_name (| "b" |),
            Value.Integer 10
          |)
        |) then
          M.return_ (|
            Value.Integer 4
          |)
        else
          Value.Tuple [] in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
