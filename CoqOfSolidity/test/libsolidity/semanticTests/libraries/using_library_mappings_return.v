(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Library *)
Module Lib.
  Definition choose (α : list Value.t) : M :=
    match α with
    | [m, key] =>
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "m" |),
            Some (M.get_name (| "key" |))
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Lib.


(* Contract *)
Module Test.
  Definition m : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.call (|
              M.member_access (|
                M.get_name (| "Lib" |),
                "choose"
              |),
              [
                M.get_name (| "m" |),
                Value.Integer 0
              ]
            |),
            Some (Value.Integer 0)
          |),
          Value.Integer 1
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.call (|
              M.member_access (|
                M.get_name (| "Lib" |),
                "choose"
              |),
              [
                M.get_name (| "m" |),
                Value.Integer 0
              ]
            |),
            Some (Value.Integer 2)
          |),
          Value.Integer 42
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.call (|
              M.member_access (|
                M.get_name (| "Lib" |),
                "choose"
              |),
              [
                M.get_name (| "m" |),
                Value.Integer 1
              ]
            |),
            Some (Value.Integer 0)
          |),
          Value.Integer 23
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.call (|
              M.member_access (|
                M.get_name (| "Lib" |),
                "choose"
              |),
              [
                M.get_name (| "m" |),
                Value.Integer 1
              ]
            |),
            Some (Value.Integer 2)
          |),
          Value.Integer 99
        |) in
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.index_access (|
              M.index_access (|
                M.get_name (| "m" |),
                Some (Value.Integer 0)
              |),
              Some (Value.Integer 0)
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "m" |),
                Some (Value.Integer 0)
              |),
              Some (Value.Integer 1)
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "m" |),
                Some (Value.Integer 0)
              |),
              Some (Value.Integer 2)
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "m" |),
                Some (Value.Integer 1)
              |),
              Some (Value.Integer 0)
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "m" |),
                Some (Value.Integer 1)
              |),
              Some (Value.Integer 1)
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "m" |),
                Some (Value.Integer 1)
              |),
              Some (Value.Integer 2)
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Test.
