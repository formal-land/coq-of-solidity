(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module Test.
  (* Struct S *)

  Definition data : Value.t :=
    undefined.

  Definition testInit (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "d" ],
          Value.Default
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.member_access (|
            M.index_access (|
              M.get_name (| "d" |),
              Some (Value.Integer 0)
            |),
            "x"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "y" |),
          M.member_access (|
            M.index_access (|
              M.get_name (| "d" |),
              Some (Value.Integer 0)
            |),
            "y"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "z" |),
          M.member_access (|
            M.index_access (|
              M.get_name (| "d" |),
              Some (Value.Integer 0)
            |),
            "z"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a" |),
          M.index_access (|
            M.member_access (|
              M.index_access (|
                M.get_name (| "d" |),
                Some (Value.Integer 0)
              |),
              "a"
            |),
            Some (Value.Integer 1)
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "flag" |),
          Value.Bool true
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition testCopyRead (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.index_access (|
              M.get_name (| "data" |),
              Some (Value.Integer 2)
            |),
            "x"
          |),
          Value.Integer 1
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.index_access (|
              M.get_name (| "data" |),
              Some (Value.Integer 2)
            |),
            "y"
          |),
          Value.Integer 2
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.index_access (|
              M.get_name (| "data" |),
              Some (Value.Integer 2)
            |),
            "z"
          |),
          Value.Integer 3
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.member_access (|
              M.index_access (|
                M.get_name (| "data" |),
                Some (Value.Integer 2)
              |),
              "a"
            |),
            Some (Value.Integer 1)
          |),
          Value.Integer 4
        |) in
      let _ :=
        M.define (|
          [ "s" ],
          M.index_access (|
            M.get_name (| "data" |),
            Some (Value.Integer 2)
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.member_access (|
            M.get_name (| "s" |),
            "x"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "y" |),
          M.member_access (|
            M.get_name (| "s" |),
            "y"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "z" |),
          M.member_access (|
            M.get_name (| "s" |),
            "z"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a" |),
          M.index_access (|
            M.member_access (|
              M.get_name (| "s" |),
              "a"
            |),
            Some (Value.Integer 1)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition testAssign (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "s" ],
          Value.Default
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "x"
          |),
          Value.Integer 1
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "y"
          |),
          Value.Integer 2
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "z"
          |),
          Value.Integer 3
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.member_access (|
              M.get_name (| "s" |),
              "a"
            |),
            Some (Value.Integer 1)
          |),
          Value.Integer 4
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          M.member_access (|
            M.get_name (| "s" |),
            "x"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "y" |),
          M.member_access (|
            M.get_name (| "s" |),
            "y"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "z" |),
          M.member_access (|
            M.get_name (| "s" |),
            "z"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a" |),
          M.index_access (|
            M.member_access (|
              M.get_name (| "s" |),
              "a"
            |),
            Some (Value.Integer 1)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Test.
