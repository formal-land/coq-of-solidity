(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition array : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "y" ],
          M.call (|
            M.member_access (|
              M.get_name (| "array" |),
              "push"
            |),
            []
          |)
        |) in
      let _ :=
        M.return_ (|
          M.get_name (| "y" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition lv (α : list Value.t) : M :=
    match α with
    | [value] =>
      let _ :=
        M.assign (|
          "=",
          M.call (|
            M.member_access (|
              M.get_name (| "array" |),
              "push"
            |),
            []
          |),
          M.get_name (| "value" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition a (α : list Value.t) : M :=
    match α with
    | [index] =>
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "array" |),
            Some (M.get_name (| "index" |))
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition l (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.member_access (|
            M.get_name (| "array" |),
            "length"
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
