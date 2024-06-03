(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Library *)
Module D.
  Definition length (α : list Value.t) : M :=
    match α with
    | [self] =>
      let _ :=
        M.return_ (|
          M.member_access (|
            M.call (|
              Ty.path "bytes",
              [
                M.get_name (| "self" |)
              ]
            |),
            "length"
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End D.


(* Contract *)
Module C.
  Axiom using : M.usingLibrary (|
      Some (Ty.path "string"),
      UsingKind.Local,
      "D"
    |).

  Definition x : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "x" |),
          Value.String "abc"
        |) in
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "x" |),
              "length"
            |),
            []
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
          [ "s" ],
          Value.String "abc"
        |) in
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "s" |),
              "length"
            |),
            []
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
