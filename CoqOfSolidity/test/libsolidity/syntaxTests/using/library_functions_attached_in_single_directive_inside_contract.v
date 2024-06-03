(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Library *)
Module L.
  Definition externalFunction (α : list Value.t) : M :=
    match α with
    | [_] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition publicFunction (α : list Value.t) : M :=
    match α with
    | [_] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition internalFunction (α : list Value.t) : M :=
    match α with
    | [_] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End L.


(* Contract *)
Module C.
  Axiom using : M.usingFunctions (|
      Some (Ty.path "uint"),
      UsingKind.Local,
      [
      UsingFunction.Function "L.externalFunction",
      UsingFunction.Function "L.publicFunction",
      UsingFunction.Function "L.internalFunction",
    ]
    |).

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "x" ],
          Value.Default
        |) in
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "x" |),
            "externalFunction"
          |),
          []
        |) in
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "x" |),
            "publicFunction"
          |),
          []
        |) in
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "x" |),
            "internalFunction"
          |),
          []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
