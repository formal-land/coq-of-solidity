(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Library *)
Module L.
  Definition pub (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Integer 7
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition inter (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          Value.Integer 8
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End L.


Definition fu (α : list Value.t) : M :=
  match α with
  | [] =>
    let _ :=
      M.return_ (|
        Value.Tuple [
          M.call (|
            M.member_access (|
              M.get_name (| "L" |),
              "pub"
            |),
            []
          |),
          M.call (|
            M.member_access (|
              M.get_name (| "L" |),
              "inter"
            |),
            []
          |)
        ]
      |) in
    Value.Tuple []
  | _ => M.impossible "invalid number of parameters"
  end.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "fu" |),
            []
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
