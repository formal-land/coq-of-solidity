(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Error CustomError *)

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "reason" ],
          Value.String "errorReason"
        |) in
      let _ :=
        M.call (|
          M.get_name (| "require" |),
          [
            Value.Bool false,
            M.call (|
              M.get_name (| "CustomError" |),
              [
                M.get_name (| "reason" |)
              ]
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "reason" ],
          Value.String "anotherReason"
        |) in
      let _ :=
        M.call (|
          M.get_name (| "require" |),
          [
            Value.Bool false,
            M.call (|
              M.get_name (| "CustomError" |),
              [
                M.get_name (| "reason" |)
              ]
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
