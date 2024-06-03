(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Error AnError *)

(* Error AnotherError *)

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "require" |),
          [
            Value.Bool false,
            M.call (|
              M.get_name (| "AnError" |),
              [
                Value.Integer 1,
                Value.String "two",
                Value.Integer 3
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
        M.call (|
          M.get_name (| "require" |),
          [
            Value.Bool false,
            M.call (|
              M.get_name (| "AnotherError" |),
              [
                Value.Integer 4,
                Value.String "five",
                Value.Integer 6
              ]
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
