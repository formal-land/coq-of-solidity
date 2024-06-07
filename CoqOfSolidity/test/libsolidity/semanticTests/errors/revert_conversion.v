(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Error E *)

(* Contract *)
Module C.
  Definition x : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "x" |),
            "push"
          |),
          [
            Value.Integer 7
          ]
        |) in
      let _ :=
        M.revert (|
          M.call (|
            M.get_name (| "E" |),
            [
              Value.String "abc",
              M.get_name (| "x" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
