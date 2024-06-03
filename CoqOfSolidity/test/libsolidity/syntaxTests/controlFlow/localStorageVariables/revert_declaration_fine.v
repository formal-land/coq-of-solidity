(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  (* Struct S *)

  Definition s : Value.t :=
    undefined.

  Definition g (α : list Value.t) : M :=
    match α with
    | [flag] =>
      let _ :=
        M.define (|
          [ "c" ],
          Value.Default
        |) in
      let _ :=
        if M.get_name (| "flag" |) then
          M.assign (|
            "=",
            M.get_name (| "c" |),
            M.get_name (| "s" |)
          |)
        else
          M.call (|
            M.get_name (| "revert" |),
            []
          |) in
      let _ :=
        M.get_name (| "s" |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
