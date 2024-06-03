(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition s : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [data] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "s" |),
          M.get_name (| "data" |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "s" |),
            Some (Value.Integer 0)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
