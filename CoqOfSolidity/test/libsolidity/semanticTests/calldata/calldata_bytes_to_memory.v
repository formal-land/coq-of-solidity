(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [data] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "keccak256" |),
            [
              M.call (|
                Ty.path "bytes",
                [
                  M.get_name (| "data" |)
                ]
              |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
