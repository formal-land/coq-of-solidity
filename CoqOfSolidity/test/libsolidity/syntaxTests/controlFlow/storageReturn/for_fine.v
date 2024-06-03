(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  (* Struct S *)

  Definition s : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.for_ (|
          M.assign (|
            "=",
            M.get_name (| "c" |),
            M.get_name (| "s" |)
          |),
          Value.Tuple [],
          Value.Tuple [],
          let _ :=
             in
          Value.Tuple []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.for_ (|
          Value.Tuple [],
          M.member_access (|
            Value.Tuple [
              M.assign (|
                "=",
                M.get_name (| "c" |),
                M.get_name (| "s" |)
              |)
            ],
            "f"
          |),
          Value.Tuple [],
          let _ :=
             in
          Value.Tuple []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
