(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        TryStatement M.call (|
          M.member_access (|
            M.get_name (| "this" |),
            "f"
          |),
          []
        |) TryCatchClause   let _ :=
           in
        Value.Tuple [], TryCatchClause Error ParameterList.make [
          Definition  : Value.t :=
            undefined.
        ] let _ :=
           in
        Value.Tuple [] in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
