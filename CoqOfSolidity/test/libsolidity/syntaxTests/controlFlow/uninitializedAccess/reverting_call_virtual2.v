(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module B.
  Definition iWillRevert (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition test (α : list Value.t) : M :=
    match α with
    | [_param] =>
      let _ :=
        if M.get_name (| "_param" |) then
          M.return_ (|
            Value.Integer 1
          |)
        else
          Value.Tuple [] in
      let _ :=
        M.call (|
          M.get_name (| "iWillRevert" |),
          []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End B.


(* Contract *)
Module C.
  Definition iWillRevert (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "revert" |),
          []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
