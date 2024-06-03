(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition iWillRevertLevel2 (α : list Value.t) : M :=
    match α with
    | [_recurse] =>
      let _ :=
        if M.get_name (| "_recurse" |) then
          M.call (|
            M.get_name (| "iWillRevertLevel1" |),
            []
          |)
        else
          M.call (|
            M.get_name (| "revert" |),
            []
          |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition iWillRevertLevel1 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "iWillRevertLevel2" |),
          [
            Value.Bool true
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition iWillRevert (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "iWillRevertLevel1" |),
          []
        |) in
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
End C.
