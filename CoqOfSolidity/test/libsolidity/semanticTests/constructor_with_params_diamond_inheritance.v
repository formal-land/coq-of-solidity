(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module A.
  Definition i : Value.t :=
    undefined.

  Definition k : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [newI, newK] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "i" |),
          M.get_name (| "newI" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "k" |),
          M.get_name (| "newK" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End A.


(* Contract *)
Module B.
  Definition j : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [newJ] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "j" |),
          M.get_name (| "newJ" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End B.


(* Contract *)
Module C.
  Definition  (α : list Value.t) : M :=
    match α with
    | [newI, newK] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.


(* Contract *)
Module D.
  Definition  (α : list Value.t) : M :=
    match α with
    | [newI, newK] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End D.
