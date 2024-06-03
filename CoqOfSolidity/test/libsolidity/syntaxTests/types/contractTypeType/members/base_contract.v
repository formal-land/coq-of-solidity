(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module B.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End B.


(* Contract *)
Module C.
  Definition h (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "fs" |),
          M.member_access (|
            M.member_access (|
              M.get_name (| "B" |),
              "f"
            |),
            "selector"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "gs" |),
          M.member_access (|
            M.member_access (|
              M.get_name (| "B" |),
              "g"
            |),
            "selector"
          |)
        |) in
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "B" |),
            "g"
          |),
          []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
