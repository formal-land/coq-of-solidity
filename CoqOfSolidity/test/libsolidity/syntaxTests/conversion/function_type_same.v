(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition dummy : Value.t :=
    undefined.

  Definition h_nonpayable (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "dummy" |),
          Value.Integer 1
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h_payable (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h_view (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.get_name (| "dummy" |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h_pure (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "g_nonpayable" ],
          M.member_access (|
            M.get_name (| "this" |),
            "h_nonpayable"
          |)
        |) in
      let _ :=
        M.get_name (| "g_nonpayable" |) in
      let _ :=
        M.define (|
          [ "g_payable" ],
          M.member_access (|
            M.get_name (| "this" |),
            "h_payable"
          |)
        |) in
      let _ :=
        M.get_name (| "g_payable" |) in
      let _ :=
        M.define (|
          [ "g_view" ],
          M.member_access (|
            M.get_name (| "this" |),
            "h_view"
          |)
        |) in
      let _ :=
        M.get_name (| "g_view" |) in
      let _ :=
        M.define (|
          [ "g_pure" ],
          M.member_access (|
            M.get_name (| "this" |),
            "h_pure"
          |)
        |) in
      let _ :=
        M.get_name (| "g_pure" |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
