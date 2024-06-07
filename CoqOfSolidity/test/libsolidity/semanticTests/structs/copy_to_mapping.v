(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  (* Struct S *)

  Definition s : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "a" ],
          M.call (|
            NewExpression Ty.array (Ty.path "uint16") None
,
            [
              Value.Integer 2
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "a" |),
            Some (Value.Integer 0)
          |),
          Value.Integer 13
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "a" |),
            Some (Value.Integer 1)
          |),
          Value.Integer 14
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "b"
          |),
          Value.String "foo"
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "a"
          |),
          M.get_name (| "a" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.member_access (|
            M.get_name (| "s" |),
            "u"
          |),
          Value.Integer 21
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition m : Value.t :=
    undefined.

  Definition from_state (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 0)
          |),
          M.get_name (| "s" |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 0)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition from_storage (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "sLocal" ],
          M.get_name (| "s" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 1)
          |),
          M.get_name (| "sLocal" |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 1)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition from_memory (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "sMemory" ],
          M.get_name (| "s" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 2)
          |),
          M.get_name (| "sMemory" |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 2)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition from_calldata (α : list Value.t) : M :=
    match α with
    | [sCalldata] =>
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 3)
          |),
          M.get_name (| "sCalldata" |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.get_name (| "m" |),
            Some (Value.Integer 3)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
