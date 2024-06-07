(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

Axiom user_type_Small : Ty.path "Small" = Ty.path "uint16".

Axiom user_type_Left : Ty.path "Left" = Ty.path "bytes2".

(* Struct S *)

(* Contract *)
Module C.
  Definition s : Value.t :=
    undefined.

  Definition small : Value.t :=
    undefined.

  Definition l : Value.t :=
    undefined.

  Definition f (α : list Value.t) : M :=
    match α with
    | [_s] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "s" |),
          M.get_name (| "_s" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [_small] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "small" |),
          M.get_name (| "_small" |)
        |) in
      let _ :=
        M.return_ (|
          M.get_name (| "small" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [_left] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "l" |),
          M.get_name (| "_left" |)
        |) in
      let _ :=
        M.return_ (|
          M.get_name (| "l" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
