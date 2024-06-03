(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Pragma abicoderv2 *)

(* Contract *)
Module C.
  Definition ggg (α : list Value.t) : M :=
    match α with
    | [s] =>
      let _ :=
        M.index_access (|
          M.get_name (| "s" |),
          Some (Value.Integer 0)
        |) in
      let _ :=
        M.return_ (|
          M.member_access (|
            M.get_name (| "msg" |),
            "data"
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f (α : list Value.t) : M :=
    match α with
    | [a] =>
      let _ :=
        M.define (|
          [ "m" ],
          M.call (|
            NewExpression Ty.array (Ty.path "uint8") None
,
            [
              M.member_access (|
                M.get_name (| "a" |),
                "length"
              |)
            ]
          |)
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 37
src: 326:93:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 366:1:0declaration: 29isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      let _ :=
        M.return_ (|
          M.call (|
            M.member_access (|
              M.get_name (| "this" |),
              "ggg"
            |),
            [
              M.get_name (| "m" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
