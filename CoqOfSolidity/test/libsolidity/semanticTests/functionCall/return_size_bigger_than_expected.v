(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Interface *)
Module ShortReturn.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      not implemented
    | _ => M.impossible "invalid number of parameters"
    end.
End ShortReturn.


(* Contract *)
Module LongReturn.
  Definition f (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End LongReturn.


(* Contract *)
Module Test.
  Definition test (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.define (|
          [ "longReturn" ],
          M.call (|
            NewExpression Ty.path "LongReturn"
,
            []
          |)
        |) in
      let _ :=
        M.define (|
          [ "freeMemoryBefore" ],
          Value.Default
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 31
src: 310:64:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 333:16:0declaration: 29isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      let _ :=
        M.call (|
          M.member_access (|
            M.call (|
              M.get_name (| "ShortReturn" |),
              [
                M.call (|
                  Ty.path "address",
                  [
                    M.get_name (| "longReturn" |)
                  ]
                |)
              ]
            |),
            "f"
          |),
          []
        |) in
      let _ :=
        M.define (|
          [ "freeMemoryAfter" ],
          Value.Default
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 44
src: 462:63:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 485:15:0declaration: 42isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      let _ :=
        M.return_ (|
          M.bin_op (|
            "-",
            M.get_name (| "freeMemoryAfter" |),
            M.get_name (| "freeMemoryBefore" |)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End Test.
