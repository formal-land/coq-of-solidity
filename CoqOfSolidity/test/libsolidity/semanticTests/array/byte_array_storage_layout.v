(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module c.
  Definition data : Value.t :=
    undefined.

  Definition test_short (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        (* Beginning of a node! *)
id: 7
src: 92:53:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 122:9:0declaration: 2sSlot: isOffset: suffix: slotalueSize: 
evmVersion: cancun
 in
      let _ :=
        M.for_ (|
          M.define (|
            [ "i" ],
            Value.Integer 0
          |),
          M.bin_op (|
            "<",
            M.get_name (| "i" |),
            Value.Integer 15
          |),
          M.un_op (|
            false,
            "++",
            M.get_name (| "i" |)
          |),
          let _ :=
            M.call (|
              M.member_access (|
                M.get_name (| "data" |),
                "push"
              |),
              [
                M.call (|
                  Ty.path "bytes1",
                  [
                    M.get_name (| "i" |)
                  ]
                |)
              ]
            |) in
          Value.Tuple []
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 29
src: 239:54:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 273:9:0declaration: 2sSlot: isOffset: suffix: slotalueSize: src: 262:1:0declaration: 5isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition test_long (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        (* Beginning of a node! *)
id: 36
src: 363:53:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 393:9:0declaration: 2sSlot: isOffset: suffix: slotalueSize: 
evmVersion: cancun
 in
      let _ :=
        M.for_ (|
          M.define (|
            [ "i" ],
            Value.Integer 0
          |),
          M.bin_op (|
            "<",
            M.get_name (| "i" |),
            Value.Integer 33
          |),
          M.un_op (|
            false,
            "++",
            M.get_name (| "i" |)
          |),
          let _ :=
            M.call (|
              M.member_access (|
                M.get_name (| "data" |),
                "push"
              |),
              [
                M.call (|
                  Ty.path "bytes1",
                  [
                    M.get_name (| "i" |)
                  ]
                |)
              ]
            |) in
          Value.Tuple []
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 58
src: 510:54:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 544:9:0declaration: 2sSlot: isOffset: suffix: slotalueSize: src: 533:1:0declaration: 34isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition test_pop (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        (* Beginning of a node! *)
id: 65
src: 633:53:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 663:9:0declaration: 2sSlot: isOffset: suffix: slotalueSize: 
evmVersion: cancun
 in
      let _ :=
        M.for_ (|
          M.define (|
            [ "i" ],
            Value.Integer 0
          |),
          M.bin_op (|
            "<",
            M.get_name (| "i" |),
            Value.Integer 32
          |),
          M.un_op (|
            false,
            "++",
            M.get_name (| "i" |)
          |),
          let _ :=
            M.call (|
              M.member_access (|
                M.get_name (| "data" |),
                "push"
              |),
              [
                M.call (|
                  Ty.path "bytes1",
                  [
                    M.get_name (| "i" |)
                  ]
                |)
              ]
            |) in
          Value.Tuple []
        |) in
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "data" |),
            "pop"
          |),
          []
        |) in
      let _ :=
        M.call (|
          M.member_access (|
            M.get_name (| "data" |),
            "pop"
          |),
          []
        |) in
      let _ :=
        (* Beginning of a node! *)
id: 97
src: 820:54:0
nodeType: InlineAssembly
AST: TODO YulJson
externalReferences: src: 854:9:0declaration: 2sSlot: isOffset: suffix: slotalueSize: src: 843:1:0declaration: 63isSlot: isOffset: alueSize: 
evmVersion: cancun
 in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End c.
