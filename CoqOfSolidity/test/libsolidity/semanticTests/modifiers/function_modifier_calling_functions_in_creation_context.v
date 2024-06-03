(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module A.
  Definition data : Value.t :=
    undefined.

  Definition  (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.call (|
          M.get_name (| "f1" |),
          []
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f1 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "|=",
          M.get_name (| "data" |),
          Value.Integer 0x1
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f2 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "|=",
          M.get_name (| "data" |),
          Value.Integer 0x20
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f3 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
         in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  (* Beginning of a node! *)
id: 40
src: 235:54:0
nodeType: ModifierDefinition
name: mod1
nameLocation: 244:4:0
documentation: 
visibility: internal
parameters: ParameterList.make []
virtual: 1
overrides: 
body: let _ :=
    M.call (|
      M.get_name (| "f2" |),
      []
    |) in
  let _ :=
    (* Beginning of a node! *)
id: 38
src: 281:1:0
nodeType: PlaceholderStatement
 in
  Value.Tuple []


  (* Beginning of a node! *)
id: 49
src: 294:57:0
nodeType: ModifierDefinition
name: mod2
nameLocation: 303:4:0
documentation: 
visibility: internal
parameters: ParameterList.make []
virtual: 0
overrides: 
body: let _ :=
    M.call (|
      M.get_name (| "f3" |),
      []
    |) in
  let _ :=
    if Value.Bool false then
      (* Beginning of a node! *)
id: 46
src: 343:1:0
nodeType: PlaceholderStatement

    else
      Value.Tuple [] in
  Value.Tuple []


  Definition getData (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.get_name (| "data" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End A.


(* Contract *)
Module C.
  (* Beginning of a node! *)
id: 68
src: 458:55:0
nodeType: ModifierDefinition
name: mod1
nameLocation: 467:4:0
documentation: 
visibility: internal
parameters: ParameterList.make []
virtual: 0
overrides: OverrideSpecifier.make []
body: let _ :=
    M.call (|
      M.get_name (| "f4" |),
      []
    |) in
  let _ :=
    (* Beginning of a node! *)
id: 66
src: 505:1:0
nodeType: PlaceholderStatement
 in
  Value.Tuple []
baseModifiers: [nput files for --]


  Definition f3 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "|=",
          M.get_name (| "data" |),
          Value.Integer 0x300
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition f4 (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "|=",
          M.get_name (| "data" |),
          Value.Integer 0x4000
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
