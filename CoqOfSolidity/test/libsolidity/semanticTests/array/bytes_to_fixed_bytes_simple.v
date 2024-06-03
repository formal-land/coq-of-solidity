(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition s : Value.t :=
    Value.String "abcdefghabcdefgh".

  Definition sLong : Value.t :=
    Value.String "abcdefghabcdefghabcdefghabcdefgh".

  Definition fromMemory (α : list Value.t) : M :=
    match α with
    | [m] =>
      let _ :=
        M.return_ (|
          M.call (|
            Ty.path "bytes16",
            [
              M.get_name (| "m" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition fromCalldata (α : list Value.t) : M :=
    match α with
    | [c] =>
      let _ :=
        M.return_ (|
          M.call (|
            Ty.path "bytes16",
            [
              M.get_name (| "c" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition fromStorage (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.call (|
            Ty.path "bytes16",
            [
              M.get_name (| "s" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition fromStorageLong (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.return_ (|
          M.call (|
            Ty.path "bytes32",
            [
              M.get_name (| "sLong" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition fromSlice (α : list Value.t) : M :=
    match α with
    | [c] =>
      let _ :=
        M.return_ (|
          M.call (|
            Ty.path "bytes8",
            [
              IndexRangeAccess M.get_name (| "c" |) Value.Integer 1 Value.Integer 9

            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
