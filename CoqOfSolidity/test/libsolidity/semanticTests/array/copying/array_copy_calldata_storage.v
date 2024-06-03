(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module c.
  Definition m_data : Value.t :=
    undefined.

  Definition m_data_dyn : Value.t :=
    undefined.

  Definition m_byte_data : Value.t :=
    undefined.

  Definition store (α : list Value.t) : M :=
    match α with
    | [a, b] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "m_data" |),
          M.get_name (| "a" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "m_data_dyn" |),
          M.get_name (| "a" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "m_byte_data" |),
          M.get_name (| "b" |)
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.index_access (|
              M.get_name (| "b" |),
              Some (Value.Integer 3)
            |),
            Some (Value.Integer 1)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition retrieve (α : list Value.t) : M :=
    match α with
    | [] =>
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "a" |),
          M.member_access (|
            M.get_name (| "m_data" |),
            "length"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "b" |),
          M.index_access (|
            M.get_name (| "m_data" |),
            Some (Value.Integer 7)
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "c" |),
          M.member_access (|
            M.get_name (| "m_data_dyn" |),
            "length"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "d" |),
          M.index_access (|
            M.get_name (| "m_data_dyn" |),
            Some (Value.Integer 7)
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "e" |),
          M.member_access (|
            M.get_name (| "m_byte_data" |),
            "length"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "f" |),
          M.member_access (|
            M.index_access (|
              M.get_name (| "m_byte_data" |),
              Some (Value.Integer 3)
            |),
            "length"
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.get_name (| "g" |),
          M.index_access (|
            M.index_access (|
              M.get_name (| "m_byte_data" |),
              Some (Value.Integer 3)
            |),
            Some (Value.Integer 1)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End c.
