(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module test.
  Definition a : Value.t :=
    undefined.

  Definition b : Value.t :=
    undefined.

  Definition set_internal (α : list Value.t) : M :=
    match α with
    | [m, key, value1, value2] =>
      let _ :=
        M.define (|
          [ "oldValue1" ],
          M.index_access (|
            M.index_access (|
              M.get_name (| "m" |),
              Some (Value.Integer 0)
            |),
            Some (M.get_name (| "key" |))
          |)
        |) in
      let _ :=
        M.define (|
          [ "oldValue2" ],
          M.index_access (|
            M.index_access (|
              M.get_name (| "m" |),
              Some (Value.Integer 1)
            |),
            Some (M.get_name (| "key" |))
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.index_access (|
              M.get_name (| "m" |),
              Some (Value.Integer 0)
            |),
            Some (M.get_name (| "key" |))
          |),
          M.get_name (| "value1" |)
        |) in
      let _ :=
        M.assign (|
          "=",
          M.index_access (|
            M.index_access (|
              M.get_name (| "m" |),
              Some (Value.Integer 1)
            |),
            Some (M.get_name (| "key" |))
          |),
          M.get_name (| "value2" |)
        |) in
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.get_name (| "oldValue1" |),
            M.get_name (| "oldValue2" |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition set (α : list Value.t) : M :=
    match α with
    | [key, value_a1, value_a2, value_b1, value_b2] =>
      let _ :=
        M.assign (|
          "=",
          Value.Tuple [
            M.get_name (| "old_a1" |),
            M.get_name (| "old_a2" |)
          ],
          M.call (|
            M.get_name (| "set_internal" |),
            [
              M.get_name (| "a" |),
              M.get_name (| "key" |),
              M.get_name (| "value_a1" |),
              M.get_name (| "value_a2" |)
            ]
          |)
        |) in
      let _ :=
        M.assign (|
          "=",
          Value.Tuple [
            M.get_name (| "old_b1" |),
            M.get_name (| "old_b2" |)
          ],
          M.call (|
            M.get_name (| "set_internal" |),
            [
              M.get_name (| "b" |),
              M.get_name (| "key" |),
              M.get_name (| "value_b1" |),
              M.get_name (| "value_b2" |)
            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition get (α : list Value.t) : M :=
    match α with
    | [key] =>
      let _ :=
        M.return_ (|
          Value.Tuple [
            M.index_access (|
              M.index_access (|
                M.get_name (| "a" |),
                Some (Value.Integer 0)
              |),
              Some (M.get_name (| "key" |))
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "a" |),
                Some (Value.Integer 1)
              |),
              Some (M.get_name (| "key" |))
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "b" |),
                Some (Value.Integer 0)
              |),
              Some (M.get_name (| "key" |))
            |),
            M.index_access (|
              M.index_access (|
                M.get_name (| "b" |),
                Some (Value.Integer 1)
              |),
              Some (M.get_name (| "key" |))
            |)
          ]
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End test.
