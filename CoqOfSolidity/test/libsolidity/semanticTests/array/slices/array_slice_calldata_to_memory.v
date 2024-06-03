(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

(* Contract *)
Module C.
  Definition f (α : list Value.t) : M :=
    match α with
    | [b, start, end] =>
      let _ :=
        M.define (|
          [ "m" ],
          IndexRangeAccess M.get_name (| "b" |) M.get_name (| "start" |) M.get_name (| "end" |)

        |) in
      let _ :=
        M.define (|
          [ "len" ],
          M.bin_op (|
            "-",
            M.get_name (| "end" |),
            M.get_name (| "start" |)
          |)
        |) in
      let _ :=
        M.call (|
          M.get_name (| "assert" |),
          [
            M.bin_op (|
              "==",
              M.get_name (| "len" |),
              M.member_access (|
                M.get_name (| "m" |),
                "length"
              |)
            |)
          ]
        |) in
      let _ :=
        M.for_ (|
          M.define (|
            [ "i" ],
            Value.Integer 0
          |),
          M.bin_op (|
            "<",
            M.get_name (| "i" |),
            M.get_name (| "len" |)
          |),
          M.un_op (|
            false,
            "++",
            M.get_name (| "i" |)
          |),
          let _ :=
            M.call (|
              M.get_name (| "assert" |),
              [
                M.bin_op (|
                  "==",
                  M.index_access (|
                    IndexRangeAccess M.get_name (| "b" |) M.get_name (| "start" |) M.get_name (| "end" |)
,
                    Some (M.get_name (| "i" |))
                  |),
                  M.index_access (|
                    M.get_name (| "m" |),
                    Some (M.get_name (| "i" |))
                  |)
                |)
              ]
            |) in
          Value.Tuple []
        |) in
      let _ :=
        M.return_ (|
          M.index_access (|
            M.index_access (|
              Value.Array [
                IndexRangeAccess M.get_name (| "b" |) M.get_name (| "start" |) M.get_name (| "end" |)

              ],
              Some (Value.Integer 0)
            |),
            Some (Value.Integer 0)
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition g (α : list Value.t) : M :=
    match α with
    | [b, start, end] =>
      let _ :=
        M.return_ (|
          IndexRangeAccess M.get_name (| "b" |) M.get_name (| "start" |) M.get_name (| "end" |)

        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h1 (α : list Value.t) : M :=
    match α with
    | [b] =>
      let _ :=
        M.return_ (|
          M.get_name (| "b" |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.

  Definition h (α : list Value.t) : M :=
    match α with
    | [b, start, end] =>
      let _ :=
        M.return_ (|
          M.call (|
            M.get_name (| "h1" |),
            [
              IndexRangeAccess M.get_name (| "b" |) M.get_name (| "start" |) M.get_name (| "end" |)

            ]
          |)
        |) in
      Value.Tuple []
    | _ => M.impossible "invalid number of parameters"
    end.
End C.
