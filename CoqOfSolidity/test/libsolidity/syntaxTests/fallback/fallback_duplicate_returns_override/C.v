(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_9.
  Definition code : M.t BlockUnit.t :=
    do* M.open_scope in
    do* ltac:(M.monadic (
      M.function (|
        "allocate_unbounded",
        [],
        ["memPtr"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["memPtr"],
            Some (M.call (|
              "mload",
              [
                [Literal.number 64]
              ]
            |))
          |)
        )) in
        M.close_scope
      |)
    )) in
    do* ltac:(M.monadic (
      M.function (|
        "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
        [],
        [],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.expr_stmt (|
            M.call (|
              "revert",
              [
                [Literal.number 0];
                [Literal.number 0]
              ]
            |)
          |)
        )) in
        M.close_scope
      |)
    )) in
    do* ltac:(M.monadic (
      do* M.open_scope in
      do* ltac:(M.monadic (
        M.expr_stmt (|
          M.call (|
            "mstore",
            [
              [Literal.number 64];
              M.call (|
                "memoryguard",
                [
                  [Literal.number 0x80]
                ]
              |)
            ]
          |)
        |)
      )) in
      do* ltac:(M.monadic (
        M.if_ (|
          M.call (|
            "callvalue",
            []
          |),
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                []
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.declare (|
          ["_1"],
          Some (M.call (|
            "allocate_unbounded",
            []
          |))
        |)
      )) in
      do* ltac:(M.monadic (
        M.expr_stmt (|
          M.call (|
            "codecopy",
            [
              M.get_var (| "_1" |);
              M.call (|
                "dataoffset",
                [
                  [Literal.string "435f395f6465706c6f7965640000000000000000000000000000000000000000"]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string "435f395f6465706c6f7965640000000000000000000000000000000000000000"]
                ]
              |)
            ]
          |)
        |)
      )) in
      do* ltac:(M.monadic (
        M.expr_stmt (|
          M.call (|
            "return",
            [
              M.get_var (| "_1" |);
              M.call (|
                "datasize",
                [
                  [Literal.string "435f395f6465706c6f7965640000000000000000000000000000000000000000"]
                ]
              |)
            ]
          |)
        |)
      )) in
      M.close_scope
    )) in
    M.close_scope.

  Module C_9_deployed.
    Definition code : M.t BlockUnit.t :=
      do* M.open_scope in
      do* ltac:(M.monadic (
        M.function (|
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
          [],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0]
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "zero_value_for_split_bytes",
          [],
          ["ret"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["ret"],
              Some ([Literal.number 96])
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "fun",
          ["var_input_offset"; "var_input_length"],
          ["var_output_mpos"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["zero_bytes_mpos"],
              Some (M.call (|
                "zero_value_for_split_bytes",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_output_mpos"],
              Some (M.get_var (| "zero_bytes_mpos" |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.expr_stmt (|
            M.call (|
              "mstore",
              [
                [Literal.number 64];
                M.call (|
                  "memoryguard",
                  [
                    [Literal.number 0x80]
                  ]
                |)
              ]
            |)
          |)
        )) in
        do* ltac:(M.monadic (
          M.if_ (|
            M.call (|
              "callvalue",
              []
            |),
            do* M.open_scope in
            do* ltac:(M.monadic (
              M.expr_stmt (|
                M.call (|
                  "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                  []
                |)
              |)
            )) in
            M.close_scope
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["retval"],
            Some (M.call (|
              "fun",
              [
                [Literal.number 0];
                M.call (|
                  "calldatasize",
                  []
                |)
              ]
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.expr_stmt (|
            M.call (|
              "return",
              [
                M.call (|
                  "add",
                  [
                    M.get_var (| "retval" |);
                    [Literal.number 0x20]
                  ]
                |);
                M.call (|
                  "mload",
                  [
                    M.get_var (| "retval" |)
                  ]
                |)
              ]
            |)
          |)
        )) in
        M.close_scope
      )) in
      M.close_scope.

    Definition data : string :=
      "a2646970667358221220a3a39ecc4cc8eef70e7443da4c0f0238b65c90a9d4f82ec92513829d9ae76dd264736f6c634300081b0033".
  End C_9_deployed.
End C_9.
