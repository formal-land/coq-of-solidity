(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_17.
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
                  [Literal.string "435f31375f6465706c6f79656400000000000000000000000000000000000000"]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string "435f31375f6465706c6f79656400000000000000000000000000000000000000"]
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
                  [Literal.string "435f31375f6465706c6f79656400000000000000000000000000000000000000"]
                ]
              |)
            ]
          |)
        |)
      )) in
      M.close_scope
    )) in
    M.close_scope.

  Module C_17_deployed.
    Definition code : M.t BlockUnit.t :=
      do* M.open_scope in
      do* ltac:(M.monadic (
        M.function (|
          "shift_right_unsigned",
          ["value"],
          ["newValue"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["newValue"],
              Some (M.call (|
                "shr",
                [
                  [Literal.number 224];
                  M.get_var (| "value" |)
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
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
        M.function (|
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
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
          "cleanup_bool",
          ["value"],
          ["cleaned"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["cleaned"],
              Some (M.call (|
                "iszero",
                [
                  M.call (|
                    "iszero",
                    [
                      M.get_var (| "value" |)
                    ]
                  |)
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "validator_revert_bool",
          ["value"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "iszero",
                [
                  M.call (|
                    "eq",
                    [
                      M.get_var (| "value" |);
                      M.call (|
                        "cleanup_bool",
                        [
                          M.get_var (| "value" |)
                        ]
                      |)
                    ]
                  |)
                ]
              |),
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
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "abi_decode_t_bool",
          ["offset"; "end"],
          ["value"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["value"],
              Some (M.call (|
                "calldataload",
                [
                  M.get_var (| "offset" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "validator_revert_bool",
                [
                  M.get_var (| "value" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "abi_decode_bool",
          ["headStart"; "dataEnd"],
          ["value0"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "slt",
                [
                  M.call (|
                    "sub",
                    [
                      M.get_var (| "dataEnd" |);
                      M.get_var (| "headStart" |)
                    ]
                  |);
                  [Literal.number 32]
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["offset"],
              Some ([Literal.number 0])
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["value0"],
              Some (M.call (|
                "abi_decode_t_bool",
                [
                  M.call (|
                    "add",
                    [
                      M.get_var (| "headStart" |);
                      M.get_var (| "offset" |)
                    ]
                  |);
                  M.get_var (| "dataEnd" |)
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "abi_encode_bool_to_bool",
          ["value"; "pos"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  M.get_var (| "pos" |);
                  M.call (|
                    "cleanup_bool",
                    [
                      M.get_var (| "value" |)
                    ]
                  |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "abi_encode_bool",
          ["headStart"; "value0"],
          ["tail"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["tail"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "headStart" |);
                  [Literal.number 32]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "abi_encode_bool_to_bool",
                [
                  M.get_var (| "value0" |);
                  M.call (|
                    "add",
                    [
                      M.get_var (| "headStart" |);
                      [Literal.number 0]
                    ]
                  |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "external_fun_f",
          [],
          [],
          do* M.open_scope in
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
              ["param"],
              Some (M.call (|
                "abi_decode_bool",
                [
                  [Literal.number 4];
                  M.call (|
                    "calldatasize",
                    []
                  |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["ret"],
              Some (M.call (|
                "fun_f",
                [
                  M.get_var (| "param" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["memPos"],
              Some (M.call (|
                "allocate_unbounded",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["memEnd"],
              Some (M.call (|
                "abi_encode_bool",
                [
                  M.get_var (| "memPos" |);
                  M.get_var (| "ret" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "return",
                [
                  M.get_var (| "memPos" |);
                  M.call (|
                    "sub",
                    [
                      M.get_var (| "memEnd" |);
                      M.get_var (| "memPos" |)
                    ]
                  |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
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
          "zero_value_for_split_bool",
          [],
          ["ret"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["ret"],
              Some ([Literal.number 0])
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "fun_f",
          ["var_a"],
          ["var_x"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["zero_bool"],
              Some (M.call (|
                "zero_value_for_split_bool",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_x"],
              Some (M.get_var (| "zero_bool" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_1"],
              Some (M.get_var (| "var_a" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr"],
              Some (M.get_var (| "_1" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_b"],
              Some (M.get_var (| "expr" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_2"],
              Some (M.get_var (| "var_b" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_1"],
              Some (M.get_var (| "_2" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_x"],
              Some (M.get_var (| "expr_1" |))
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
              "iszero",
              [
                M.call (|
                  "lt",
                  [
                    M.call (|
                      "calldatasize",
                      []
                    |);
                    [Literal.number 4]
                  ]
                |)
              ]
            |),
            do* M.open_scope in
            do* ltac:(M.monadic (
              M.declare (|
                ["selector"],
                Some (M.call (|
                  "shift_right_unsigned",
                  [
                    M.call (|
                      "calldataload",
                      [
                        [Literal.number 0]
                      ]
                    |)
                  ]
                |))
              |)
            )) in
            do* ltac:(M.monadic (
              M.switch (|
                M.get_var (| "selector" |),
                [
                  (
                    Some (Literal.number 0x98c3a6c1),
                    do* M.open_scope in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "external_fun_f",
                          []
                        |)
                      |)
                    )) in
                    M.close_scope
                  );
                  (
                    None,
                    do* M.open_scope in
                    M.close_scope
                  )          ]
              |)
            )) in
            M.close_scope
          |)
        )) in
        do* ltac:(M.monadic (
          M.expr_stmt (|
            M.call (|
              "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
              []
            |)
          |)
        )) in
        M.close_scope
      )) in
      M.close_scope.

    Definition data : string :=
      "a26469706673582212202d385bba19c01ab10a033ca02e92e670cc7354a9cc20477206479d8b40cb752b64736f6c634300081b0033".
  End C_17_deployed.
End C_17.
