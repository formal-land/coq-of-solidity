(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module A_37.
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
                  [Literal.string "415f33375f6465706c6f79656400000000000000000000000000000000000000"]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string "415f33375f6465706c6f79656400000000000000000000000000000000000000"]
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
                  [Literal.string "415f33375f6465706c6f79656400000000000000000000000000000000000000"]
                ]
              |)
            ]
          |)
        |)
      )) in
      M.close_scope
    )) in
    M.close_scope.

  Module A_37_deployed.
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
          "revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db",
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
          "revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d",
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
          "revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490",
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
          "revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef",
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
          "abi_decode_array_uint256_dyn_calldata",
          ["offset"; "end"],
          ["arrayPos";
      "length"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "iszero",
                [
                  M.call (|
                    "slt",
                    [
                      M.call (|
                        "add",
                        [
                          M.get_var (| "offset" |);
                          [Literal.number 0x1f]
                        ]
                      |);
                      M.get_var (| "end" |)
                    ]
                  |)
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["length"],
              Some (M.call (|
                "calldataload",
                [
                  M.get_var (| "offset" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.get_var (| "length" |);
                  [Literal.number 0xffffffffffffffff]
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["arrayPos"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "offset" |);
                  [Literal.number 0x20]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.call (|
                    "add",
                    [
                      M.get_var (| "arrayPos" |);
                      M.call (|
                        "mul",
                        [
                          M.get_var (| "length" |);
                          [Literal.number 0x20]
                        ]
                      |)
                    ]
                  |);
                  M.get_var (| "end" |)
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef",
                    []
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
          "abi_decode_array_uint256_dyn_calldata_ptr",
          ["headStart"; "dataEnd"],
          ["value0";
      "value1"],
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
              Some (M.call (|
                "calldataload",
                [
                  M.call (|
                    "add",
                    [
                      M.get_var (| "headStart" |);
                      [Literal.number 0]
                    ]
                  |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.get_var (| "offset" |);
                  [Literal.number 0xffffffffffffffff]
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["value0"; "value1"],
              Some (M.call (|
                "abi_decode_array_uint256_dyn_calldata",
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
          "abi_encode_tuple",
          ["headStart"],
          ["tail"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["tail"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "headStart" |);
                  [Literal.number 0]
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "external_fun_i",
          [],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["param"; "param_1"],
              Some (M.call (|
                "abi_decode_array_uint256_dyn_calldata_ptr",
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
                "abi_encode_tuple",
                [
                  M.get_var (| "memPos" |)
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
          "external_fun_h",
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
              ["param"; "param_1"],
              Some (M.call (|
                "abi_decode_array_uint256_dyn_calldata_ptr",
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
            M.expr_stmt (|
              M.call (|
                "fun_h",
                [
                  M.get_var (| "param" |);
                  M.get_var (| "param_1" |)
                ]
              |)
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
                "abi_encode_tuple",
                [
                  M.get_var (| "memPos" |)
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
              ["param"; "param_1"],
              Some (M.call (|
                "abi_decode_array_uint256_dyn_calldata_ptr",
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
                "abi_encode_tuple",
                [
                  M.get_var (| "memPos" |)
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
          "external_fun_g",
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
              ["param"; "param_1"],
              Some (M.call (|
                "abi_decode_array_uint256_dyn_calldata_ptr",
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
                "abi_encode_tuple",
                [
                  M.get_var (| "memPos" |)
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
          "cleanup_rational_by",
          ["value"],
          ["cleaned"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["cleaned"],
              Some (M.get_var (| "value" |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "cleanup_uint256",
          ["value"],
          ["cleaned"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["cleaned"],
              Some (M.get_var (| "value" |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "identity",
          ["value"],
          ["ret"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["ret"],
              Some (M.get_var (| "value" |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "convert_rational_by_to_uint256",
          ["value"],
          ["converted"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["converted"],
              Some (M.call (|
                "cleanup_uint256",
                [
                  M.call (|
                    "identity",
                    [
                      M.call (|
                        "cleanup_rational_by",
                        [
                          M.get_var (| "value" |)
                        ]
                      |)
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
          "shift_left",
          ["value"],
          ["newValue"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["newValue"],
              Some (M.call (|
                "shl",
                [
                  [Literal.number 0];
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
          "update_byte_slice_shift",
          ["value"; "toInsert"],
          ["result"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["mask"],
              Some (M.call (|
                "not",
                [
                  [Literal.number 0]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["toInsert"],
              Some (M.call (|
                "shift_left",
                [
                  M.get_var (| "toInsert" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["value"],
              Some (M.call (|
                "and",
                [
                  M.get_var (| "value" |);
                  M.call (|
                    "not",
                    [
                      M.get_var (| "mask" |)
                    ]
                  |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["result"],
              Some (M.call (|
                "or",
                [
                  M.get_var (| "value" |);
                  M.call (|
                    "and",
                    [
                      M.get_var (| "toInsert" |);
                      M.get_var (| "mask" |)
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
          "convert_uint256_to_uint256",
          ["value"],
          ["converted"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["converted"],
              Some (M.call (|
                "cleanup_uint256",
                [
                  M.call (|
                    "identity",
                    [
                      M.call (|
                        "cleanup_uint256",
                        [
                          M.get_var (| "value" |)
                        ]
                      |)
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
          "prepare_store_uint256",
          ["value"],
          ["ret"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["ret"],
              Some (M.get_var (| "value" |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "update_storage_value_offsett_uint256_to_uint256",
          ["slot"; "value"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["convertedValue"],
              Some (M.call (|
                "convert_uint256_to_uint256",
                [
                  M.get_var (| "value" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "sstore",
                [
                  M.get_var (| "slot" |);
                  M.call (|
                    "update_byte_slice_shift",
                    [
                      M.call (|
                        "sload",
                        [
                          M.get_var (| "slot" |)
                        ]
                      |);
                      M.call (|
                        "prepare_store_uint256",
                        [
                          M.get_var (| "convertedValue" |)
                        ]
                      |)
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
          "fun_h",
          ["var_offset"; "var_length"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr"],
              Some ([Literal.number 0x2a])
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_1"],
              Some (M.call (|
                "convert_rational_by_to_uint256",
                [
                  M.get_var (| "expr" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "update_storage_value_offsett_uint256_to_uint256",
                [
                  [Literal.number 0x00];
                  M.get_var (| "_1" |)
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
                    Some (Literal.number 0x01d0e2b5),
                    do* M.open_scope in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "external_fun_i",
                          []
                        |)
                      |)
                    )) in
                    M.close_scope
                  );
                  (
                    Some (Literal.number 0x40dcbb08),
                    do* M.open_scope in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "external_fun_h",
                          []
                        |)
                      |)
                    )) in
                    M.close_scope
                  );
                  (
                    Some (Literal.number 0x7bc5bbbf),
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
                    Some (Literal.number 0xbaf71609),
                    do* M.open_scope in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "external_fun_g",
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
      "a2646970667358221220d4145c16bcf6768080dd629225a85ddced2cc04e48629d98b09c3925e56645f664736f6c634300081b0033".
  End A_37_deployed.
End A_37.
