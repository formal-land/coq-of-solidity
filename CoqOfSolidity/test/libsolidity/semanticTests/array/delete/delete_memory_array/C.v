(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
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
                  [Literal.string 0x435f33345f6465706c6f79656400000000000000000000000000000000000000]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string 0x435f33345f6465706c6f79656400000000000000000000000000000000000000]
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
                  [Literal.string 0x435f33345f6465706c6f79656400000000000000000000000000000000000000]
                ]
              |)
            ]
          |)
        |)
      )) in
      M.close_scope
    )) in
    M.close_scope.

  Module deployed.
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
          "abi_decode",
          ["headStart"; "dataEnd"],
          [],
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
                  [Literal.number 0]
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
          "abi_encode_uint256_to_uint256",
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
                    "cleanup_uint256",
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
          "abi_encode_uint256",
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
                "abi_encode_uint256_to_uint256",
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
          "external_fun_len",
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
            M.expr_stmt (|
              M.call (|
                "abi_decode",
                [
                  [Literal.number 4];
                  M.call (|
                    "calldatasize",
                    []
                  |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["ret"],
              Some (M.call (|
                "fun_len",
                []
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
                "abi_encode_uint256",
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
          "zero_value_for_split_uint256",
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
          "cleanup_t_rational_by_1",
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
          "convert_rational_2_by_1_to_uint256",
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
                        "cleanup_t_rational_by_1",
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
          "round_up_to_mul_of",
          ["value"],
          ["result"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["result"],
              Some (M.call (|
                "and",
                [
                  M.call (|
                    "add",
                    [
                      M.get_var (| "value" |);
                      [Literal.number 31]
                    ]
                  |);
                  M.call (|
                    "not",
                    [
                      [Literal.number 31]
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
          "panic_error_0x41",
          [],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 0];
                  M.call (|
                    "shl",
                    [
                      [Literal.number 224];
                      [Literal.number 0x4e487b71]
                    ]
                  |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 4];
                  [Literal.number 0x41]
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0x24]
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "finalize_allocation",
          ["memPtr"; "size"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["newFreePtr"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "memPtr" |);
                  M.call (|
                    "round_up_to_mul_of",
                    [
                      M.get_var (| "size" |)
                    ]
                  |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "or",
                [
                  M.call (|
                    "gt",
                    [
                      M.get_var (| "newFreePtr" |);
                      [Literal.number 0xffffffffffffffff]
                    ]
                  |);
                  M.call (|
                    "lt",
                    [
                      M.get_var (| "newFreePtr" |);
                      M.get_var (| "memPtr" |)
                    ]
                  |)
                ]
              |),
              do* M.open_scope in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "panic_error_0x41",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 64];
                  M.get_var (| "newFreePtr" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "allocate_memory",
          ["size"],
          ["memPtr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["memPtr"],
              Some (M.call (|
                "allocate_unbounded",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "finalize_allocation",
                [
                  M.get_var (| "memPtr" |);
                  M.get_var (| "size" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "array_allocation_size_array_uint256_dyn",
          ["length"],
          ["size"],
          do* M.open_scope in
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
                    "panic_error_0x41",
                    []
                  |)
                |)
              )) in
              M.close_scope
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["size"],
              Some (M.call (|
                "mul",
                [
                  M.get_var (| "length" |);
                  [Literal.number 0x20]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["size"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "size" |);
                  [Literal.number 0x20]
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "allocate_memory_array_array_uint256_dyn",
          ["length"],
          ["memPtr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["allocSize"],
              Some (M.call (|
                "array_allocation_size_array_uint256_dyn",
                [
                  M.get_var (| "length" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["memPtr"],
              Some (M.call (|
                "allocate_memory",
                [
                  M.get_var (| "allocSize" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  M.get_var (| "memPtr" |);
                  M.get_var (| "length" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "zero_memory_chunk_uint256",
          ["dataStart"; "dataSizeInBytes"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "calldatacopy",
                [
                  M.get_var (| "dataStart" |);
                  M.call (|
                    "calldatasize",
                    []
                  |);
                  M.get_var (| "dataSizeInBytes" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "allocate_and_zero_memory_array_array_uint256_dyn",
          ["length"],
          ["memPtr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["memPtr"],
              Some (M.call (|
                "allocate_memory_array_array_uint256_dyn",
                [
                  M.get_var (| "length" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["dataStart"],
              Some (M.get_var (| "memPtr" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["dataSize"],
              Some (M.call (|
                "array_allocation_size_array_uint256_dyn",
                [
                  M.get_var (| "length" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["dataStart"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "dataStart" |);
                  [Literal.number 32]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["dataSize"],
              Some (M.call (|
                "sub",
                [
                  M.get_var (| "dataSize" |);
                  [Literal.number 32]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "zero_memory_chunk_uint256",
                [
                  M.get_var (| "dataStart" |);
                  M.get_var (| "dataSize" |)
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "cleanup_rational_234_by",
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
          "convert_t_rational_by_to_t_uint256",
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
                        "cleanup_rational_234_by",
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
          "panic_error_0x32",
          [],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 0];
                  M.call (|
                    "shl",
                    [
                      [Literal.number 224];
                      [Literal.number 0x4e487b71]
                    ]
                  |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  [Literal.number 4];
                  [Literal.number 0x32]
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0x24]
                ]
              |)
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "array_length_array_uint256_dyn",
          ["value"],
          ["length"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["length"],
              Some (M.call (|
                "mload",
                [
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
          "memory_array_index_access_uint256_dyn",
          ["baseRef"; "index"],
          ["addr"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.if_ (|
              M.call (|
                "iszero",
                [
                  M.call (|
                    "lt",
                    [
                      M.get_var (| "index" |);
                      M.call (|
                        "array_length_array_uint256_dyn",
                        [
                          M.get_var (| "baseRef" |)
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
                    "panic_error_0x32",
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
                "mul",
                [
                  M.get_var (| "index" |);
                  [Literal.number 32]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["offset"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "offset" |);
                  [Literal.number 32]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["addr"],
              Some (M.call (|
                "add",
                [
                  M.get_var (| "baseRef" |);
                  M.get_var (| "offset" |)
                ]
              |))
            |)
          )) in
          M.close_scope
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "cleanup_rational_by_1",
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
          "convert_rational_0_by_1_to_uint256",
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
                        "cleanup_rational_by_1",
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
          "write_to_memory_uint256",
          ["memPtr"; "value"],
          [],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "mstore",
                [
                  M.get_var (| "memPtr" |);
                  M.call (|
                    "cleanup_uint256",
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
          "cleanup_t_rational_by",
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
          "convert_rational_1_by_1_to_uint256",
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
                        "cleanup_t_rational_by",
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
          "zero_value_for_split_array_uint256_dyn",
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
          "fun_len",
          [],
          ["var_ret"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["zero_uint256"],
              Some (M.call (|
                "zero_value_for_split_uint256",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_ret"],
              Some (M.get_var (| "zero_uint256" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr"],
              Some ([Literal.number 0x02])
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_1"],
              Some (M.call (|
                "convert_rational_2_by_1_to_uint256",
                [
                  M.get_var (| "expr" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_14_mpos"],
              Some (M.call (|
                "allocate_and_zero_memory_array_array_uint256_dyn",
                [
                  M.get_var (| "_1" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["var_data_mpos"],
              Some (M.get_var (| "expr_14_mpos" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_1"],
              Some ([Literal.number 0xea])
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_2"],
              Some (M.call (|
                "convert_t_rational_by_to_t_uint256",
                [
                  M.get_var (| "expr_1" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_4_mpos"],
              Some (M.get_var (| "var_data_mpos" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_16_mpos"],
              Some (M.get_var (| "_4_mpos" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_2"],
              Some ([Literal.number 0x00])
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_3"],
              Some (M.get_var (| "_2" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "write_to_memory_uint256",
                [
                  M.call (|
                    "memory_array_index_access_uint256_dyn",
                    [
                      M.get_var (| "expr_16_mpos" |);
                      M.call (|
                        "convert_rational_0_by_1_to_uint256",
                        [
                          M.get_var (| "expr_2" |)
                        ]
                      |)
                    ]
                  |);
                  M.get_var (| "_3" |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_3"],
              Some ([Literal.number 0x7b])
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_4"],
              Some (M.call (|
                "convert_rational_by_to_uint256",
                [
                  M.get_var (| "expr_3" |)
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_mpos"],
              Some (M.get_var (| "var_data_mpos" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_mpos"],
              Some (M.get_var (| "_mpos" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr_4"],
              Some ([Literal.number 0x01])
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_5"],
              Some (M.get_var (| "_4" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.expr_stmt (|
              M.call (|
                "write_to_memory_uint256",
                [
                  M.call (|
                    "memory_array_index_access_uint256_dyn",
                    [
                      M.get_var (| "expr_mpos" |);
                      M.call (|
                        "convert_rational_1_by_1_to_uint256",
                        [
                          M.get_var (| "expr_4" |)
                        ]
                      |)
                    ]
                  |);
                  M.get_var (| "_5" |)
                ]
              |)
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_9_mpos"],
              Some (M.call (|
                "zero_value_for_split_array_uint256_dyn",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_data_mpos"],
              Some (M.get_var (| "_9_mpos" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_ret"],
              Some (M.call (|
                "mload",
                [
                  M.get_var (| "var_data_mpos" |)
                ]
              |))
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
                [Literal.number 128]
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
                    Some (Literal.number 0x56d88e27),
                    do* M.open_scope in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "external_fun_len",
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
      "a2646970667358221220eecafb69397e051409085a54df5895352ece99409a170ac22932b46f4bb4406364736f6c634300081b0033".
  End deployed.
End C.
