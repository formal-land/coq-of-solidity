(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition name : string := "C_23".

  Definition code : M.t BlockUnit.t :=
    M.scope (
      do* ltac:(M.monadic (
        M.function (|
          "allocate_unbounded",
          [],
          ["memPtr"],
          M.scope (
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
            M.pure BlockUnit.Tt
          )
        |)
      )) in
      do* ltac:(M.monadic (
        M.function (|
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
          [],
          [],
          M.scope (
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
            M.pure BlockUnit.Tt
          )
        |)
      )) in
      do* ltac:(M.monadic (
        M.scope (
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
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                      []
                    |)
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
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
                      [Literal.string 0x435f32335f6465706c6f79656400000000000000000000000000000000000000]
                    ]
                  |);
                  M.call (|
                    "datasize",
                    [
                      [Literal.string 0x435f32335f6465706c6f79656400000000000000000000000000000000000000]
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
                      [Literal.string 0x435f32335f6465706c6f79656400000000000000000000000000000000000000]
                    ]
                  |)
                ]
              |)
            |)
          )) in
          M.pure BlockUnit.Tt
        )
      )) in
      M.pure BlockUnit.Tt
    ).

  Module deployed.
    Definition name : string := "C_23_deployed".

    Definition code : M.t BlockUnit.t :=
      M.scope (
        do* ltac:(M.monadic (
          M.function (|
            "shift_right_unsigned",
            ["value"],
            ["newValue"],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "allocate_unbounded",
            [],
            ["memPtr"],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "abi_decode_array_uint256_dyn_calldata",
            ["offset"; "end"],
            ["arrayPos"; "length"],
            M.scope (
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
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
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
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
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
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "cleanup_uint256",
            ["value"],
            ["cleaned"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["cleaned"],
                  Some (M.get_var (| "value" |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "validator_revert_uint256",
            ["value"],
            [],
            M.scope (
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
                            "cleanup_uint256",
                            [
                              M.get_var (| "value" |)
                            ]
                          |)
                        ]
                      |)
                    ]
                  |),
                  M.scope (
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
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "abi_decode_uint256",
            ["offset"; "end"],
            ["value"],
            M.scope (
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
                    "validator_revert_uint256",
                    [
                      M.get_var (| "value" |)
                    ]
                  |)
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_uint256",
            ["headStart"; "dataEnd"],
            ["value0"; "value1"; "value2"; "value3"; "value4"],
            M.scope (
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
                      [Literal.number 96]
                    ]
                  |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
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
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
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
              do* ltac:(M.monadic (
                M.declare (|
                  ["offset_1"],
                  Some (M.call (|
                    "calldataload",
                    [
                      M.call (|
                        "add",
                        [
                          M.get_var (| "headStart" |);
                          [Literal.number 32]
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
                      M.get_var (| "offset_1" |);
                      [Literal.number 0xffffffffffffffff]
                    ]
                  |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["value2"; "value3"],
                  Some (M.call (|
                    "abi_decode_array_uint256_dyn_calldata",
                    [
                      M.call (|
                        "add",
                        [
                          M.get_var (| "headStart" |);
                          M.get_var (| "offset_1" |)
                        ]
                      |);
                      M.get_var (| "dataEnd" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["offset_2"],
                  Some ([Literal.number 64])
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["value4"],
                  Some (M.call (|
                    "abi_decode_uint256",
                    [
                      M.call (|
                        "add",
                        [
                          M.get_var (| "headStart" |);
                          M.get_var (| "offset_2" |)
                        ]
                      |);
                      M.get_var (| "dataEnd" |)
                    ]
                  |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "abi_encode_uint256_to_uint256",
            ["value"; "pos"],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "abi_encode_uint256",
            ["headStart"; "value0"],
            ["tail"],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "external_fun_f",
            [],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.if_ (|
                  M.call (|
                    "callvalue",
                    []
                  |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["param"; "param_1"; "param_2"; "param_3"; "param_4"],
                  Some (M.call (|
                    "abi_decode_array_uint256_dyn_calldatat_array_uint256_dyn_calldatat_uint256",
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
                      M.get_var (| "param" |);
                      M.get_var (| "param_1" |);
                      M.get_var (| "param_2" |);
                      M.get_var (| "param_3" |);
                      M.get_var (| "param_4" |)
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "zero_value_for_split_uint256",
            [],
            ["ret"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["ret"],
                  Some ([Literal.number 0])
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "panic_error_0x32",
            [],
            [],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "calldata_array_index_access_uint256_dyn_calldata",
            ["base_ref"; "length"; "index"],
            ["addr"],
            M.scope (
              do* ltac:(M.monadic (
                M.if_ (|
                  M.call (|
                    "iszero",
                    [
                      M.call (|
                        "lt",
                        [
                          M.get_var (| "index" |);
                          M.get_var (| "length" |)
                        ]
                      |)
                    ]
                  |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "panic_error_0x32",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["addr"],
                  Some (M.call (|
                    "add",
                    [
                      M.get_var (| "base_ref" |);
                      M.call (|
                        "mul",
                        [
                          M.get_var (| "index" |);
                          [Literal.number 32]
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "read_from_calldatat_uint256",
            ["ptr"],
            ["returnValue"],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["value"],
                  Some (M.call (|
                    "calldataload",
                    [
                      M.get_var (| "ptr" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "validator_revert_uint256",
                    [
                      M.get_var (| "value" |)
                    ]
                  |)
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["returnValue"],
                  Some (M.get_var (| "value" |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "fun_f",
            ["var_x_offset"; "var_x_length"; "var_y_offset"; "var_y_length"; "var_i"],
            ["var"],
            M.scope (
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
                  ["var"],
                  Some (M.get_var (| "zero_uint256" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_2_offset"],
                  Some (M.get_var (| "var_y_offset" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_length"],
                  Some (M.get_var (| "var_y_length" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_offset"],
                  Some (M.get_var (| "_2_offset" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_length"],
                  Some (M.get_var (| "_length" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_x_offset"],
                  Some (M.get_var (| "expr_offset" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_x_length"],
                  Some (M.get_var (| "expr_length" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_offset"],
                  Some (M.get_var (| "var_x_offset" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_4_length"],
                  Some (M.get_var (| "var_x_length" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_17_offset"],
                  Some (M.get_var (| "_offset" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_17_length"],
                  Some (M.get_var (| "_4_length" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_1"],
                  Some (M.get_var (| "var_i" |))
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
                  ["expr_1"],
                  Some (M.call (|
                    "read_from_calldatat_uint256",
                    [
                      M.call (|
                        "calldata_array_index_access_uint256_dyn_calldata",
                        [
                          M.get_var (| "expr_17_offset" |);
                          M.get_var (| "expr_17_length" |);
                          M.get_var (| "expr" |)
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var"],
                  Some (M.get_var (| "expr_1" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.leave (||)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.scope (
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
                M.scope (
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
                          Some (Literal.number 0x76953590),
                          M.scope (
                            do* ltac:(M.monadic (
                              M.expr_stmt (|
                                M.call (|
                                  "external_fun_f",
                                  []
                                |)
                              |)
                            )) in
                            M.pure BlockUnit.Tt
                          )
                        );
                        (
                          None,
                          M.scope (
                            M.pure BlockUnit.Tt
                          )
                        )
                      ]
                    |)
                  )) in
                  M.pure BlockUnit.Tt
                )
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
            M.pure BlockUnit.Tt
          )
        )) in
        M.pure BlockUnit.Tt
      ).

    Definition data : string :=
      "a2646970667358221220586c3926ed264d703b272675201b50988ffc42aca09ee09bac4cb186b4b6755264736f6c634300081b0033".
  End deployed.
End C.
