(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition name : string := "C_31".

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
                      [Literal.string 0x435f33315f6465706c6f79656400000000000000000000000000000000000000]
                    ]
                  |);
                  M.call (|
                    "datasize",
                    [
                      [Literal.string 0x435f33315f6465706c6f79656400000000000000000000000000000000000000]
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
                      [Literal.string 0x435f33315f6465706c6f79656400000000000000000000000000000000000000]
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
    Definition name : string := "C_31_deployed".

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
            "cleanup_bytes32",
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
            "validator_revert_bytes32",
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
                            "cleanup_bytes32",
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
            "abi_decode_t_bytes32",
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
                    "validator_revert_bytes32",
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
            "abi_decode_bytes32",
            ["headStart"; "dataEnd"],
            ["value0"],
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
                      [Literal.number 32]
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
                  Some ([Literal.number 0])
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["value0"],
                  Some (M.call (|
                    "abi_decode_t_bytes32",
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
            "abi_encode_uint256",
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
            "abi_encode_uint256_uint256_uint256",
            ["headStart"; "value0"; "value1"; "value2"],
            ["tail"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["tail"],
                  Some (M.call (|
                    "add",
                    [
                      M.get_var (| "headStart" |);
                      [Literal.number 96]
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "abi_encode_uint256",
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
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "abi_encode_uint256",
                    [
                      M.get_var (| "value1" |);
                      M.call (|
                        "add",
                        [
                          M.get_var (| "headStart" |);
                          [Literal.number 32]
                        ]
                      |)
                    ]
                  |)
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "abi_encode_uint256",
                    [
                      M.get_var (| "value2" |);
                      M.call (|
                        "add",
                        [
                          M.get_var (| "headStart" |);
                          [Literal.number 64]
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
                  ["param"],
                  Some (M.call (|
                    "abi_decode_bytes32",
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
                  ["ret"; "ret_1"; "ret_2"],
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
                    "abi_encode_uint256_uint256_uint256",
                    [
                      M.get_var (| "memPos" |);
                      M.get_var (| "ret" |);
                      M.get_var (| "ret_1" |);
                      M.get_var (| "ret_2" |)
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
            "identity",
            ["value"],
            ["ret"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["ret"],
                  Some (M.get_var (| "value" |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "cleanup_rational_by",
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
            "cleanup_uint8",
            ["value"],
            ["cleaned"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["cleaned"],
                  Some (M.call (|
                    "and",
                    [
                      M.get_var (| "value" |);
                      [Literal.number 0xff]
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
            "convert_rational_by_to_uint8",
            ["value"],
            ["converted"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["converted"],
                  Some (M.call (|
                    "cleanup_uint8",
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "panic_error_0x11",
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
                      [Literal.number 0x11]
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
            "checked_add_uint8",
            ["x"; "y"],
            ["sum"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["x"],
                  Some (M.call (|
                    "cleanup_uint8",
                    [
                      M.get_var (| "x" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["y"],
                  Some (M.call (|
                    "cleanup_uint8",
                    [
                      M.get_var (| "y" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["sum"],
                  Some (M.call (|
                    "add",
                    [
                      M.get_var (| "x" |);
                      M.get_var (| "y" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.if_ (|
                  M.call (|
                    "gt",
                    [
                      M.get_var (| "sum" |);
                      [Literal.number 0xff]
                    ]
                  |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "panic_error_0x11",
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
            "convert_uint8_to_uint256",
            ["value"],
            ["converted"],
            M.scope (
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
                            "cleanup_uint8",
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "fun_f",
            ["var_x"],
            ["var_"; "var"; "var_1"],
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
                  ["var_"],
                  Some (M.get_var (| "zero_uint256" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["zero_uint256_1"],
                  Some (M.call (|
                    "zero_value_for_split_uint256",
                    []
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var"],
                  Some (M.get_var (| "zero_uint256_1" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["zero_t_uint256"],
                  Some (M.call (|
                    "zero_value_for_split_uint256",
                    []
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_1"],
                  Some (M.get_var (| "zero_t_uint256" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr"],
                  Some ([Literal.number 32])
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_component"],
                  Some (M.get_var (| "expr" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_1"],
                  Some ([Literal.number 16])
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_component_1"],
                  Some (M.get_var (| "expr_1" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_2"],
                  Some ([Literal.number 1])
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_3"],
                  Some ([Literal.number 0x07])
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_4"],
                  Some (M.call (|
                    "checked_add_uint8",
                    [
                      M.get_var (| "expr_2" |);
                      M.call (|
                        "convert_rational_by_to_uint8",
                        [
                          M.get_var (| "expr_3" |)
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_component_2"],
                  Some (M.get_var (| "expr_4" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_"],
                  Some (M.call (|
                    "convert_uint8_to_uint256",
                    [
                      M.get_var (| "expr_component" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var"],
                  Some (M.call (|
                    "convert_uint8_to_uint256",
                    [
                      M.get_var (| "expr_component_1" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_1"],
                  Some (M.call (|
                    "convert_uint8_to_uint256",
                    [
                      M.get_var (| "expr_component_2" |)
                    ]
                  |))
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
                          Some (Literal.number 0xd7da973a),
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
      "a264697066735822122090236c43b99d9a4d123458139f86877b29ea2c1d9403b9e3ad885f461068f56f64736f6c634300081b0033".
  End deployed.
End C.
