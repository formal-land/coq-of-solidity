(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition name : string := "C_34".

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
          M.pure BlockUnit.Tt
        )
      )) in
      M.pure BlockUnit.Tt
    ).

  Module deployed.
    Definition name : string := "C_34_deployed".

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
            "cleanup_uint16",
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
                      [Literal.number 0xffff]
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
            "validator_revert_uint16",
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
                            "cleanup_uint16",
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
            "abi_decode_uint16",
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
                    "validator_revert_uint16",
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
            "abi_decode_uint16t_uint16t_uint16",
            ["headStart"; "dataEnd"],
            ["value0"; "value1"; "value2"],
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
                  Some ([Literal.number 0])
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["value0"],
                  Some (M.call (|
                    "abi_decode_uint16",
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
                  Some ([Literal.number 32])
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["value1"],
                  Some (M.call (|
                    "abi_decode_uint16",
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
                  ["value2"],
                  Some (M.call (|
                    "abi_decode_uint16",
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
            "abi_encode_uint16",
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
                        "cleanup_uint16",
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
            "abi_encode_tuple_uint16",
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
                    "abi_encode_uint16",
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
                  ["param"; "param_1"; "param_2"],
                  Some (M.call (|
                    "abi_decode_uint16t_uint16t_uint16",
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
                      M.get_var (| "param_2" |)
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
                    "abi_encode_tuple_uint16",
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
            "zero_value_for_split_uint16",
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
            "modifier_add",
            ["var"; "var_a"; "var_b"; "var_c"],
            ["_1"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["_1"],
                  Some (M.get_var (| "var" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["_1"],
                  Some (M.call (|
                    "fun_f_inner",
                    [
                      M.get_var (| "var" |);
                      M.get_var (| "var_a" |);
                      M.get_var (| "var_b" |);
                      M.get_var (| "var_c" |)
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
            "checked_add_uint16",
            ["x"; "y"],
            ["sum"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["x"],
                  Some (M.call (|
                    "cleanup_uint16",
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
                    "cleanup_uint16",
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
                      [Literal.number 0xffff]
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
            "fun_f_inner",
            ["_1"; "var_a"; "var_b"; "var_c"],
            ["var"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["var"],
                  Some (M.get_var (| "_1" |))
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
                  ["expr"],
                  Some (M.get_var (| "_2" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_3"],
                  Some (M.get_var (| "var_c" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_1"],
                  Some (M.get_var (| "_3" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_2"],
                  Some (M.call (|
                    "checked_add_uint16",
                    [
                      M.get_var (| "expr" |);
                      M.get_var (| "expr_1" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var"],
                  Some (M.get_var (| "expr_2" |))
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
          M.function (|
            "fun_f",
            ["var_a"; "var_b"; "var_c"],
            ["var_"],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["zero_uint16"],
                  Some (M.call (|
                    "zero_value_for_split_uint16",
                    []
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_"],
                  Some (M.get_var (| "zero_uint16" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_"],
                  Some (M.call (|
                    "modifier_add",
                    [
                      M.get_var (| "var_" |);
                      M.get_var (| "var_a" |);
                      M.get_var (| "var_b" |);
                      M.get_var (| "var_c" |)
                    ]
                  |))
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
                          Some (Literal.number 0x85df086f),
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
      "a264697066735822122083c26c8d5131e136345944be951fe0749c6cb7dbfded91149d5f9e00a592b22f64736f6c634300081b0033".
  End deployed.
End C.
