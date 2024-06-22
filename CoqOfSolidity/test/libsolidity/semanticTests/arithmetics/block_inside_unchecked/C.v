(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition name : string := "C_27".

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
                      [Literal.string 0x435f32375f6465706c6f79656400000000000000000000000000000000000000]
                    ]
                  |);
                  M.call (|
                    "datasize",
                    [
                      [Literal.string 0x435f32375f6465706c6f79656400000000000000000000000000000000000000]
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
                      [Literal.string 0x435f32375f6465706c6f79656400000000000000000000000000000000000000]
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
    Definition name : string := "C_27_deployed".

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
            "abi_decode",
            ["headStart"; "dataEnd"],
            [],
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
                      [Literal.number 0]
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
                    "fun_f",
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
            "convert_rational_by_to_uint256",
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
            "wrapping_add_uint256",
            ["x"; "y"],
            ["sum"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["sum"],
                  Some (M.call (|
                    "cleanup_uint256",
                    [
                      M.call (|
                        "add",
                        [
                          M.get_var (| "x" |);
                          M.get_var (| "y" |)
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
            [],
            ["var_y"],
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
                  ["var_y"],
                  Some (M.get_var (| "zero_uint256" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr"],
                  Some (M.call (|
                    "not",
                    [
                      [Literal.number 0]
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["var_max"],
                  Some (M.get_var (| "expr" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_1"],
                  Some (M.get_var (| "var_max" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_1"],
                  Some (M.get_var (| "_1" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_2"],
                  Some ([Literal.number 0x01])
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_3"],
                  Some (M.call (|
                    "wrapping_add_uint256",
                    [
                      M.get_var (| "expr_1" |);
                      M.call (|
                        "convert_rational_by_to_uint256",
                        [
                          M.get_var (| "expr_2" |)
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["var_x"],
                  Some (M.get_var (| "expr_3" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["_2"],
                  Some (M.get_var (| "var_x" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_4"],
                  Some (M.get_var (| "_2" |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["var_y"],
                  Some (M.get_var (| "expr_4" |))
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
                          Some (Literal.number 0x26121ff0),
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
      "a2646970667358221220295f9bdbaa546896bf76183a4d3bdc37b359e2a6d3c9e9ade156148dc5971a1964736f6c634300081b0033".
  End deployed.
End C.
