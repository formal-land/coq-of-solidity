(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module Test.
  Definition name : string := "Test_31".

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
      M.function (|
        "convert_stringliteral_4e03_to_bytes3",
        [],
        ["converted"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["converted"],
            Some (M.call (|
              "shl",
              [
                [Literal.number 232];
                [Literal.number 6382179]
              ]
            |))
          |)
        )) in
        M.close_scope
      |)
    )) in
    do* ltac:(M.monadic (
      M.function (|
        "constructor_Test",
        [],
        [],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.declare (|
            ["_1"],
            Some (M.call (|
              "convert_stringliteral_4e03_to_bytes3",
              []
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.expr_stmt (|
            M.call (|
              "fun_setName",
              [
                M.get_var (| "_1" |)
              ]
            |)
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
            Some ([Literal.number 16777215])
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
        "cleanup_bytes3",
        ["value"],
        ["cleaned"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["cleaned"],
            Some (M.call (|
              "and",
              [
                M.get_var (| "value" |);
                M.call (|
                  "shl",
                  [
                    [Literal.number 232];
                    [Literal.number 16777215]
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
        "convert_bytes3_to_bytes3",
        ["value"],
        ["converted"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["converted"],
            Some (M.call (|
              "cleanup_bytes3",
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
                [Literal.number 232];
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
        "prepare_store_bytes3",
        ["value"],
        ["ret"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["ret"],
            Some (M.call (|
              "shift_right_unsigned",
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
        "update_storage_value_offsett_bytes3_to_bytes3",
        ["slot"; "value"],
        [],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.declare (|
            ["convertedValue"],
            Some (M.call (|
              "convert_bytes3_to_bytes3",
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
                      "prepare_store_bytes3",
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
        "fun_setName",
        ["var_name"],
        [],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.declare (|
            ["_1"],
            Some (M.get_var (| "var_name" |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["expr"],
            Some (M.get_var (| "_1" |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.expr_stmt (|
            M.call (|
              "update_storage_value_offsett_bytes3_to_bytes3",
              [
                [Literal.number 0x00];
                M.get_var (| "expr" |)
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
        M.expr_stmt (|
          M.call (|
            "constructor_Test",
            []
          |)
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
                  [Literal.string 0x546573745f33315f6465706c6f79656400000000000000000000000000000000]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string 0x546573745f33315f6465706c6f79656400000000000000000000000000000000]
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
                  [Literal.string 0x546573745f33315f6465706c6f79656400000000000000000000000000000000]
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
    Definition name : string := "Test_31_deployed".

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
          "cleanup_bytes3",
          ["value"],
          ["cleaned"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["cleaned"],
              Some (M.call (|
                "and",
                [
                  M.get_var (| "value" |);
                  M.call (|
                    "shl",
                    [
                      [Literal.number 232];
                      [Literal.number 16777215]
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
          "abi_encode_bytes3_to_bytes3",
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
                    "cleanup_bytes3",
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
          "abi_encode_bytes3",
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
                "abi_encode_bytes3_to_bytes3",
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
          "external_fun_getName",
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
                "fun_getName",
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
                "abi_encode_bytes3",
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
          "zero_value_for_split_bytes3",
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
          "shift_right_0_unsigned",
          ["value"],
          ["newValue"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["newValue"],
              Some (M.call (|
                "shr",
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
                  [Literal.number 232];
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
          "cleanup_from_storage_bytes3",
          ["value"],
          ["cleaned"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["cleaned"],
              Some (M.call (|
                "shift_left",
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
          "extract_from_storage_value_offsett_bytes3",
          ["slot_value"],
          ["value"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["value"],
              Some (M.call (|
                "cleanup_from_storage_bytes3",
                [
                  M.call (|
                    "shift_right_0_unsigned",
                    [
                      M.get_var (| "slot_value" |)
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
          "read_from_storage_split_offset_bytes3",
          ["slot"],
          ["value"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.assign (|
              ["value"],
              Some (M.call (|
                "extract_from_storage_value_offsett_bytes3",
                [
                  M.call (|
                    "sload",
                    [
                      M.get_var (| "slot" |)
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
          "fun_getName",
          [],
          ["var_ret"],
          do* M.open_scope in
          do* ltac:(M.monadic (
            M.declare (|
              ["zero_bytes3"],
              Some (M.call (|
                "zero_value_for_split_bytes3",
                []
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_ret"],
              Some (M.get_var (| "zero_bytes3" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["_1"],
              Some (M.call (|
                "read_from_storage_split_offset_bytes3",
                [
                  [Literal.number 0x00]
                ]
              |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.declare (|
              ["expr"],
              Some (M.get_var (| "_1" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.assign (|
              ["var_ret"],
              Some (M.get_var (| "expr" |))
            |)
          )) in
          do* ltac:(M.monadic (
            M.leave (||)
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
                    Some (Literal.number 0x17d7de7c),
                    do* M.open_scope in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "external_fun_getName",
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
                  )
                ]
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
      "a2646970667358221220939a80a9105c6cb46df0ebac6d57471090e5e4332ee106e6388abc58289b6c1464736f6c634300081b0033".
  End deployed.
End Test.
