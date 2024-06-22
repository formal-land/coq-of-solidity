(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module Base.
  Definition name : string := "Base_25".

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
        "cleanup_from_storage_uint256",
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
        "extract_from_storage_value_offsett_uint256",
        ["slot_value"],
        ["value"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["value"],
            Some (M.call (|
              "cleanup_from_storage_uint256",
              [
                M.call (|
                  "shift_right_unsigned",
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
        "read_from_storage_split_offset_uint256",
        ["slot"],
        ["value"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["value"],
            Some (M.call (|
              "extract_from_storage_value_offsett_uint256",
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
        "panic_error_0x11",
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
        M.close_scope
      |)
    )) in
    do* ltac:(M.monadic (
      M.function (|
        "checked_mul_uint256",
        ["x"; "y"],
        ["product"],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.assign (|
            ["x"],
            Some (M.call (|
              "cleanup_uint256",
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
              "cleanup_uint256",
              [
                M.get_var (| "y" |)
              ]
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["product_raw"],
            Some (M.call (|
              "mul",
              [
                M.get_var (| "x" |);
                M.get_var (| "y" |)
              ]
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.assign (|
            ["product"],
            Some (M.call (|
              "cleanup_uint256",
              [
                M.get_var (| "product_raw" |)
              ]
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.if_ (|
            M.call (|
              "iszero",
              [
                M.call (|
                  "or",
                  [
                    M.call (|
                      "iszero",
                      [
                        M.get_var (| "x" |)
                      ]
                    |);
                    M.call (|
                      "eq",
                      [
                        M.get_var (| "y" |);
                        M.call (|
                          "div",
                          [
                            M.get_var (| "product" |);
                            M.get_var (| "x" |)
                          ]
                        |)
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
                  "panic_error_0x11",
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
        "constructor_Base",
        [],
        [],
        do* M.open_scope in
        do* ltac:(M.monadic (
          M.declare (|
            ["expr"],
            Some ([Literal.number 0x07])
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
              "constructor_BaseBase",
              [
                M.get_var (| "_1" |)
              ]
            |)
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["_2"],
            Some (M.call (|
              "read_from_storage_split_offset_uint256",
              [
                [Literal.number 0x00]
              ]
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["expr_1"],
            Some (M.get_var (| "_2" |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["_3"],
            Some (M.call (|
              "read_from_storage_split_offset_uint256",
              [
                [Literal.number 0x00]
              ]
            |))
          |)
        )) in
        do* ltac:(M.monadic (
          M.declare (|
            ["expr_2"],
            Some (M.call (|
              "checked_mul_uint256",
              [
                M.get_var (| "_3" |);
                M.get_var (| "expr_1" |)
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
                M.get_var (| "expr_2" |)
              ]
            |)
          |)
        )) in
        M.close_scope
      |)
    )) in
    do* ltac:(M.monadic (
      M.function (|
        "constructor_BaseBase",
        ["var_a"],
        [],
        do* M.open_scope in
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
          M.expr_stmt (|
            M.call (|
              "update_storage_value_offsett_uint256_to_uint256",
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
            "constructor_Base",
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
                  [Literal.string 0x426173655f32355f6465706c6f79656400000000000000000000000000000000]
                ]
              |);
              M.call (|
                "datasize",
                [
                  [Literal.string 0x426173655f32355f6465706c6f79656400000000000000000000000000000000]
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
                  [Literal.string 0x426173655f32355f6465706c6f79656400000000000000000000000000000000]
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
    Definition name : string := "Base_25_deployed".

    Definition code : M.t BlockUnit.t :=
      do* M.open_scope in
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
      "a264697066735822122078d4c12311fd957bbbd7aa521eef3bc6d0c93a6e81d1bb459017e0c573950d3164736f6c634300081b0033".
  End deployed.
End Base.
