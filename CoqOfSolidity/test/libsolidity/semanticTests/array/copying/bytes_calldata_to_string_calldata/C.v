(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_14";
    Code.hex_name := 0x435f313400000000000000000000000000000000000000000000000000000000;
    Code.code :=
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
                        [Literal.string 0x435f31345f6465706c6f79656400000000000000000000000000000000000000]
                      ]
                    |);
                    M.call (|
                      "datasize",
                      [
                        [Literal.string 0x435f31345f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x435f31345f6465706c6f79656400000000000000000000000000000000000000]
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
      );
  |}.

  Module deployed.
    Definition code : Code.t := {|
      Code.name := "C_14_deployed";
      Code.hex_name := 0x435f31345f6465706c6f79656400000000000000000000000000000000000000;
      Code.code :=
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
              "abi_decode_bytes_calldata_ptr",
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
                                [Literal.number 0x01]
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
              "abi_decode_bytes_calldata",
              ["headStart"; "dataEnd"],
              ["value0"; "value1"],
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
                      "abi_decode_bytes_calldata_ptr",
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
              "array_storeLengthForEncoding_string",
              ["pos"; "length"],
              ["updated_pos"],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "mstore",
                      [
                        M.get_var (| "pos" |);
                        M.get_var (| "length" |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["updated_pos"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "pos" |);
                        [Literal.number 0x20]
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
              "copy_calldata_to_memory_with_cleanup",
              ["src"; "dst"; "length"],
              [],
              M.scope (
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "calldatacopy",
                      [
                        M.get_var (| "dst" |);
                        M.get_var (| "src" |);
                        M.get_var (| "length" |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "mstore",
                      [
                        M.call (|
                          "add",
                          [
                            M.get_var (| "dst" |);
                            M.get_var (| "length" |)
                          ]
                        |);
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
              "round_up_to_mul_of",
              ["value"],
              ["result"],
              M.scope (
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
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "abi_encode_string_calldata_ptr",
              ["start"; "length"; "pos"],
              ["end"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["pos"],
                    Some (M.call (|
                      "array_storeLengthForEncoding_string",
                      [
                        M.get_var (| "pos" |);
                        M.get_var (| "length" |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.expr_stmt (|
                    M.call (|
                      "copy_calldata_to_memory_with_cleanup",
                      [
                        M.get_var (| "start" |);
                        M.get_var (| "pos" |);
                        M.get_var (| "length" |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["end"],
                    Some (M.call (|
                      "add",
                      [
                        M.get_var (| "pos" |);
                        M.call (|
                          "round_up_to_mul_of",
                          [
                            M.get_var (| "length" |)
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
              "abi_encode_string_calldata",
              ["headStart"; "value0"; "value1"],
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
                      "mstore",
                      [
                        M.call (|
                          "add",
                          [
                            M.get_var (| "headStart" |);
                            [Literal.number 0]
                          ]
                        |);
                        M.call (|
                          "sub",
                          [
                            M.get_var (| "tail" |);
                            M.get_var (| "headStart" |)
                          ]
                        |)
                      ]
                    |)
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["tail"],
                    Some (M.call (|
                      "abi_encode_string_calldata_ptr",
                      [
                        M.get_var (| "value0" |);
                        M.get_var (| "value1" |);
                        M.get_var (| "tail" |)
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
                    ["param"; "param_1"],
                    Some (M.call (|
                      "abi_decode_bytes_calldata",
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
                    ["ret"; "ret_1"],
                    Some (M.call (|
                      "fun_f",
                      [
                        M.get_var (| "param" |);
                        M.get_var (| "param_1" |)
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
                      "abi_encode_string_calldata",
                      [
                        M.get_var (| "memPos" |);
                        M.get_var (| "ret" |);
                        M.get_var (| "ret_1" |)
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
              "zero_value_for_split_string_calldata",
              [],
              ["offset"; "length"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["offset"],
                    Some (M.call (|
                      "calldatasize",
                      []
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["length"],
                    Some ([Literal.number 0])
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "convert_array_bytes_calldata_to_string_calldata",
              ["value"; "length"],
              ["converted"; "outLength"],
              M.scope (
                do* ltac:(M.monadic (
                  M.assign (|
                    ["converted"],
                    Some (M.get_var (| "value" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["outLength"],
                    Some (M.get_var (| "length" |))
                  |)
                )) in
                M.pure BlockUnit.Tt
              )
            |)
          )) in
          do* ltac:(M.monadic (
            M.function (|
              "fun_f",
              ["var_c_offset"; "var_c_length"],
              ["var_s_offset"; "var_s_length"],
              M.scope (
                do* ltac:(M.monadic (
                  M.declare (|
                    ["zero_string_calldata_offset"; "zero_string_calldata_length"],
                    Some (M.call (|
                      "zero_value_for_split_string_calldata",
                      []
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["var_s_offset"],
                    Some (M.get_var (| "zero_string_calldata_offset" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["var_s_length"],
                    Some (M.get_var (| "zero_string_calldata_length" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["_offset"],
                    Some (M.get_var (| "var_c_offset" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["_length"],
                    Some (M.get_var (| "var_c_length" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["expr_9_offset"],
                    Some (M.get_var (| "_offset" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["expr_length"],
                    Some (M.get_var (| "_length" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.declare (|
                    ["expr_offset"; "expr_10_length"],
                    Some (M.call (|
                      "convert_array_bytes_calldata_to_string_calldata",
                      [
                        M.get_var (| "expr_9_offset" |);
                        M.get_var (| "expr_length" |)
                      ]
                    |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["var_s_offset"],
                    Some (M.get_var (| "expr_offset" |))
                  |)
                )) in
                do* ltac:(M.monadic (
                  M.assign (|
                    ["var_s_length"],
                    Some (M.get_var (| "expr_10_length" |))
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
                            Some (Literal.number 0xd45754f8),
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
        );
    |}.

    Definition data : string :=
      "a264697066735822122054eaf49ffa6129d4adf90c60c6e4c0fb6188d83a798b8fa1ffad7ade6ff1105164736f6c634300081b0033".
  End deployed.
End C.

Definition codes : list (U256.t * M.t BlockUnit.t) :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
