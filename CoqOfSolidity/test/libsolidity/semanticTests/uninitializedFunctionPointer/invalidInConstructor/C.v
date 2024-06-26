(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C.
  Definition code : Code.t := {|
    Code.name := "C_35";
    Code.hex_name := 0x435f333500000000000000000000000000000000000000000000000000000000;
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
                      [Literal.number 64];
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
            "cleanup_from_storage_bool",
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
            "extract_from_storage_value_offsett_bool",
            ["slot_value"],
            ["value"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["value"],
                  Some (M.call (|
                    "cleanup_from_storage_bool",
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "read_from_storage_split_offset_bool",
            ["slot"],
            ["value"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["value"],
                  Some (M.call (|
                    "extract_from_storage_value_offsett_bool",
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "cleanup_bool",
            ["value"],
            ["cleaned"],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "shift_left_64",
            ["value"],
            ["newValue"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["newValue"],
                  Some (M.call (|
                    "shl",
                    [
                      [Literal.number 64];
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
            "update_byte_slice_shift",
            ["value"; "toInsert"],
            ["result"],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["mask"],
                  Some ([Literal.number 0xff0000000000000000])
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["toInsert"],
                  Some (M.call (|
                    "shift_left_64",
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "convert_bool_to_bool",
            ["value"],
            ["converted"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["converted"],
                  Some (M.call (|
                    "cleanup_bool",
                    [
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
            "prepare_store_bool",
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
            "update_storage_value_offsett_bool_to_bool",
            ["slot"; "value"],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["convertedValue"],
                  Some (M.call (|
                    "convert_bool_to_bool",
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
                            "prepare_store_bool",
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "zero_value_for_split_function_internal_nonpayable_returns",
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
            "shift_left",
            ["value"],
            ["newValue"],
            M.scope (
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "update_byte_slice_shift_0",
            ["value"; "toInsert"],
            ["result"],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["mask"],
                  Some (M.call (|
                    "sub",
                    [
                      M.call (|
                        "shl",
                        [
                          [Literal.number 64];
                          [Literal.number 1]
                        ]
                      |);
                      [Literal.number 1]
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "convert_function_internal_nonpayable_returns_to_function_internal_nonpayable_returns",
            ["functionId"],
            ["outFunctionId"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["outFunctionId"],
                  Some (M.get_var (| "functionId" |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "prepare_store_function_internal_nonpayable_returns",
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
            "update_storage_value_offsett_function_internal_nonpayable_returns_to_function_internal_nonpayable_returns",
            ["slot"; "value"],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["convertedValue"],
                  Some (M.call (|
                    "convert_function_internal_nonpayable_returns_to_function_internal_nonpayable_returns",
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
                        "update_byte_slice_shift_0",
                        [
                          M.call (|
                            "sload",
                            [
                              M.get_var (| "slot" |)
                            ]
                          |);
                          M.call (|
                            "prepare_store_function_internal_nonpayable_returns",
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
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "constructor_C",
            [],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["_1"],
                  Some (M.call (|
                    "read_from_storage_split_offset_bool",
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
                M.declare (|
                  ["expr_1"],
                  Some (M.call (|
                    "cleanup_bool",
                    [
                      M.call (|
                        "iszero",
                        [
                          M.get_var (| "expr" |)
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.if_ (|
                  M.get_var (| "expr_1" |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.declare (|
                        ["expr_2"],
                        Some ([Literal.number 0x01])
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "update_storage_value_offsett_bool_to_bool",
                          [
                            [Literal.number 0x00];
                            M.get_var (| "expr_2" |)
                          ]
                        |)
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.declare (|
                        ["var_invalid_functionIdentifier"],
                        None
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.declare (|
                        ["zero_function_internal_nonpayable_returns_functionIdentifier"],
                        Some (M.call (|
                          "zero_value_for_split_function_internal_nonpayable_returns",
                          []
                        |))
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.assign (|
                        ["var_invalid_functionIdentifier"],
                        Some (M.get_var (| "zero_function_internal_nonpayable_returns_functionIdentifier" |))
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.declare (|
                        ["_4_functionIdentifier"],
                        Some (M.get_var (| "var_invalid_functionIdentifier" |))
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.declare (|
                        ["expr_21_functionIdentifier"],
                        Some (M.get_var (| "_4_functionIdentifier" |))
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "update_storage_value_offsett_function_internal_nonpayable_returns_to_function_internal_nonpayable_returns",
                          [
                            [Literal.number 0x00];
                            M.get_var (| "expr_21_functionIdentifier" |)
                          ]
                        |)
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.declare (|
                        ["_functionIdentifier"],
                        Some (M.get_var (| "var_invalid_functionIdentifier" |))
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.declare (|
                        ["expr_functionIdentifier"],
                        Some (M.get_var (| "_functionIdentifier" |))
                      |)
                    )) in
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "dispatch_internal_in_out",
                          [
                            M.get_var (| "expr_functionIdentifier" |)
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
            "panic_error_0x51",
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
                      [Literal.number 0x51]
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
            "dispatch_internal_in_out",
            ["fun"],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.switch (|
                  M.get_var (| "fun" |),
                  [
                    (
                      None,
                      M.scope (
                        do* ltac:(M.monadic (
                          M.expr_stmt (|
                            M.call (|
                              "panic_error_0x51",
                              []
                            |)
                          |)
                        )) in
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
              M.expr_stmt (|
                M.call (|
                  "constructor_C",
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
                        [Literal.string 0x435f33355f6465706c6f79656400000000000000000000000000000000000000]
                      ]
                    |);
                    M.call (|
                      "datasize",
                      [
                        [Literal.string 0x435f33355f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x435f33355f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "C_35_deployed";
      Code.hex_name := 0x435f33355f6465706c6f79656400000000000000000000000000000000000000;
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
              "abi_encode_tuple",
              ["headStart"],
              ["tail"],
              M.scope (
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
        );
    |}.

    Definition data : string :=
      "a26469706673582212205158623565d600ee98079bf6b90814dfe422474626f17474011d761adb2f1b7564736f6c634300081b0033".
  End deployed.
End C.

Definition codes : list (U256.t * M.t BlockUnit.t) :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
