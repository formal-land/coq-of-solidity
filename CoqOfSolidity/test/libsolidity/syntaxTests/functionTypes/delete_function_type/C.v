(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_61.
  Definition code : M.t unit := ltac:(M.monadic (
    let _ :=
      let _ :=
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
        |) in
      let _ :=
        M.if_ (|
          M.call (|
            "callvalue",
            []
          |),
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                []
              |) in
            tt
          ))
        |) in
      let _ :=
        M.assign (|
          ["_1"],
          Some (M.call (|
            "allocate_unbounded",
            []
          |))
        |) in
      let _ :=
        M.call (|
          "codecopy",
          [
            M.get (| "_1" |);
            M.call (|
              "dataoffset",
              [
                [Literal.string "435f36315f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f36315f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      let _ :=
        M.call (|
          "return",
          [
            M.get (| "_1" |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f36315f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      tt in
    let _ :=
      M.function (|
        "allocate_unbounded",
        [],
        ["memPtr"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["memPtr"],
              M.call (|
                "mload",
                [
                  [Literal.number 64]
                ]
              |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
            M.call (|
              "revert",
              [
                [Literal.number 0];
                [Literal.number 0]
              ]
            |) in
          tt
        ))
      |) in
    tt
  )).

  Module C_61_deployed.
    Definition code : M.t unit := ltac:(M.monadic (
      let _ :=
        let _ :=
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
          |) in
        let _ :=
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
            ltac:(M.monadic (
              let _ :=
                M.assign (|
                  ["selector"],
                  Some (M.call (|
                    "shift_right_224_unsigned",
                    [
                      M.call (|
                        "calldataload",
                        [
                          [Literal.number 0]
                        ]
                      |)
                    ]
                  |))
                |) in
              let _ :=
                M.switch (|
                  M.get (| "selector" |),
                  [
                    (
                      Some (Literal.number 0x26121ff0),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_f",
                            []
                          |) in
                        tt
                      ))              );
                    (
                      None,
                      ltac:(M.monadic (
                        tt
                      ))              )            ]
                |) in
              tt
            ))
          |) in
        let _ :=
          M.call (|
            "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
            []
          |) in
        tt in
      let _ :=
        M.function (|
          "shift_right_224_unsigned",
          ["value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shr",
                  [
                    [Literal.number 224];
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "allocate_unbounded",
          [],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "mload",
                  [
                    [Literal.number 64]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode",
          ["headStart"; "dataEnd"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "slt",
                  [
                    M.call (|
                      "sub",
                      [
                        M.get (| "dataEnd" |);
                        M.get (| "headStart" |)
                      ]
                    |);
                    [Literal.number 0]
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
                      []
                    |) in
                  tt
                ))
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_tuple",
          ["headStart"],
          ["tail"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["tail"],
                M.call (|
                  "add",
                  [
                    M.get (| "headStart" |);
                    [Literal.number 0]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "external_fun_f",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "callvalue",
                  []
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.call (|
                "abi_decode",
                [
                  [Literal.number 4];
                  M.call (|
                    "calldatasize",
                    []
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "fun_f",
                []
              |) in
            let _ :=
              M.assign (|
                ["memPos"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["memEnd"],
                Some (M.call (|
                  "abi_encode_tuple",
                  [
                    M.get (| "memPos" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "return",
                [
                  M.get (| "memPos" |);
                  M.call (|
                    "sub",
                    [
                      M.get (| "memEnd" |);
                      M.get (| "memPos" |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "revert",
                [
                  [Literal.number 0];
                  [Literal.number 0]
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "shift_left_dynamic",
          ["bits"; "value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shl",
                  [
                    M.get (| "bits" |);
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "update_byte_slice_dynamic24",
          ["value"; "shiftBytes"; "toInsert"],
          ["result"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["shiftBits"],
                Some (M.call (|
                  "mul",
                  [
                    M.get (| "shiftBytes" |);
                    [Literal.number 8]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["mask"],
                Some (M.call (|
                  "shift_left_dynamic",
                  [
                    M.get (| "shiftBits" |);
                    M.call (|
                      "sub",
                      [
                        M.call (|
                          "shl",
                          [
                            [Literal.number 192];
                            [Literal.number 1]
                          ]
                        |);
                        [Literal.number 1]
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["toInsert"],
                M.call (|
                  "shift_left_dynamic",
                  [
                    M.get (| "shiftBits" |);
                    M.get (| "toInsert" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "and",
                  [
                    M.get (| "value" |);
                    M.call (|
                      "not",
                      [
                        M.get (| "mask" |)
                      ]
                    |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["result"],
                M.call (|
                  "or",
                  [
                    M.get (| "value" |);
                    M.call (|
                      "and",
                      [
                        M.get (| "toInsert" |);
                        M.get (| "mask" |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_function_external_nonpayable_uint256_returns_uint256_to_function_external_nonpayable_uint256_returns_uint",
          ["addr"; "functionId"],
          ["outAddr";
      "outFunctionId"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["outAddr"],
                M.get (| "addr" |)
              |) in
            let _ :=
              M.declare (|
                ["outFunctionId"],
                M.get (| "functionId" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "shift_right_64_unsigned",
          ["value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shr",
                  [
                    [Literal.number 64];
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "prepare_store_bytes24",
          ["value"],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                M.call (|
                  "shift_right_64_unsigned",
                  [
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "shift_left_32",
          ["value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shl",
                  [
                    [Literal.number 32];
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "shift_left",
          ["value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shl",
                  [
                    [Literal.number 64];
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "combine_external_function_id",
          ["addr"; "selector"],
          ["combined"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["combined"],
                M.call (|
                  "shift_left",
                  [
                    M.call (|
                      "or",
                      [
                        M.call (|
                          "shift_left_32",
                          [
                            M.get (| "addr" |)
                          ]
                        |);
                        M.call (|
                          "and",
                          [
                            M.get (| "selector" |);
                            [Literal.number 0xffffffff]
                          ]
                        |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "prepare_store_function_external_nonpayable_uint256_returns_uint",
          ["addr"; "selector"],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                M.call (|
                  "prepare_store_bytes24",
                  [
                    M.call (|
                      "combine_external_function_id",
                      [
                        M.get (| "addr" |);
                        M.get (| "selector" |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "update_storage_value_function_external_nonpayable_uint256_returns_uint256_to_function_external_nonpayable_uint256_returns_uint",
          ["slot"; "offset"; "value"; "value_1"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["convertedValue"; "convertedValue_1"],
                Some (M.call (|
                  "convert_function_external_nonpayable_uint256_returns_uint256_to_function_external_nonpayable_uint256_returns_uint",
                  [
                    M.get (| "value" |);
                    M.get (| "value_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "sstore",
                [
                  M.get (| "slot" |);
                  M.call (|
                    "update_byte_slice_dynamic24",
                    [
                      M.call (|
                        "sload",
                        [
                          M.get (| "slot" |)
                        ]
                      |);
                      M.get (| "offset" |);
                      M.call (|
                        "prepare_store_function_external_nonpayable_uint256_returns_uint",
                        [
                          M.get (| "convertedValue" |);
                          M.get (| "convertedValue_1" |)
                        ]
                      |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "zero_value_for_split_function_external_nonpayable_uint256_returns_uint",
          [],
          ["retAddress";
      "retFunction"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["retAddress"],
                [Literal.number 0]
              |) in
            let _ :=
              M.declare (|
                ["retFunction"],
                [Literal.number 0]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "storage_set_to_zero_function_external_nonpayable_uint256_returns_uint",
          ["slot"; "offset"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["zero"; "zero_1"],
                Some (M.call (|
                  "zero_value_for_split_function_external_nonpayable_uint256_returns_uint",
                  []
                |))
              |) in
            let _ :=
              M.call (|
                "update_storage_value_function_external_nonpayable_uint256_returns_uint256_to_function_external_nonpayable_uint256_returns_uint",
                [
                  M.get (| "slot" |);
                  M.get (| "offset" |);
                  M.get (| "zero" |);
                  M.get (| "zero_1" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "shift_right_unsigned",
          ["value"],
          ["newValue"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["newValue"],
                M.call (|
                  "shr",
                  [
                    [Literal.number 192];
                    M.get (| "value" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_from_storage_function_internal_nonpayable_uint256_returns_uint",
          ["value"],
          ["cleaned"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["cleaned"],
                M.call (|
                  "and",
                  [
                    M.get (| "value" |);
                    [Literal.number 0xffffffffffffffff]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "extract_from_storage_value_offsett_function_internal_nonpayable_uint256_returns_uint",
          ["slot_value"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "cleanup_from_storage_function_internal_nonpayable_uint256_returns_uint",
                  [
                    M.call (|
                      "shift_right_unsigned",
                      [
                        M.get (| "slot_value" |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "read_from_storage_split_offset_function_internal_nonpayable_uint256_returns_uint",
          ["slot"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "extract_from_storage_value_offsett_function_internal_nonpayable_uint256_returns_uint",
                  [
                    M.call (|
                      "sload",
                      [
                        M.get (| "slot" |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "zero_value_for_split_function_internal_nonpayable_uint256_returns_uint",
          [],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                [Literal.number 0]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "update_byte_slice_dynamic8",
          ["value"; "shiftBytes"; "toInsert"],
          ["result"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["shiftBits"],
                Some (M.call (|
                  "mul",
                  [
                    M.get (| "shiftBytes" |);
                    [Literal.number 8]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["mask"],
                Some (M.call (|
                  "shift_left_dynamic",
                  [
                    M.get (| "shiftBits" |);
                    [Literal.number 0xffffffffffffffff]
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["toInsert"],
                M.call (|
                  "shift_left_dynamic",
                  [
                    M.get (| "shiftBits" |);
                    M.get (| "toInsert" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "and",
                  [
                    M.get (| "value" |);
                    M.call (|
                      "not",
                      [
                        M.get (| "mask" |)
                      ]
                    |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["result"],
                M.call (|
                  "or",
                  [
                    M.get (| "value" |);
                    M.call (|
                      "and",
                      [
                        M.get (| "toInsert" |);
                        M.get (| "mask" |)
                      ]
                    |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_function_internal_nonpayable_uint256_returns_uint256_to_function_internal_nonpayable_uint256_returns_uint",
          ["functionId"],
          ["outFunctionId"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["outFunctionId"],
                M.get (| "functionId" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "prepare_store_function_internal_nonpayable_uint256_returns_uint",
          ["value"],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                M.get (| "value" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "update_storage_value_function_internal_nonpayable_uint256_returns_uint256_to_function_internal_nonpayable_uint256_returns_uint",
          ["slot"; "offset"; "value"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["convertedValue"],
                Some (M.call (|
                  "convert_function_internal_nonpayable_uint256_returns_uint256_to_function_internal_nonpayable_uint256_returns_uint",
                  [
                    M.get (| "value" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "sstore",
                [
                  M.get (| "slot" |);
                  M.call (|
                    "update_byte_slice_dynamic8",
                    [
                      M.call (|
                        "sload",
                        [
                          M.get (| "slot" |)
                        ]
                      |);
                      M.get (| "offset" |);
                      M.call (|
                        "prepare_store_function_internal_nonpayable_uint256_returns_uint",
                        [
                          M.get (| "convertedValue" |)
                        ]
                      |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "storage_set_to_zero_function_internal_nonpayable_uint256_returns_uint",
          ["slot"; "offset"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["zero"],
                Some (M.call (|
                  "zero_value_for_split_function_internal_nonpayable_uint256_returns_uint",
                  []
                |))
              |) in
            let _ :=
              M.call (|
                "update_storage_value_function_internal_nonpayable_uint256_returns_uint256_to_function_internal_nonpayable_uint256_returns_uint",
                [
                  M.get (| "slot" |);
                  M.get (| "offset" |);
                  M.get (| "zero" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "zero_value_for_split_function_internal_nonpayable_returns",
          [],
          ["ret"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["ret"],
                [Literal.number 0]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_f",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "storage_set_to_zero_function_external_nonpayable_uint256_returns_uint",
                [
                  [Literal.number 0x00];
                  [Literal.number 0]
                ]
              |) in
            let _ :=
              M.assign (|
                ["_1_functionIdentifier"],
                Some (M.call (|
                  "read_from_storage_split_offset_function_internal_nonpayable_uint256_returns_uint",
                  [
                    [Literal.number 0x00]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_30_functionIdentifier"],
                Some (M.get (| "_1_functionIdentifier" |))
              |) in
            let _ :=
              M.assign (|
                ["var_a_functionIdentifier"],
                Some (M.get (| "expr_30_functionIdentifier" |))
              |) in
            let _ :=
              M.assign (|
                ["_2_functionIdentifier"],
                Some (M.call (|
                  "zero_value_for_split_function_internal_nonpayable_uint256_returns_uint",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_a_functionIdentifier"],
                M.get (| "_2_functionIdentifier" |)
              |) in
            let _ :=
              M.call (|
                "storage_set_to_zero_function_internal_nonpayable_uint256_returns_uint",
                [
                  [Literal.number 0x00];
                  [Literal.number 24]
                ]
              |) in
            let _ :=
              M.assign (|
                ["expr_functionIdentifier"],
                Some ([Literal.number 1])
              |) in
            let _ :=
              M.assign (|
                ["var_c_functionIdentifier"],
                Some (M.get (| "expr_functionIdentifier" |))
              |) in
            let _ :=
              M.assign (|
                ["_3_functionIdentifier"],
                Some (M.call (|
                  "zero_value_for_split_function_internal_nonpayable_returns",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_c_functionIdentifier"],
                M.get (| "_3_functionIdentifier" |)
              |) in
            let _ :=
              M.assign (|
                ["var_g_functionIdentifier"],
                None
              |) in
            let _ :=
              M.assign (|
                ["zero_function_internal_nonpayable_uint256_returns_uint256_functionIdentifier"],
                Some (M.call (|
                  "zero_value_for_split_function_internal_nonpayable_uint256_returns_uint",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_g_functionIdentifier"],
                M.get (| "zero_function_internal_nonpayable_uint256_returns_uint256_functionIdentifier" |)
              |) in
            let _ :=
              M.assign (|
                ["_functionIdentifier"],
                Some (M.call (|
                  "zero_value_for_split_function_internal_nonpayable_uint256_returns_uint",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_g_functionIdentifier"],
                M.get (| "_functionIdentifier" |)
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a2646970667358221220236536236fcc76ca5f5bb9d78914fcc879e7baeb86d8b2288a39986a22d5511b64736f6c634300081b0033".
  End C_61_deployed.
End C_61.
