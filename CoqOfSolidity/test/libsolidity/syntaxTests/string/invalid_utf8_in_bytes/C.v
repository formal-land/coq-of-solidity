(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_10.
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
        M.call (|
          "constructor_C",
          []
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
                [Literal.string "435f31305f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f31305f6465706c6f796564"]
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
                [Literal.string "435f31305f6465706c6f796564"]
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
    let _ :=
      M.function (|
        "panic_error_0x22",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
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
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 4];
                [Literal.number 0x22]
              ]
            |) in
          let _ :=
            M.call (|
              "revert",
              [
                [Literal.number 0];
                [Literal.number 0x24]
              ]
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "extract_byte_array_length",
        ["data"],
        ["length"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["length"],
              M.call (|
                "div",
                [
                  M.get (| "data" |);
                  [Literal.number 2]
                ]
              |)
            |) in
          let _ :=
            M.assign (|
              ["outOfPlaceEncoding"],
              Some (M.call (|
                "and",
                [
                  M.get (| "data" |);
                  [Literal.number 1]
                ]
              |))
            |) in
          let _ :=
            M.if_ (|
              M.call (|
                "iszero",
                [
                  M.get (| "outOfPlaceEncoding" |)
                ]
              |),
              ltac:(M.monadic (
                let _ :=
                  M.declare (|
                    ["length"],
                    M.call (|
                      "and",
                      [
                        M.get (| "length" |);
                        [Literal.number 0x7f]
                      ]
                    |)
                  |) in
                tt
              ))
            |) in
          let _ :=
            M.if_ (|
              M.call (|
                "eq",
                [
                  M.get (| "outOfPlaceEncoding" |);
                  M.call (|
                    "lt",
                    [
                      M.get (| "length" |);
                      [Literal.number 32]
                    ]
                  |)
                ]
              |),
              ltac:(M.monadic (
                let _ :=
                  M.call (|
                    "panic_error_0x22",
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
        "array_dataslot_bytes_storage_ptr",
        ["ptr"],
        ["data"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["data"],
              M.get (| "ptr" |)
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 0];
                M.get (| "ptr" |)
              ]
            |) in
          let _ :=
            M.declare (|
              ["data"],
              M.call (|
                "keccak256",
                [
                  [Literal.number 0];
                  [Literal.number 0x20]
                ]
              |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "divide_by_ceil",
        ["value"],
        ["result"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["result"],
              M.call (|
                "div",
                [
                  M.call (|
                    "add",
                    [
                      M.get (| "value" |);
                      [Literal.number 31]
                    ]
                  |);
                  [Literal.number 32]
                ]
              |)
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
        "update_byte_slice_dynamic32",
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
                    "not",
                    [
                      [Literal.number 0]
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
        "cleanup_uint256",
        ["value"],
        ["cleaned"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["cleaned"],
              M.get (| "value" |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "identity",
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
        "convert_uint256_to_uint256",
        ["value"],
        ["converted"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["converted"],
              M.call (|
                "cleanup_uint256",
                [
                  M.call (|
                    "identity",
                    [
                      M.call (|
                        "cleanup_uint256",
                        [
                          M.get (| "value" |)
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
        "prepare_store_uint256",
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
        "update_storage_value_uint256_to_uint256",
        ["slot"; "offset"; "value"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["convertedValue"],
              Some (M.call (|
                "convert_uint256_to_uint256",
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
                  "update_byte_slice_dynamic32",
                  [
                    M.call (|
                      "sload",
                      [
                        M.get (| "slot" |)
                      ]
                    |);
                    M.get (| "offset" |);
                    M.call (|
                      "prepare_store_uint256",
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
        "zero_value_for_split_uint256",
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
        "storage_set_to_zero_uint256",
        ["slot"; "offset"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["zero"],
              Some (M.call (|
                "zero_value_for_split_uint256",
                []
              |))
            |) in
          let _ :=
            M.call (|
              "update_storage_value_uint256_to_uint256",
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
        "clear_storage_range_bytes1",
        ["start"; "end"],
        [],
        ltac:(M.monadic (
          let _ :=
            let _ :=
              tt in
            M.for_ (|
              M.call (|
                "lt",
                [
                  M.get (| "start" |);
                  M.get (| "end" |)
                ]
              |),
              ltac:(M.monadic (
                let _ :=
                  M.declare (|
                    ["start"],
                    M.call (|
                      "add",
                      [
                        M.get (| "start" |);
                        [Literal.number 1]
                      ]
                    |)
                  |) in
                tt
              )),
              ltac:(M.monadic (
                let _ :=
                  M.call (|
                    "storage_set_to_zero_uint256",
                    [
                      M.get (| "start" |);
                      [Literal.number 0]
                    ]
                  |) in
                tt
              ))
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "clean_up_bytearray_end_slots_bytes_storage_ptr",
        ["array"; "len"; "startIndex"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.get (| "len" |);
                  [Literal.number 31]
                ]
              |),
              ltac:(M.monadic (
                let _ :=
                  M.assign (|
                    ["dataArea"],
                    Some (M.call (|
                      "array_dataslot_bytes_storage_ptr",
                      [
                        M.get (| "array" |)
                      ]
                    |))
                  |) in
                let _ :=
                  M.assign (|
                    ["deleteStart"],
                    Some (M.call (|
                      "add",
                      [
                        M.get (| "dataArea" |);
                        M.call (|
                          "divide_by_ceil",
                          [
                            M.get (| "startIndex" |)
                          ]
                        |)
                      ]
                    |))
                  |) in
                let _ :=
                  M.if_ (|
                    M.call (|
                      "lt",
                      [
                        M.get (| "startIndex" |);
                        [Literal.number 32]
                      ]
                    |),
                    ltac:(M.monadic (
                      let _ :=
                        M.declare (|
                          ["deleteStart"],
                          M.get (| "dataArea" |)
                        |) in
                      tt
                    ))
                  |) in
                let _ :=
                  M.call (|
                    "clear_storage_range_bytes1",
                    [
                      M.get (| "deleteStart" |);
                      M.call (|
                        "add",
                        [
                          M.get (| "dataArea" |);
                          M.call (|
                            "divide_by_ceil",
                            [
                              M.get (| "len" |)
                            ]
                          |)
                        ]
                      |)
                    ]
                  |) in
                tt
              ))
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "copy_literal_to_storage_bd3ca26b7b920cf378779e8e53dba5df6da21e2348f6f92a55377fb12340d09b",
        ["slot"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["oldLen"],
              Some (M.call (|
                "extract_byte_array_length",
                [
                  M.call (|
                    "sload",
                    [
                      M.get (| "slot" |)
                    ]
                  |)
                ]
              |))
            |) in
          let _ :=
            M.call (|
              "clean_up_bytearray_end_slots_bytes_storage_ptr",
              [
                M.get (| "slot" |);
                M.get (| "oldLen" |);
                [Literal.number 2]
              ]
            |) in
          let _ :=
            M.call (|
              "sstore",
              [
                M.get (| "slot" |);
                M.call (|
                  "add",
                  [
                    M.call (|
                      "shl",
                      [
                        [Literal.number 253];
                        [Literal.number 5]
                      ]
                    |);
                    [Literal.number 4]
                  ]
                |)
              ]
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "update_storage_value_offsett_stringliteral_bd3c_to_bytes",
        ["slot"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.call (|
              "copy_literal_to_storage_bd3ca26b7b920cf378779e8e53dba5df6da21e2348f6f92a55377fb12340d09b",
              [
                M.get (| "slot" |)
              ]
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
                  [Literal.number 0];
                  M.get (| "value" |)
                ]
              |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "update_byte_slice_shift",
        ["value"; "toInsert"],
        ["result"],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["mask"],
              Some (M.call (|
                "not",
                [
                  [Literal.number 0]
                ]
              |))
            |) in
          let _ :=
            M.declare (|
              ["toInsert"],
              M.call (|
                "shift_left",
                [
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
        "convert_stringliteral_bd3c_to_bytes32",
        [],
        ["converted"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["converted"],
              M.call (|
                "shl",
                [
                  [Literal.number 253];
                  [Literal.number 5]
                ]
              |)
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
                  [Literal.number 0];
                  M.get (| "value" |)
                ]
              |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "prepare_store_bytes32",
        ["value"],
        ["ret"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["ret"],
              M.call (|
                "shift_right_unsigned",
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
        "update_storage_value_offsett_stringliteral_bd3c_to_bytes32",
        ["slot"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["convertedValue"],
              Some (M.call (|
                "convert_stringliteral_bd3c_to_bytes32",
                []
              |))
            |) in
          let _ :=
            M.call (|
              "sstore",
              [
                M.get (| "slot" |);
                M.call (|
                  "update_byte_slice_shift",
                  [
                    M.call (|
                      "sload",
                      [
                        M.get (| "slot" |)
                      ]
                    |);
                    M.call (|
                      "prepare_store_bytes32",
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
        "constructor_C",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
            M.call (|
              "update_storage_value_offsett_stringliteral_bd3c_to_bytes",
              [
                [Literal.number 0x00]
              ]
            |) in
          let _ :=
            M.call (|
              "update_storage_value_offsett_stringliteral_bd3c_to_bytes32",
              [
                [Literal.number 0x01]
              ]
            |) in
          let _ :=
            M.call (|
              "update_storage_value_offsett_stringliteral_bd3c_to_bytes",
              [
                [Literal.number 0x02]
              ]
            |) in
          tt
        ))
      |) in
    tt
  )).

  Module C_10_deployed.
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
          M.call (|
            "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74",
            []
          |) in
        tt in
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
      tt
    )).

    Definition data : string :=
      "a2646970667358221220fceae7378c9135298631f3d75ea9695071a12a553c46ccc2bed98310f24343ab64736f6c634300081b0033".
  End C_10_deployed.
End C_10.
