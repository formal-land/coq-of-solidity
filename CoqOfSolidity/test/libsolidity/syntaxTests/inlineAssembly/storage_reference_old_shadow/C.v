(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_30.
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
                [Literal.string "435f33305f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f33305f6465706c6f796564"]
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
                [Literal.string "435f33305f6465706c6f796564"]
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

  Module C_30_deployed.
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
            "fun",
            []
          |) in
        let _ :=
          M.call (|
            "stop",
            []
          |) in
        tt in
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
          "cleanup_rational_by",
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
          "convert_rational_by_to_uint256",
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
                          "cleanup_rational_by",
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
          "convert_array_array_uint256_dyn_storage_to_array_uint256_dyn_ptr",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.get (| "value" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "panic_error_0x32",
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
                  [Literal.number 0x32]
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
          "array_length_array_uint256_dyn_storage_ptr",
          ["value"],
          ["length"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["length"],
                M.call (|
                  "sload",
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
          "array_dataslot_array_uint256_dyn_storage_ptr",
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
          "storage_array_index_access_uint256_dyn_ptr",
          ["array"; "index"],
          ["slot";
      "offset"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["arrayLength"],
                Some (M.call (|
                  "array_length_array_uint256_dyn_storage_ptr",
                  [
                    M.get (| "array" |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "lt",
                      [
                        M.get (| "index" |);
                        M.get (| "arrayLength" |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x32",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.assign (|
                ["dataArea"],
                Some (M.call (|
                  "array_dataslot_array_uint256_dyn_storage_ptr",
                  [
                    M.get (| "array" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["slot"],
                M.call (|
                  "add",
                  [
                    M.get (| "dataArea" |);
                    M.call (|
                      "mul",
                      [
                        M.get (| "index" |);
                        [Literal.number 1]
                      ]
                    |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["offset"],
                [Literal.number 0]
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
          "fun",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["_1_slot"],
                Some ([Literal.number 0x00])
              |) in
            let _ :=
              M.assign (|
                ["expr_19_slot"],
                Some (M.get (| "_1_slot" |))
              |) in
            let _ :=
              M.assign (|
                ["var_y_slot"],
                Some (M.call (|
                  "convert_array_array_uint256_dyn_storage_to_array_uint256_dyn_ptr",
                  [
                    M.get (| "expr_19_slot" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some ([Literal.number 0x02])
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.call (|
                  "convert_rational_by_to_uint256",
                  [
                    M.get (| "expr" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["_slot"],
                Some (M.get (| "var_y_slot" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_slot"],
                Some (M.get (| "_slot" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some ([Literal.number 0x00])
              |) in
            let _ :=
              M.assign (|
                ["_2"; "_3"],
                Some (M.call (|
                  "storage_array_index_access_uint256_dyn_ptr",
                  [
                    M.get (| "expr_slot" |);
                    M.get (| "expr_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "update_storage_value_uint256_to_uint256",
                [
                  M.get (| "_2" |);
                  M.get (| "_3" |);
                  M.get (| "_1" |)
                ]
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a2646970667358221220dbc6cc4ede99fe38049be4703a0ca372d7aa79aab1d8537d17dc0d7b82425bd364736f6c634300081b0033".
  End C_30_deployed.
End C_30.
