(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_35.
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
                [Literal.string "435f33355f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f33355f6465706c6f796564"]
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
                [Literal.string "435f33355f6465706c6f796564"]
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

  Module C_35_deployed.
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
          "abi_encode_uint256_to_uint256",
          ["value"; "pos"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "pos" |);
                  M.call (|
                    "cleanup_uint256",
                    [
                      M.get (| "value" |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_uint256",
          ["headStart"; "value0"],
          ["tail"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["tail"],
                M.call (|
                  "add",
                  [
                    M.get (| "headStart" |);
                    [Literal.number 32]
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "abi_encode_uint256_to_uint256",
                [
                  M.get (| "value0" |);
                  M.call (|
                    "add",
                    [
                      M.get (| "headStart" |);
                      [Literal.number 0]
                    ]
                  |)
                ]
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
              M.assign (|
                ["ret"],
                Some (M.call (|
                  "fun_f",
                  []
                |))
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
                  "abi_encode_uint256",
                  [
                    M.get (| "memPos" |);
                    M.get (| "ret" |)
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
          "cleanup_uint8",
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
                    [Literal.number 0xff]
                  ]
                |)
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
          "convert_rational_by_to_uint8",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint8",
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
          "cleanup_t_rational_by",
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
          "cleanup_uint16",
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
                    [Literal.number 0xffff]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_rational_by_to_uint16",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint16",
                  [
                    M.call (|
                      "identity",
                      [
                        M.call (|
                          "cleanup_t_rational_by",
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
          "cleanup_t_rational_by_1",
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
          "cleanup_uint32",
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
                    [Literal.number 0xffffffff]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_rational_by_to_uint32",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint32",
                  [
                    M.call (|
                      "identity",
                      [
                        M.call (|
                          "cleanup_t_rational_by_1",
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
          "round_up_to_mul_of",
          ["value"],
          ["result"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["result"],
                M.call (|
                  "and",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "value" |);
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
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "panic_error_0x41",
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
                  [Literal.number 0x41]
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
          "finalize_allocation",
          ["memPtr"; "size"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["newFreePtr"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "memPtr" |);
                    M.call (|
                      "round_up_to_mul_of",
                      [
                        M.get (| "size" |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "or",
                  [
                    M.call (|
                      "gt",
                      [
                        M.get (| "newFreePtr" |);
                        [Literal.number 0xffffffffffffffff]
                      ]
                    |);
                    M.call (|
                      "lt",
                      [
                        M.get (| "newFreePtr" |);
                        M.get (| "memPtr" |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x41",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.call (|
                "mstore",
                [
                  [Literal.number 64];
                  M.get (| "newFreePtr" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "allocate_memory",
          ["size"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "allocate_unbounded",
                  []
                |)
              |) in
            let _ :=
              M.call (|
                "finalize_allocation",
                [
                  M.get (| "memPtr" |);
                  M.get (| "size" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "array_allocation_size_array_uint32",
          ["length"],
          ["size"],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "gt",
                  [
                    M.get (| "length" |);
                    [Literal.number 0xffffffffffffffff]
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x41",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.declare (|
                ["size"],
                M.call (|
                  "mul",
                  [
                    M.get (| "length" |);
                    [Literal.number 0x20]
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "allocate_memory_array_array_uint32",
          ["length"],
          ["memPtr"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["allocSize"],
                Some (M.call (|
                  "array_allocation_size_array_uint32",
                  [
                    M.get (| "length" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["memPtr"],
                M.call (|
                  "allocate_memory",
                  [
                    M.get (| "allocSize" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_uint8_to_uint32",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint32",
                  [
                    M.call (|
                      "identity",
                      [
                        M.call (|
                          "cleanup_uint8",
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
          "write_to_memory_uint32",
          ["memPtr"; "value"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "memPtr" |);
                  M.call (|
                    "cleanup_uint32",
                    [
                      M.get (| "value" |)
                    ]
                  |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_uint16_to_uint32",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_uint32",
                  [
                    M.call (|
                      "identity",
                      [
                        M.call (|
                          "cleanup_uint16",
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
          "array_length_array_uint32",
          ["value"],
          ["length"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["length"],
                [Literal.number 0x03]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "memory_array_index_access_uint32",
          ["baseRef"; "index"],
          ["addr"],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "lt",
                      [
                        M.get (| "index" |);
                        M.call (|
                          "array_length_array_uint32",
                          [
                            M.get (| "baseRef" |)
                          ]
                        |)
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
                ["offset"],
                Some (M.call (|
                  "mul",
                  [
                    M.get (| "index" |);
                    [Literal.number 32]
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["addr"],
                M.call (|
                  "add",
                  [
                    M.get (| "baseRef" |);
                    M.get (| "offset" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_rational_by_1",
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
                          "cleanup_rational_by_1",
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
          "read_from_memoryt_uint32",
          ["ptr"],
          ["returnValue"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["value"],
                Some (M.call (|
                  "cleanup_uint32",
                  [
                    M.call (|
                      "mload",
                      [
                        M.get (| "ptr" |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["returnValue"],
                M.get (| "value" |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "convert_uint32_to_uint256",
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
                          "cleanup_uint32",
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
          "fun_f",
          [],
          ["var"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["zero_uint256"],
                Some (M.call (|
                  "zero_value_for_split_uint256",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.get (| "zero_uint256" |)
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some ([Literal.number 0x07])
              |) in
            let _ :=
              M.assign (|
                ["var_x"],
                Some (M.call (|
                  "convert_rational_by_to_uint8",
                  [
                    M.get (| "expr" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some ([Literal.number 0x08])
              |) in
            let _ :=
              M.assign (|
                ["var_y"],
                Some (M.call (|
                  "convert_rational_by_to_uint16",
                  [
                    M.get (| "expr_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some ([Literal.number 0x09])
              |) in
            let _ :=
              M.assign (|
                ["var_z"],
                Some (M.call (|
                  "convert_rational_by_to_uint32",
                  [
                    M.get (| "expr_2" |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_26_mpos"],
                Some (M.call (|
                  "allocate_memory_array_array_uint32",
                  [
                    [Literal.number 3]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.get (| "var_x" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_3"],
                Some (M.get (| "_1" |))
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.call (|
                  "convert_uint8_to_uint32",
                  [
                    M.get (| "expr_3" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "write_to_memory_uint32",
                [
                  M.call (|
                    "add",
                    [
                      M.get (| "expr_26_mpos" |);
                      [Literal.number 0]
                    ]
                  |);
                  M.get (| "_2" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["_3"],
                Some (M.get (| "var_y" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_4"],
                Some (M.get (| "_3" |))
              |) in
            let _ :=
              M.assign (|
                ["_4"],
                Some (M.call (|
                  "convert_uint16_to_uint32",
                  [
                    M.get (| "expr_4" |)
                  ]
                |))
              |) in
            let _ :=
              M.call (|
                "write_to_memory_uint32",
                [
                  M.call (|
                    "add",
                    [
                      M.get (| "expr_26_mpos" |);
                      [Literal.number 32]
                    ]
                  |);
                  M.get (| "_4" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["_5"],
                Some (M.get (| "var_z" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_5"],
                Some (M.get (| "_5" |))
              |) in
            let _ :=
              M.call (|
                "write_to_memory_uint32",
                [
                  M.call (|
                    "add",
                    [
                      M.get (| "expr_26_mpos" |);
                      [Literal.number 64]
                    ]
                  |);
                  M.get (| "expr_5" |)
                ]
              |) in
            let _ :=
              M.assign (|
                ["var_ending_mpos"],
                Some (M.get (| "expr_26_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["_mpos"],
                Some (M.get (| "var_ending_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_mpos"],
                Some (M.get (| "_mpos" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_6"],
                Some ([Literal.number 0x01])
              |) in
            let _ :=
              M.assign (|
                ["_6"],
                Some (M.call (|
                  "read_from_memoryt_uint32",
                  [
                    M.call (|
                      "memory_array_index_access_uint32",
                      [
                        M.get (| "expr_mpos" |);
                        M.call (|
                          "convert_rational_by_to_uint256",
                          [
                            M.get (| "expr_6" |)
                          ]
                        |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr_7"],
                Some (M.get (| "_6" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_8"],
                Some (M.get (| "expr_7" |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.call (|
                  "convert_uint32_to_uint256",
                  [
                    M.get (| "expr_8" |)
                  ]
                |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a2646970667358221220658e19b384fe0d8601692c86ae7f36563e60fd421f9a011bb0d1c9a15a9b9b5864736f6c634300081b0033".
  End C_35_deployed.
End C_35.
