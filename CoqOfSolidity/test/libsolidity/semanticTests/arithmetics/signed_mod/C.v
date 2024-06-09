(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_46.
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
                [Literal.string "435f34365f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f34365f6465706c6f796564"]
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
                [Literal.string "435f34365f6465706c6f796564"]
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

  Module C_46_deployed.
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
                      Some (Literal.number 0x0afdb4ea),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_f",
                            []
                          |) in
                        tt
                      ))              );
                    (
                      Some (Literal.number 0xd48092f7),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_g",
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
          "cleanup_int256",
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
          "validator_revert_int256",
          ["value"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "eq",
                      [
                        M.get (| "value" |);
                        M.call (|
                          "cleanup_int256",
                          [
                            M.get (| "value" |)
                          ]
                        |)
                      ]
                    |)
                  ]
                |),
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
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode_int256",
          ["offset"; "end"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "calldataload",
                  [
                    M.get (| "offset" |)
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "validator_revert_int256",
                [
                  M.get (| "value" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode_int256t_int256",
          ["headStart"; "dataEnd"],
          ["value0";
      "value1"],
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
                    [Literal.number 64]
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
            let _ :=
              M.assign (|
                ["offset"],
                Some ([Literal.number 0])
              |) in
            let _ :=
              M.declare (|
                ["value0"],
                M.call (|
                  "abi_decode_int256",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "headStart" |);
                        M.get (| "offset" |)
                      ]
                    |);
                    M.get (| "dataEnd" |)
                  ]
                |)
              |) in
            let _ :=
              M.assign (|
                ["offset_1"],
                Some ([Literal.number 32])
              |) in
            let _ :=
              M.declare (|
                ["value1"],
                M.call (|
                  "abi_decode_int256",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "headStart" |);
                        M.get (| "offset_1" |)
                      ]
                    |);
                    M.get (| "dataEnd" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_encode_int256",
          ["value"; "pos"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.call (|
                "mstore",
                [
                  M.get (| "pos" |);
                  M.call (|
                    "cleanup_int256",
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
          "abi_encode_tuple_int256",
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
                "abi_encode_int256",
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
              M.assign (|
                ["param"; "param_1"],
                Some (M.call (|
                  "abi_decode_int256t_int256",
                  [
                    [Literal.number 4];
                    M.call (|
                      "calldatasize",
                      []
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["ret"],
                Some (M.call (|
                  "fun_f",
                  [
                    M.get (| "param" |);
                    M.get (| "param_1" |)
                  ]
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
                  "abi_encode_tuple_int256",
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
          "cleanup_bool",
          ["value"],
          ["cleaned"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["cleaned"],
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "iszero",
                      [
                        M.get (| "value" |)
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
          "validator_revert_bool",
          ["value"],
          [],
          ltac:(M.monadic (
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.call (|
                      "eq",
                      [
                        M.get (| "value" |);
                        M.call (|
                          "cleanup_bool",
                          [
                            M.get (| "value" |)
                          ]
                        |)
                      ]
                    |)
                  ]
                |),
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
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode_t_bool",
          ["offset"; "end"],
          ["value"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["value"],
                M.call (|
                  "calldataload",
                  [
                    M.get (| "offset" |)
                  ]
                |)
              |) in
            let _ :=
              M.call (|
                "validator_revert_bool",
                [
                  M.get (| "value" |)
                ]
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "abi_decode_bool",
          ["headStart"; "dataEnd"],
          ["value0"],
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
                    [Literal.number 32]
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
            let _ :=
              M.assign (|
                ["offset"],
                Some ([Literal.number 0])
              |) in
            let _ :=
              M.declare (|
                ["value0"],
                M.call (|
                  "abi_decode_t_bool",
                  [
                    M.call (|
                      "add",
                      [
                        M.get (| "headStart" |);
                        M.get (| "offset" |)
                      ]
                    |);
                    M.get (| "dataEnd" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "external_fun_g",
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
              M.assign (|
                ["param"],
                Some (M.call (|
                  "abi_decode_bool",
                  [
                    [Literal.number 4];
                    M.call (|
                      "calldatasize",
                      []
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["ret"],
                Some (M.call (|
                  "fun_g",
                  [
                    M.get (| "param" |)
                  ]
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
                  "abi_encode_tuple_int256",
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
          "zero_value_for_split_int256",
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
          "panic_error_0x12",
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
                  [Literal.number 0x12]
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
          "mod_int256",
          ["x"; "y"],
          ["r"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["x"],
                M.call (|
                  "cleanup_int256",
                  [
                    M.get (| "x" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["y"],
                M.call (|
                  "cleanup_int256",
                  [
                    M.get (| "y" |)
                  ]
                |)
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "y" |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x12",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.declare (|
                ["r"],
                M.call (|
                  "smod",
                  [
                    M.get (| "x" |);
                    M.get (| "y" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_f",
          ["var_a"; "var_b"],
          ["var"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["zero_t_int256"],
                Some (M.call (|
                  "zero_value_for_split_int256",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.get (| "zero_t_int256" |)
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.get (| "var_a" |))
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some (M.get (| "_1" |))
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.get (| "var_b" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "_2" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_2"],
                Some (M.call (|
                  "mod_int256",
                  [
                    M.get (| "expr" |);
                    M.get (| "expr_1" |)
                  ]
                |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.get (| "expr_2" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "cleanup_rational_minus_by",
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
          "convert_rational_minus_by_to_int256",
          ["value"],
          ["converted"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["converted"],
                M.call (|
                  "cleanup_int256",
                  [
                    M.call (|
                      "identity",
                      [
                        M.call (|
                          "cleanup_rational_minus_by",
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
          "wrapping_div_int256",
          ["x"; "y"],
          ["r"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["x"],
                M.call (|
                  "cleanup_int256",
                  [
                    M.get (| "x" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["y"],
                M.call (|
                  "cleanup_int256",
                  [
                    M.get (| "y" |)
                  ]
                |)
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "y" |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x12",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.declare (|
                ["r"],
                M.call (|
                  "sdiv",
                  [
                    M.get (| "x" |);
                    M.get (| "y" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "panic_error_0x11",
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
                  [Literal.number 0x11]
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
          "checked_div_int256",
          ["x"; "y"],
          ["r"],
          ltac:(M.monadic (
            let _ :=
              M.declare (|
                ["x"],
                M.call (|
                  "cleanup_int256",
                  [
                    M.get (| "x" |)
                  ]
                |)
              |) in
            let _ :=
              M.declare (|
                ["y"],
                M.call (|
                  "cleanup_int256",
                  [
                    M.get (| "y" |)
                  ]
                |)
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "y" |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x12",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "and",
                  [
                    M.call (|
                      "eq",
                      [
                        M.get (| "x" |);
                        M.call (|
                          "shl",
                          [
                            [Literal.number 255];
                            [Literal.number 1]
                          ]
                        |)
                      ]
                    |);
                    M.call (|
                      "eq",
                      [
                        M.get (| "y" |);
                        M.call (|
                          "sub",
                          [
                            [Literal.number 0];
                            [Literal.number 1]
                          ]
                        |)
                      ]
                    |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "panic_error_0x11",
                      []
                    |) in
                  tt
                ))
              |) in
            let _ :=
              M.declare (|
                ["r"],
                M.call (|
                  "sdiv",
                  [
                    M.get (| "x" |);
                    M.get (| "y" |)
                  ]
                |)
              |) in
            tt
          ))
        |) in
      let _ :=
        M.function (|
          "fun_g",
          ["var_check"],
          ["var_"],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["zero_int256"],
                Some (M.call (|
                  "zero_value_for_split_int256",
                  []
                |))
              |) in
            let _ :=
              M.declare (|
                ["var_"],
                M.get (| "zero_int256" |)
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some (M.call (|
                  "shl",
                  [
                    [Literal.number 255];
                    [Literal.number 1]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["var_x"],
                Some (M.get (| "expr" |))
              |) in
            let _ :=
              M.assign (|
                ["_1"],
                Some (M.get (| "var_check" |))
              |) in
            let _ :=
              M.assign (|
                ["expr_1"],
                Some (M.get (| "_1" |))
              |) in
            let _ :=
              M.switch (|
                M.get (| "expr_1" |),
                [
                  (
                    Some (Literal.number 0),
                    ltac:(M.monadic (
                      let _ :=
                        M.assign (|
                          ["_2"],
                          Some (M.get (| "var_x" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_2"],
                          Some (M.get (| "_2" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_3"],
                          Some (M.call (|
                            "not",
                            [
                              [Literal.number 0]
                            ]
                          |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_4"],
                          Some (M.call (|
                            "wrapping_div_int256",
                            [
                              M.get (| "expr_2" |);
                              M.call (|
                                "convert_rational_minus_by_to_int256",
                                [
                                  M.get (| "expr_3" |)
                                ]
                              |)
                            ]
                          |))
                        |) in
                      let _ :=
                        M.declare (|
                          ["var_"],
                          M.get (| "expr_4" |)
                        |) in
                      let _ :=
                        M.leave (||) in
                      tt
                    ))            );
                  (
                    None,
                    ltac:(M.monadic (
                      let _ :=
                        M.assign (|
                          ["_3"],
                          Some (M.get (| "var_x" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_5"],
                          Some (M.get (| "_3" |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_6"],
                          Some (M.call (|
                            "not",
                            [
                              [Literal.number 0]
                            ]
                          |))
                        |) in
                      let _ :=
                        M.assign (|
                          ["expr_7"],
                          Some (M.call (|
                            "checked_div_int256",
                            [
                              M.get (| "expr_5" |);
                              M.call (|
                                "convert_rational_minus_by_to_int256",
                                [
                                  M.get (| "expr_6" |)
                                ]
                              |)
                            ]
                          |))
                        |) in
                      let _ :=
                        M.declare (|
                          ["var_"],
                          M.get (| "expr_7" |)
                        |) in
                      let _ :=
                        M.leave (||) in
                      tt
                    ))            )          ]
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a26469706673582212207074cd08f7ddc2d846b0010dc2224b63fd41c39a30246bcfe26addc13d12584164736f6c634300081b0033".
  End C_46_deployed.
End C_46.
