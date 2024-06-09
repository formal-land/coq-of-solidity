(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_74.
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
                [Literal.number 0xc0]
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
                [Literal.string "435f37345f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f37345f6465706c6f796564"]
              ]
            |)
          ]
        |) in
      let _ :=
        M.call (|
          "setimmutable",
          [
            M.get (| "_1" |);
            [Literal.string "35"];
            M.call (|
              "mload",
              [
                [Literal.number 128]
              ]
            |)
          ]
        |) in
      let _ :=
        M.call (|
          "setimmutable",
          [
            M.get (| "_1" |);
            [Literal.string "3130"];
            M.call (|
              "mload",
              [
                [Literal.number 160]
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
                [Literal.string "435f37345f6465706c6f796564"]
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
        "convert_rational_4_by_1_to_uint256",
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
        "read_from_memoryt_uint256",
        ["ptr"],
        ["returnValue"],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["value"],
              Some (M.call (|
                "cleanup_uint256",
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
        "checked_add_uint256",
        ["x"; "y"],
        ["sum"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["x"],
              M.call (|
                "cleanup_uint256",
                [
                  M.get (| "x" |)
                ]
              |)
            |) in
          let _ :=
            M.declare (|
              ["y"],
              M.call (|
                "cleanup_uint256",
                [
                  M.get (| "y" |)
                ]
              |)
            |) in
          let _ :=
            M.declare (|
              ["sum"],
              M.call (|
                "add",
                [
                  M.get (| "x" |);
                  M.get (| "y" |)
                ]
              |)
            |) in
          let _ :=
            M.if_ (|
              M.call (|
                "gt",
                [
                  M.get (| "x" |);
                  M.get (| "sum" |)
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
            M.assign (|
              ["expr"],
              Some ([Literal.number 0x04])
            |) in
          let _ :=
            M.assign (|
              ["_1"],
              Some (M.call (|
                "convert_rational_4_by_1_to_uint256",
                [
                  M.get (| "expr" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_2"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "_2" |);
                  M.get (| "_1" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_3"],
              Some (M.get (| "expr_1" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_3" |)
              ]
            |) in
          let _ :=
            M.assign (|
              ["_4"],
              Some (M.get (| "expr_1" |))
            |) in
          let _ :=
            M.call (|
              "constructor_B",
              [
                M.get (| "_4" |)
              ]
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
        "convert_rational_8_by_1_to_uint256",
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
        "constructor_B",
        ["var"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["expr"],
              Some ([Literal.number 0x08])
            |) in
          let _ :=
            M.assign (|
              ["_1"],
              Some (M.call (|
                "convert_rational_8_by_1_to_uint256",
                [
                  M.get (| "expr" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_2"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "_2" |);
                  M.get (| "_1" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_3"],
              Some (M.get (| "expr_1" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_3" |)
              ]
            |) in
          let _ :=
            M.assign (|
              ["_4"],
              Some (M.get (| "expr_1" |))
            |) in
          let _ :=
            M.call (|
              "constructor_A",
              [
                M.get (| "_4" |)
              ]
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "cleanup_rational_1_by",
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
        "convert_rational_1_by_1_to_uint256",
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
                        "cleanup_rational_1_by",
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
        "cleanup_rational_2_by",
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
        "convert_rational_2_by_1_to_uint256",
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
                        "cleanup_rational_2_by",
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
        "cleanup_rational_16_by",
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
        "convert_rational_16_by_1_to_uint256",
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
                        "cleanup_rational_16_by",
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
        "modifier_m_18",
        ["var_"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["expr"],
              Some ([Literal.number 0x10])
            |) in
          let _ :=
            M.assign (|
              ["_1"],
              Some (M.call (|
                "convert_rational_16_by_1_to_uint256",
                [
                  M.get (| "expr" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_2"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "_2" |);
                  M.get (| "_1" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_3"],
              Some (M.get (| "expr_1" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_3" |)
              ]
            |) in
          let _ :=
            M.call (|
              "modifier_m",
              [
                M.get (| "var_" |)
              ]
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
        "convert_rational_32_by_1_to_uint256",
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
        "modifier_m",
        ["var"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["expr"],
              Some ([Literal.number 0x20])
            |) in
          let _ :=
            M.assign (|
              ["_1"],
              Some (M.call (|
                "convert_rational_32_by_1_to_uint256",
                [
                  M.get (| "expr" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_2"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "_2" |);
                  M.get (| "_1" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_3"],
              Some (M.get (| "expr_1" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_3" |)
              ]
            |) in
          let _ :=
            M.call (|
              "fun_inner",
              [
                M.get (| "var" |)
              ]
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "cleanup_rational_64_by",
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
        "convert_t_rational_by_to_t_uint256",
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
                        "cleanup_rational_64_by",
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
        "fun_inner",
        ["var"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["expr"],
              Some ([Literal.number 0x40])
            |) in
          let _ :=
            M.assign (|
              ["_1"],
              Some (M.call (|
                "convert_t_rational_by_to_t_uint256",
                [
                  M.get (| "expr" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_2"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "_2" |);
                  M.get (| "_1" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_3"],
              Some (M.get (| "expr_1" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_3" |)
              ]
            |) in
          let _ :=
            M.assign (|
              ["expr_2"],
              Some ([Literal.number 0x80])
            |) in
          let _ :=
            M.assign (|
              ["_4"],
              Some (M.call (|
                "convert_rational_by_to_uint256",
                [
                  M.get (| "expr_2" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_5"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_3"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "_5" |);
                  M.get (| "_4" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_6"],
              Some (M.get (| "expr_3" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_6" |)
              ]
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "constructor_A",
        ["var"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["_1"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr"],
              Some (M.get (| "_1" |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some ([Literal.number 0x01])
            |) in
          let _ :=
            M.assign (|
              ["expr_2"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "expr" |);
                  M.call (|
                    "convert_rational_1_by_1_to_uint256",
                    [
                      M.get (| "expr_1" |)
                    ]
                  |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_2"],
              Some (M.get (| "expr_2" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_2" |)
              ]
            |) in
          let _ :=
            M.assign (|
              ["expr_3"],
              Some ([Literal.number 0x02])
            |) in
          let _ :=
            M.assign (|
              ["_3"],
              Some (M.call (|
                "convert_rational_2_by_1_to_uint256",
                [
                  M.get (| "expr_3" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_4"],
              Some (M.call (|
                "read_from_memoryt_uint256",
                [
                  [Literal.number 128]
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_4"],
              Some (M.call (|
                "checked_add_uint256",
                [
                  M.get (| "_4" |);
                  M.get (| "_3" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_5"],
              Some (M.get (| "expr_4" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 128];
                M.get (| "_5" |)
              ]
            |) in
          let _ :=
            M.assign (|
              ["_6"],
              Some (M.get (| "expr_4" |))
            |) in
          let _ :=
            M.call (|
              "mstore",
              [
                [Literal.number 160];
                M.get (| "_6" |)
              ]
            |) in
          let _ :=
            M.call (|
              "modifier_m_18",
              [
                M.get (| "var" |)
              ]
            |) in
          tt
        ))
      |) in
    tt
  )).

  Module C_74_deployed.
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
                      Some (Literal.number 0x6d4ce63c),
                      ltac:(M.monadic (
                        let _ :=
                          M.call (|
                            "external_fun_get",
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
          "external_fun_get",
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
                  "fun_get",
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
          "fun_get",
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
                ["_1"],
                Some (M.call (|
                  "loadimmutable",
                  [
                    [Literal.string "35"]
                  ]
                |))
              |) in
            let _ :=
              M.assign (|
                ["expr"],
                Some (M.get (| "_1" |))
              |) in
            let _ :=
              M.declare (|
                ["var"],
                M.get (| "expr" |)
              |) in
            let _ :=
              M.leave (||) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a2646970667358221220d660a649edd5232f6e577162ecc233705084d603bbe647a0c6f54f4ddb70d90d64736f6c634300081b0033".
  End C_74_deployed.
End C_74.
