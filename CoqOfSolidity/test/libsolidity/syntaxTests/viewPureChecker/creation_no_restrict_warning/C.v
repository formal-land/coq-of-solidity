(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module C_11.
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
                [Literal.string "435f31315f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "435f31315f6465706c6f796564"]
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
                [Literal.string "435f31315f6465706c6f796564"]
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

  Module C_11_deployed.
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
          "revert_forward",
          [],
          [],
          ltac:(M.monadic (
            let _ :=
              M.assign (|
                ["pos"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.call (|
                "returndatacopy",
                [
                  M.get (| "pos" |);
                  [Literal.number 0];
                  M.call (|
                    "returndatasize",
                    []
                  |)
                ]
              |) in
            let _ :=
              M.call (|
                "revert",
                [
                  M.get (| "pos" |);
                  M.call (|
                    "returndatasize",
                    []
                  |)
                ]
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
              M.assign (|
                ["_1"],
                Some (M.call (|
                  "allocate_unbounded",
                  []
                |))
              |) in
            let _ :=
              M.assign (|
                ["_2"],
                Some (M.call (|
                  "add",
                  [
                    M.get (| "_1" |);
                    M.call (|
                      "datasize",
                      [
                        [Literal.string "445f31"]
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
                        M.get (| "_2" |);
                        [Literal.number 0xffffffffffffffff]
                      ]
                    |);
                    M.call (|
                      "lt",
                      [
                        M.get (| "_2" |);
                        M.get (| "_1" |)
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
                "datacopy",
                [
                  M.get (| "_1" |);
                  M.call (|
                    "dataoffset",
                    [
                      [Literal.string "445f31"]
                    ]
                  |);
                  M.call (|
                    "datasize",
                    [
                      [Literal.string "445f31"]
                    ]
                  |)
                ]
              |) in
            let _ :=
              M.declare (|
                ["_2"],
                M.call (|
                  "abi_encode_tuple",
                  [
                    M.get (| "_2" |)
                  ]
                |)
              |) in
            let _ :=
              M.assign (|
                ["expr_address"],
                Some (M.call (|
                  "create",
                  [
                    [Literal.number 0];
                    M.get (| "_1" |);
                    M.call (|
                      "sub",
                      [
                        M.get (| "_2" |);
                        M.get (| "_1" |)
                      ]
                    |)
                  ]
                |))
              |) in
            let _ :=
              M.if_ (|
                M.call (|
                  "iszero",
                  [
                    M.get (| "expr_address" |)
                  ]
                |),
                ltac:(M.monadic (
                  let _ :=
                    M.call (|
                      "revert_forward",
                      []
                    |) in
                  tt
                ))
              |) in
            tt
          ))
        |) in
      tt
    )).

    Module D_1.
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
                    [Literal.string "445f315f6465706c6f796564"]
                  ]
                |);
                M.call (|
                  "datasize",
                  [
                    [Literal.string "445f315f6465706c6f796564"]
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
                    [Literal.string "445f315f6465706c6f796564"]
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

      Module D_1_deployed.
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
          "a2646970667358221220be15aa08e90289200260525d972ca3c057f71b908413c9c6068397f7d36781a864736f6c634300081b0033".
      End D_1_deployed.
    End D_1.

    Definition data : string :=
      "a264697066735822122005e2d7361df54988fa741969c14ad6914fdfa2bed3e63abbd1a10c1b75ffa44264736f6c634300081b0033".
  End C_11_deployed.
End C_11.
