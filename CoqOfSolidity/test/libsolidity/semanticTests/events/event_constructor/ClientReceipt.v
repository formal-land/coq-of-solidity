(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module ClientReceipt_23.
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
          "constructor_ClientReceipt",
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
                [Literal.string "436c69656e74526563656970745f32335f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "436c69656e74526563656970745f32335f6465706c6f796564"]
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
                [Literal.string "436c69656e74526563656970745f32335f6465706c6f796564"]
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
        "convert_stringliteral_4e03_to_bytes32",
        [],
        ["converted"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["converted"],
              M.call (|
                "shl",
                [
                  [Literal.number 232];
                  [Literal.number 6382179]
                ]
              |)
            |) in
          tt
        ))
      |) in
    let _ :=
      M.function (|
        "cleanup_uint160",
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
                  M.call (|
                    "sub",
                    [
                      M.call (|
                        "shl",
                        [
                          [Literal.number 160];
                          [Literal.number 1]
                        ]
                      |);
                      [Literal.number 1]
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
        "convert_uint160_to_uint160",
        ["value"],
        ["converted"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["converted"],
              M.call (|
                "cleanup_uint160",
                [
                  M.call (|
                    "identity",
                    [
                      M.call (|
                        "cleanup_uint160",
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
        "convert_uint160_to_address",
        ["value"],
        ["converted"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["converted"],
              M.call (|
                "convert_uint160_to_uint160",
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
        "convert_address_to_address",
        ["value"],
        ["converted"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["converted"],
              M.call (|
                "convert_uint160_to_address",
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
        "cleanup_bytes32",
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
        "convert_bytes32_to_bytes32",
        ["value"],
        ["converted"],
        ltac:(M.monadic (
          let _ :=
            M.declare (|
              ["converted"],
              M.call (|
                "cleanup_bytes32",
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
        "abi_encode_rational_by",
        ["value"; "pos"],
        [],
        ltac:(M.monadic (
          let _ :=
            M.call (|
              "mstore",
              [
                M.get (| "pos" |);
                M.call (|
                  "convert_rational_by_to_uint256",
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
        "abi_encode_tuple_rational_by",
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
              "abi_encode_rational_by",
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
        "constructor_ClientReceipt",
        [],
        [],
        ltac:(M.monadic (
          let _ :=
            M.assign (|
              ["expr"],
              Some (M.call (|
                "caller",
                []
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_1"],
              Some (M.call (|
                "convert_stringliteral_4e03_to_bytes32",
                []
              |))
            |) in
          let _ :=
            M.assign (|
              ["expr_2"],
              Some ([Literal.number 0x07])
            |) in
          let _ :=
            M.assign (|
              ["_1"],
              Some ([Literal.number 0x19dacbf83c5de6658e14cbf7bcae5c15eca2eedecf1c66fbca928e4d351bea0f])
            |) in
          let _ :=
            M.assign (|
              ["_2"],
              Some (M.call (|
                "convert_address_to_address",
                [
                  M.get (| "expr" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_3"],
              Some (M.call (|
                "convert_bytes32_to_bytes32",
                [
                  M.get (| "expr_1" |)
                ]
              |))
            |) in
          let _ :=
            M.assign (|
              ["_4"],
              Some (M.call (|
                "allocate_unbounded",
                []
              |))
            |) in
          let _ :=
            M.assign (|
              ["_5"],
              Some (M.call (|
                "abi_encode_tuple_rational_by",
                [
                  M.get (| "_4" |);
                  M.get (| "expr_2" |)
                ]
              |))
            |) in
          let _ :=
            M.call (|
              "log3",
              [
                M.get (| "_4" |);
                M.call (|
                  "sub",
                  [
                    M.get (| "_5" |);
                    M.get (| "_4" |)
                  ]
                |);
                M.get (| "_1" |);
                M.get (| "_2" |);
                M.get (| "_3" |)
              ]
            |) in
          tt
        ))
      |) in
    tt
  )).

  Module ClientReceipt_23_deployed.
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
      "a26469706673582212208e91de9e63eb2d91dc0a6217d7c7a3d07872597aec91d34e8f9a5078aafe818364736f6c634300081b0033".
  End ClientReceipt_23_deployed.
End ClientReceipt_23.
