(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module A_11.
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
                [Literal.string "415f31315f6465706c6f796564"]
              ]
            |);
            M.call (|
              "datasize",
              [
                [Literal.string "415f31315f6465706c6f796564"]
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
                [Literal.string "415f31315f6465706c6f796564"]
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

  Module A_11_deployed.
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
          "update_storage_value_offsett_uint256_to_uint256",
          ["slot"; "value"],
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
                    "update_byte_slice_shift",
                    [
                      M.call (|
                        "sload",
                        [
                          M.get (| "slot" |)
                        ]
                      |);
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
                ["expr"],
                Some ([Literal.number 0x01])
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
              M.call (|
                "update_storage_value_offsett_uint256_to_uint256",
                [
                  [Literal.number 0x00];
                  M.get (| "_1" |)
                ]
              |) in
            tt
          ))
        |) in
      tt
    )).

    Definition data : string :=
      "a26469706673582212208e36e751e53c69a0281dab9b4bcd2f94559b9693d0601db4c3b9cf1e87cb5edb64736f6c634300081b0033".
  End A_11_deployed.
End A_11.
