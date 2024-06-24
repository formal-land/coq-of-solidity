(* Generated by solc *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module A.
  Definition code : Code.t := {|
    Code.name := "A_13";
    Code.hex_name := 0x415f313300000000000000000000000000000000000000000000000000000000;
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
            "cleanup_uint160",
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
                  |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "identity",
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
            "convert_uint160_to_uint160",
            ["value"],
            ["converted"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["converted"],
                  Some (M.call (|
                    "cleanup_uint160",
                    [
                      M.call (|
                        "identity",
                        [
                          M.call (|
                            "cleanup_uint160",
                            [
                              M.get_var (| "value" |)
                            ]
                          |)
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
            "convert_uint160_to_address",
            ["value"],
            ["converted"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["converted"],
                  Some (M.call (|
                    "convert_uint160_to_uint160",
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
            "convert_contract_A_to_address",
            ["value"],
            ["converted"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["converted"],
                  Some (M.call (|
                    "convert_uint160_to_address",
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
            "array_storeLengthForEncoding_bytes_nonPadded_inplace",
            ["pos"; "length"],
            ["updated_pos"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["updated_pos"],
                  Some (M.get_var (| "pos" |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "store_literal_in_memory_64e604787cbf194841e7b68d7cd28786f6c9a0a3ab9f8b0a0e87cb4387ab0107",
            ["memPtr"],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "mstore",
                    [
                      M.call (|
                        "add",
                        [
                          M.get_var (| "memPtr" |);
                          [Literal.number 0]
                        ]
                      |);
                      [Literal.string 0x3132330000000000000000000000000000000000000000000000000000000000]
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
            "abi_encode_stringliteral_64e6",
            ["pos"],
            ["end"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["pos"],
                  Some (M.call (|
                    "array_storeLengthForEncoding_bytes_nonPadded_inplace",
                    [
                      M.get_var (| "pos" |);
                      [Literal.number 3]
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "store_literal_in_memory_64e604787cbf194841e7b68d7cd28786f6c9a0a3ab9f8b0a0e87cb4387ab0107",
                    [
                      M.get_var (| "pos" |)
                    ]
                  |)
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["end"],
                  Some (M.call (|
                    "add",
                    [
                      M.get_var (| "pos" |);
                      [Literal.number 3]
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
            "abi_encode_packed_stringliteral_64e6",
            ["pos"],
            ["end"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["pos"],
                  Some (M.call (|
                    "abi_encode_stringliteral_64e6",
                    [
                      M.get_var (| "pos" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["end"],
                  Some (M.get_var (| "pos" |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "round_up_to_mul_of",
            ["value"],
            ["result"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["result"],
                  Some (M.call (|
                    "and",
                    [
                      M.call (|
                        "add",
                        [
                          M.get_var (| "value" |);
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
                  |))
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "panic_error_0x41",
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
                      [Literal.number 0x41]
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
            "finalize_allocation",
            ["memPtr"; "size"],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["newFreePtr"],
                  Some (M.call (|
                    "add",
                    [
                      M.get_var (| "memPtr" |);
                      M.call (|
                        "round_up_to_mul_of",
                        [
                          M.get_var (| "size" |)
                        ]
                      |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.if_ (|
                  M.call (|
                    "or",
                    [
                      M.call (|
                        "gt",
                        [
                          M.get_var (| "newFreePtr" |);
                          M.call (|
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
                          |)
                        ]
                      |);
                      M.call (|
                        "lt",
                        [
                          M.get_var (| "newFreePtr" |);
                          M.get_var (| "memPtr" |)
                        ]
                      |)
                    ]
                  |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "panic_error_0x41",
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
                    "mstore",
                    [
                      [Literal.number 64];
                      M.get_var (| "newFreePtr" |)
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
            "allocate_memory",
            ["size"],
            ["memPtr"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["memPtr"],
                  Some (M.call (|
                    "allocate_unbounded",
                    []
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "finalize_allocation",
                    [
                      M.get_var (| "memPtr" |);
                      M.get_var (| "size" |)
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
            "array_allocation_size_bytes",
            ["length"],
            ["size"],
            M.scope (
              do* ltac:(M.monadic (
                M.if_ (|
                  M.call (|
                    "gt",
                    [
                      M.get_var (| "length" |);
                      M.call (|
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
                      |)
                    ]
                  |),
                  M.scope (
                    do* ltac:(M.monadic (
                      M.expr_stmt (|
                        M.call (|
                          "panic_error_0x41",
                          []
                        |)
                      |)
                    )) in
                    M.pure BlockUnit.Tt
                  )
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["size"],
                  Some (M.call (|
                    "round_up_to_mul_of",
                    [
                      M.get_var (| "length" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["size"],
                  Some (M.call (|
                    "add",
                    [
                      M.get_var (| "size" |);
                      [Literal.number 0x20]
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
            "allocate_memory_array_bytes",
            ["length"],
            ["memPtr"],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["allocSize"],
                  Some (M.call (|
                    "array_allocation_size_bytes",
                    [
                      M.get_var (| "length" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.assign (|
                  ["memPtr"],
                  Some (M.call (|
                    "allocate_memory",
                    [
                      M.get_var (| "allocSize" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "mstore",
                    [
                      M.get_var (| "memPtr" |);
                      M.get_var (| "length" |)
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
            "zero_value_for_split_bytes",
            [],
            ["ret"],
            M.scope (
              do* ltac:(M.monadic (
                M.assign (|
                  ["ret"],
                  Some ([Literal.number 96])
                |)
              )) in
              M.pure BlockUnit.Tt
            )
          |)
        )) in
        do* ltac:(M.monadic (
          M.function (|
            "extract_returndata",
            [],
            ["data"],
            M.scope (
              do* ltac:(M.monadic (
                M.switch (|
                  M.call (|
                    "returndatasize",
                    []
                  |),
                  [
                    (
                      Some (Literal.number 0),
                      M.scope (
                        do* ltac:(M.monadic (
                          M.assign (|
                            ["data"],
                            Some (M.call (|
                              "zero_value_for_split_bytes",
                              []
                            |))
                          |)
                        )) in
                        M.pure BlockUnit.Tt
                      )
                    );
                    (
                      None,
                      M.scope (
                        do* ltac:(M.monadic (
                          M.assign (|
                            ["data"],
                            Some (M.call (|
                              "allocate_memory_array_bytes",
                              [
                                M.call (|
                                  "returndatasize",
                                  []
                                |)
                              ]
                            |))
                          |)
                        )) in
                        do* ltac:(M.monadic (
                          M.expr_stmt (|
                            M.call (|
                              "returndatacopy",
                              [
                                M.call (|
                                  "add",
                                  [
                                    M.get_var (| "data" |);
                                    [Literal.number 0x20]
                                  ]
                                |);
                                [Literal.number 0];
                                M.call (|
                                  "returndatasize",
                                  []
                                |)
                              ]
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
          M.function (|
            "constructor_A",
            [],
            [],
            M.scope (
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_5_address"],
                  Some (M.call (|
                    "address",
                    []
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr"],
                  Some (M.call (|
                    "convert_contract_A_to_address",
                    [
                      M.get_var (| "expr_5_address" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.declare (|
                  ["expr_address"],
                  Some (M.get_var (| "expr" |))
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
                M.declare (|
                  ["_2"],
                  Some (M.call (|
                    "sub",
                    [
                      M.call (|
                        "abi_encode_packed_stringliteral_64e6",
                        [
                          M.get_var (| "_1" |)
                        ]
                      |);
                      M.get_var (| "_1" |)
                    ]
                  |))
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "pop",
                    [
                      M.call (|
                        "call",
                        [
                          M.call (|
                            "gas",
                            []
                          |);
                          M.get_var (| "expr_address" |);
                          [Literal.number 0];
                          M.get_var (| "_1" |);
                          M.get_var (| "_2" |);
                          [Literal.number 0];
                          [Literal.number 0]
                        ]
                      |)
                    ]
                  |)
                |)
              )) in
              do* ltac:(M.monadic (
                M.expr_stmt (|
                  M.call (|
                    "pop",
                    [
                      M.call (|
                        "extract_returndata",
                        []
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
                  "constructor_A",
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
                        [Literal.string 0x415f31335f6465706c6f79656400000000000000000000000000000000000000]
                      ]
                    |);
                    M.call (|
                      "datasize",
                      [
                        [Literal.string 0x415f31335f6465706c6f79656400000000000000000000000000000000000000]
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
                        [Literal.string 0x415f31335f6465706c6f79656400000000000000000000000000000000000000]
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
      Code.name := "A_13_deployed";
      Code.hex_name := 0x415f31335f6465706c6f79656400000000000000000000000000000000000000;
      Code.code :=
        M.scope (
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
      "a2646970667358221220eb29da2ed5bcf83a64122d2e3a75706c6463c960fd4df38d0b3591d63e33ac6564736f6c634300081b0033".
  End deployed.
End A.

Definition codes : list (U256.t * M.t BlockUnit.t) :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
