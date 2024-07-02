(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module BaseBase.
  Definition code : Code.t := {|
    Code.name := "BaseBase_13";
    Code.hex_name := 0x42617365426173655f3133000000000000000000000000000000000000000000;
    Code.functions :=
      [
        
      ];
    Code.body :=
      M.scope (
        do! ltac:(M.monadic (
          M.scope (
            do! ltac:(M.monadic (
              M.declare (|
                ["_1"],
                Some (M.call_function (|
                  "memoryguard",
                  [
                    [Literal.number 0x80]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.if_ (|
                M.call_function (|
                  "callvalue",
                  []
                |),
                M.scope (
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
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
            do! ltac:(M.monadic (
              M.declare (|
                ["programSize"],
                Some (M.call_function (|
                  "datasize",
                  [
                    [Literal.string 0x42617365426173655f3133000000000000000000000000000000000000000000]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["argSize"],
                Some (M.call_function (|
                  "sub",
                  [
                    M.call_function (|
                      "codesize",
                      []
                    |);
                    M.get_var (| "programSize" |)
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["newFreePtr"],
                Some (M.call_function (|
                  "add",
                  [
                    M.get_var (| "_1" |);
                    M.call_function (|
                      "and",
                      [
                        M.call_function (|
                          "add",
                          [
                            M.get_var (| "argSize" |);
                            [Literal.number 31]
                          ]
                        |);
                        M.call_function (|
                          "not",
                          [
                            [Literal.number 31]
                          ]
                        |)
                      ]
                    |)
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.if_ (|
                M.call_function (|
                  "or",
                  [
                    M.call_function (|
                      "gt",
                      [
                        M.get_var (| "newFreePtr" |);
                        M.call_function (|
                          "sub",
                          [
                            M.call_function (|
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
                    M.call_function (|
                      "lt",
                      [
                        M.get_var (| "newFreePtr" |);
                        M.get_var (| "_1" |)
                      ]
                    |)
                  ]
                |),
                M.scope (
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
                        "mstore",
                        [
                          [Literal.number 0];
                          M.call_function (|
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
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
                        "mstore",
                        [
                          [Literal.number 4];
                          [Literal.number 0x41]
                        ]
                      |)
                    |)
                  )) in
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
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
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "mstore",
                  [
                    [Literal.number 64];
                    M.get_var (| "newFreePtr" |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "codecopy",
                  [
                    M.get_var (| "_1" |);
                    M.get_var (| "programSize" |);
                    M.get_var (| "argSize" |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.if_ (|
                M.call_function (|
                  "slt",
                  [
                    M.call_function (|
                      "sub",
                      [
                        M.call_function (|
                          "add",
                          [
                            M.get_var (| "_1" |);
                            M.get_var (| "argSize" |)
                          ]
                        |);
                        M.get_var (| "_1" |)
                      ]
                    |);
                    [Literal.number 32]
                  ]
                |),
                M.scope (
                  do! ltac:(M.monadic (
                    M.expr_stmt (|
                      M.call_function (|
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
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "sstore",
                  [
                    [Literal.number 0];
                    M.call_function (|
                      "mload",
                      [
                        M.get_var (| "_1" |)
                      ]
                    |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["_2"],
                Some (M.call_function (|
                  "mload",
                  [
                    [Literal.number 64]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["_3"],
                Some (M.call_function (|
                  "datasize",
                  [
                    [Literal.string 0x42617365426173655f31335f6465706c6f796564000000000000000000000000]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "codecopy",
                  [
                    M.get_var (| "_2" |);
                    M.call_function (|
                      "dataoffset",
                      [
                        [Literal.string 0x42617365426173655f31335f6465706c6f796564000000000000000000000000]
                      ]
                    |);
                    M.get_var (| "_3" |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "return",
                  [
                    M.get_var (| "_2" |);
                    M.get_var (| "_3" |)
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
      Code.name := "BaseBase_13_deployed";
      Code.hex_name := 0x42617365426173655f31335f6465706c6f796564000000000000000000000000;
      Code.functions :=
        [
          
        ];
      Code.body :=
        M.scope (
          do! ltac:(M.monadic (
            M.scope (
              do! ltac:(M.monadic (
                M.expr_stmt (|
                  M.call_function (|
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
          )) in
          M.pure BlockUnit.Tt
        );
    |}.
  End deployed.
End BaseBase.

Import Ltac2.

Definition codes : list Code.t :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
