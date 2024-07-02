(* Generated by coq-of-solidity *)
Require Import CoqOfSolidity.CoqOfSolidity.

Module test.
  Definition code : Code.t := {|
    Code.name := "test_25";
    Code.hex_name := 0x746573745f323500000000000000000000000000000000000000000000000000;
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
              M.expr_stmt (|
                M.call_function (|
                  "mstore",
                  [
                    [Literal.number 64];
                    M.get_var (| "_1" |)
                  ]
                |)
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
                ["_2"],
                Some ([Literal.number 0x00])
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "sstore",
                  [
                    [Literal.number 0x00];
                    [Literal.number 0x02]
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.assign (|
                ["_2"],
                Some ([Literal.number 0x00])
              |)
            )) in
            do! ltac:(M.monadic (
              M.assign (|
                ["_2"],
                Some ([Literal.number 0])
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "sstore",
                  [
                    [Literal.number 1];
                    M.call_function (|
                      "or",
                      [
                        M.call_function (|
                          "and",
                          [
                            M.call_function (|
                              "sload",
                              [
                                [Literal.number 1]
                              ]
                            |);
                            M.call_function (|
                              "not",
                              [
                                [Literal.number 255]
                              ]
                            |)
                          ]
                        |);
                        [Literal.number 0x02]
                      ]
                    |)
                  ]
                |)
              |)
            )) in
            do! ltac:(M.monadic (
              M.declare (|
                ["_3"],
                Some (M.call_function (|
                  "datasize",
                  [
                    [Literal.string 0x746573745f32355f6465706c6f79656400000000000000000000000000000000]
                  ]
                |))
              |)
            )) in
            do! ltac:(M.monadic (
              M.expr_stmt (|
                M.call_function (|
                  "codecopy",
                  [
                    M.get_var (| "_1" |);
                    M.call_function (|
                      "dataoffset",
                      [
                        [Literal.string 0x746573745f32355f6465706c6f79656400000000000000000000000000000000]
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
                    M.get_var (| "_1" |);
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
      Code.name := "test_25_deployed";
      Code.hex_name := 0x746573745f32355f6465706c6f79656400000000000000000000000000000000;
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
End test.

Import Ltac2.

Definition codes : list Code.t :=
  ltac2:(
    let codes := Code.get_codes () in
    exact $codes
  ).
