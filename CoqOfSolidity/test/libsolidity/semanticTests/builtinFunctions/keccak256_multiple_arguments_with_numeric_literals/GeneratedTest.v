(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.builtinFunctions.keccak256_multiple_arguments_with_numeric_literals.c.

Definition constructor_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.builtinFunctions.keccak256_multiple_arguments_with_numeric_literals.c.c.code.

Definition deployed_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.builtinFunctions.keccak256_multiple_arguments_with_numeric_literals.c.c.deployed.code.

Module Constructor.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := [];
    Environment.codedata := Memory.hex_string_as_bytes "";
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    let address := environment.(Environment.address) in
    let account := {|
      Account.balance := environment.(Environment.callvalue);
      Account.code := deployed_code;
      Account.storage := Memory.init;
    |} in
    Stdlib.initial_state <|
      State.accounts := [(address, account)]
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment constructor_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Goal Test.is_return result = None.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Constructor.

(* // foo(uint256,uint16): 0xa, 0xc -> 0x88acd45f75907e7c560318bc1a5249850a0999c4896717b1167d05d116e6dbad *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "561536c7000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000c";
    Environment.codedata := [];
    Environment.address := HexString.of_Z 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state <|
      State.accounts := Constructor.state.(State.accounts)
    |>.

  Definition result_state :=
    eval_with_revert 1000 environment deployed_code initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "88acd45f75907e7c560318bc1a5249850a0999c4896717b1167d05d116e6dbad".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.
