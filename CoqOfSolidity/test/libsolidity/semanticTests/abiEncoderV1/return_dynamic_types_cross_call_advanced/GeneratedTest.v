(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.abiEncoderV1.return_dynamic_types_cross_call_advanced.C.

Definition constructor_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.abiEncoderV1.return_dynamic_types_cross_call_advanced.C.C.code.

Definition deployed_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.abiEncoderV1.return_dynamic_types_cross_call_advanced.C.C.deployed.code.

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

(* // f() -> 0x80, -1, 0xe0, 0x1234, 40, "12345678901234567890123456789012", "34567890", 4, 97767552542602192590433234714624, 0, 0, 537879995309340587922569878831104 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "26121ff0";
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
    Memory.hex_string_as_bytes "0000000000000000000000000000000000000000000000000000000000000080ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000001234000000000000000000000000000000000000000000000000000000000000002831323334353637383930313233343536373839303132333435363738393031323334353637383930000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000004d2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a85000000000000000000000000".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.
