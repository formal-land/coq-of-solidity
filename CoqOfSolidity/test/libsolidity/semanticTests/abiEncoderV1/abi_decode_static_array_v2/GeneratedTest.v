(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.abiEncoderV1.abi_decode_static_array_v2.C.

Definition constructor_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.abiEncoderV1.abi_decode_static_array_v2.C.C.code.

Definition deployed_code : M.t BlockUnit.t :=
  test.libsolidity.semanticTests.abiEncoderV1.abi_decode_static_array_v2.C.C.deployed.code.

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

(* // f(bytes): 0x20, 0xc0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6 -> 1, 2, 3, 4, 5, 6 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "d45754f8000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000006";
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
    Memory.hex_string_as_bytes "000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000006".

  Goal Test.extract_output result state true = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.
