(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require semanticTests.abiencodedecode.abi_decode_simple_storage.C.

Definition constructor_code : Code.t :=
  semanticTests.abiencodedecode.abi_decode_simple_storage.C.C.code.

Definition deployed_code : Code.t :=
  semanticTests.abiencodedecode.abi_decode_simple_storage.C.C.deployed.code.

Definition codes : list Code.t :=
  semanticTests.abiencodedecode.abi_decode_simple_storage.C.codes.

Module Constructor.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := [];
    Environment.address := 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
    Environment.code_name := constructor_code.(Code.hex_name);
  |}.

  Definition initial_state : State.t :=
    let address := environment.(Environment.address) in
    let account := {|
      Account.balance := environment.(Environment.callvalue);
      Account.nonce := 1;
      Account.code := constructor_code.(Code.hex_name);
      Account.codedata := Memory.hex_string_as_bytes "";
      Account.storage := Memory.empty;
      Account.immutables := [];
    |} in
    State.init <| State.accounts := [(address, account)] |>.

  Definition result_state :=
    eval_with_revert 5000 codes environment constructor_code.(Code.body) initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Goal Test.is_return result state = inl (Memory.u256_as_bytes deployed_code.(Code.hex_name)).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

Definition final_state : State.t :=
  snd (
    eval 5000 codes environment (update_current_code_for_deploy deployed_code.(Code.hex_name)) state
  ).
End Constructor.

(* // f(bytes): 0x20, 0x80, 0x21, 0x40, 0x7, "abcdefg" -> 0x21, 0x40, 0x7, "abcdefg"
// gas irOptimized: 135499
// gas legacy: 137095
// gas legacyOptimized: 135823 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "d45754f8000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000076162636465666700000000000000000000000000000000000000000000000000";
    Environment.address := 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
    Environment.code_name := deployed_code.(Code.hex_name);
  |}.

  Definition initial_state : State.t :=
    State.init <| State.accounts := Constructor.final_state.(State.accounts) |>.

  Definition result_state :=
    eval_with_revert 5000 codes environment deployed_code.(Code.body) initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "0000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000076162636465666700000000000000000000000000000000000000000000000000".

  Goal Test.extract_output result state Test.Status.Success = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.
