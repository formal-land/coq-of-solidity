(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require semanticTests.array.copying.storage_memory_nested_bytes.C.

Definition constructor_code : Code.t :=
  semanticTests.array.copying.storage_memory_nested_bytes.C.C.code.

Definition deployed_code : Code.t :=
  semanticTests.array.copying.storage_memory_nested_bytes.C.C.deployed.code.

Definition codes : list Code.t :=
  semanticTests.array.copying.storage_memory_nested_bytes.C.codes.

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

(* // f() -> 0x20, 0x02, 0x40, 0x80, 3, 0x6162630000000000000000000000000000000000000000000000000000000000, 0x99, 44048183304486788312148433451363384677562265908331949128489393215789685032262, 32241931068525137014058842823026578386641954854143559838526554899205067598957, 49951309422467613961193228765530489307475214998374779756599339590522149884499, 0x54555658595a6162636465666768696a6b6c6d6e6f707172737475767778797a, 0x4142434445464748494a4b4c4d4e4f5051525354555658595a00000000000000
// gas irOptimized: 202083
// gas legacy: 204327
// gas legacyOptimized: 202899 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "26121ff0";
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
    Memory.hex_string_as_bytes "00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000003616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000996162636465666768696a6b6c6d6e6f707172737475767778797a4142434445464748494a4b4c4d4e4f5051525354555658595a6162636465666768696a6b6c6d6e6f707172737475767778797a4142434445464748494a4b4c4d4e4f5051525354555658595a6162636465666768696a6b6c6d6e6f707172737475767778797a4142434445464748494a4b4c4d4e4f5051525354555658595a00000000000000".

  Goal Test.extract_output result state Test.Status.Success = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.
