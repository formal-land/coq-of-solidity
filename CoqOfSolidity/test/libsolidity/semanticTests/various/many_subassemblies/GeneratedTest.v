(* Generated test file *)
Require Import CoqOfSolidity.CoqOfSolidity.
Require Import simulations.CoqOfSolidity.

Require test.libsolidity.semanticTests.various.many_subassemblies.C0.
Require test.libsolidity.semanticTests.various.many_subassemblies.C1.
Require test.libsolidity.semanticTests.various.many_subassemblies.C10.
Require test.libsolidity.semanticTests.various.many_subassemblies.C2.
Require test.libsolidity.semanticTests.various.many_subassemblies.C3.
Require test.libsolidity.semanticTests.various.many_subassemblies.C4.
Require test.libsolidity.semanticTests.various.many_subassemblies.C5.
Require test.libsolidity.semanticTests.various.many_subassemblies.C6.
Require test.libsolidity.semanticTests.various.many_subassemblies.C7.
Require test.libsolidity.semanticTests.various.many_subassemblies.C8.
Require test.libsolidity.semanticTests.various.many_subassemblies.C9.
Require test.libsolidity.semanticTests.various.many_subassemblies.D.

Definition constructor_code : Code.t :=
  test.libsolidity.semanticTests.various.many_subassemblies.D.D.code.

Definition deployed_code : Code.t :=
  test.libsolidity.semanticTests.various.many_subassemblies.D.D.deployed.code.

Definition codes : list (U256.t * M.t BlockUnit.t) :=
  test.libsolidity.semanticTests.various.many_subassemblies.D.codes.

Module Constructor.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := [];
    Environment.address := 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    let address := environment.(Environment.address) in
    let account := {|
      Account.balance := environment.(Environment.callvalue);
      Account.nonce := 1;
      Account.code := constructor_code.(Code.hex_name);
      Account.codedata := Memory.hex_string_as_bytes "";
      Account.storage := Memory.init;
      Account.immutables := [];
    |} in
    Stdlib.initial_state
      <| State.accounts := [(address, account)] |>
      <| State.codes := codes |>.

  Definition result_state :=
    eval_with_revert 5000 environment constructor_code.(Code.code) initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Goal Test.is_return result state = inl (Memory.u256_as_bytes deployed_code.(Code.hex_name)).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

Definition final_state : State.t :=
  snd (
    eval 5000 environment (update_current_code_for_deploy deployed_code.(Code.hex_name)) state
  ).
End Constructor.

(* // run() ->
// gas irOptimized: 374934
// gas irOptimized code: 6600
// gas legacy: 375119
// gas legacy code: 17600
// gas legacyOptimized: 375119
// gas legacyOptimized code: 17600 *)
Module Step1.
  Definition environment : Environment.t :={|
    Environment.caller := 0x1212121212121212121212121212120000000012;
    Environment.callvalue := 0;
    Environment.calldata := Memory.hex_string_as_bytes "c0406226";
    Environment.address := 0xc06afe3a8444fc0004668591e8306bfb9968e79e;
  |}.

  Definition initial_state : State.t :=
    Stdlib.initial_state
      <| State.accounts := Constructor.final_state.(State.accounts) |>
      <| State.codes := Constructor.final_state.(State.codes) |>.

  Definition result_state :=
    eval_with_revert 5000 environment deployed_code.(Code.code) initial_state.

  Definition result := fst result_state.
  Definition state := snd result_state.

  Definition expected_output : list Z :=
    Memory.hex_string_as_bytes "".

  Goal Test.extract_output result state Test.Status.Success = inl expected_output.
  Proof.
    vm_compute.
    reflexivity.
  Qed.
End Step1.
