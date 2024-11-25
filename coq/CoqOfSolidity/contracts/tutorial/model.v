Require Import CoqOfSolidity.CoqOfSolidity.
Require Import CoqOfSolidity.proofs.CoqOfSolidity.
Require Import CoqOfSolidity.simulations.CoqOfSolidity.
Require Import CoqOfSolidity.contracts.tutorial.shallow.

Import Stdlib.
Import RunO.

Definition safe_add (x y : Z) : option Z :=
  (* We use unbounded integers [Z] *)
  let sum := x + y in
  (* We return [None] in case of overflow *)
  if sum <? 2 ^ 256 then
    Some sum
  else
    None.

Lemma run_checked_add_t_uint256 codes environment state
    (x y sum : Z)
    (H_x : 0 <= x < 2^256)
    (H_y : 0 <= y < 2^256)
    (H_sum : safe_add x y = Some sum) :
  {{? codes, environment, Some state |
    Contract_16.Contract_16_deployed.checked_add_t_uint256 x y ⇓
    Result.Ok sum
  | Some state ?}}.
Proof.
  unfold safe_add in H_sum.
  destruct (_ <? _) eqn:? in H_sum; inversion_clear H_sum.
  unfold Contract_16.Contract_16_deployed.checked_add_t_uint256, safe_add in *.
  lu.
  repeat (lu || cu || p).
  s.
  unfold Pure.gt, Pure.add.
  destruct (_ >? _) eqn:?; s.
  { lia. }
  { pe; f_equal.
    lia.
  }
Qed.
