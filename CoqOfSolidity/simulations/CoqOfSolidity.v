Require Import CoqOfSolidity.CoqOfSolidity.

Module Dict.
  Definition t (A : Set) : Set :=
    list (string * A).

  Fixpoint get {A : Set} (dict : t A) (name : string) : option A :=
    match dict with
    | [] => None
    | (name', value) :: dict =>
      if String.eqb name name' then
        Some value
      else
        get dict name
    end.

  Definition declare {A : Set} (dict : t A) (name : string) (value : A) : t A :=
    (name, value) :: dict.

  Fixpoint assign {A : Set} (dict : t A) (name : string) (value : A) : option (t A) :=
    match dict with
    | [] => None
    | ((name', _) as entry) :: dict =>
      if String.eqb name name' then
        Some ((name, value) :: dict)
      else
        match assign dict name value with
        | None => None
        | Some dict => Some (entry :: dict)
        end
    end.
End Dict.

Module Locals.
  Record t : Set := {
    functions : list (string * (list U256.t -> M.t (list U256.t)));
    variables : list (string * U256.t)
  }.

  Definition empty : t := {|
    functions := [];
    variables := [];
  |}.
End Locals.

Module Stack.
  Definition t : Set :=
    list Locals.t.

  Definition open_scope (stack : t) : t :=
    Locals.empty :: stack.

  Definition close_scope (stack : t) : t :=
    match stack with
    | [] => stack
    | _ :: stack => stack
    end.

  Fixpoint get_var (stack : t) (name : string) : U256.t :=
    match stack with
    | [] => 0
    | locals :: stack =>
      match Dict.get locals.(Locals.variables) name with
      | None => get_var stack name
      | Some value => value
      end
    end.

  Definition declare_var (stack : t) (name : string) (value : U256.t) : t :=
    match stack with
    | [] => []
    | locals :: stack =>
      locals <| Locals.variables := Dict.declare locals.(Locals.variables) name value |> :: stack
    end.

  Fixpoint declare_vars (stack : t) (names : list string) (values : list U256.t) : t :=
    match names, values with
    | name :: names, value :: values =>
      declare_vars (declare_var stack name value) names values
    | _, _ => stack
    end.

  Fixpoint assign_var (stack : t) (name : string) (value : U256.t) : t :=
    match stack with
    | [] => []
    | locals :: stack =>
      match Dict.assign locals.(Locals.variables) name value with
      | None => locals :: assign_var stack name value
      | Some variables => locals <| Locals.variables := variables |> :: stack
      end
    end.

  Fixpoint assign_vars (stack : t) (names : list string) (values : list U256.t) : t :=
    match names, values with
    | name :: names, value :: values =>
      assign_vars (assign_var stack name value) names values
    | _, _ => stack
    end.

  Fixpoint get_function (stack : t) (name : string) : list U256.t -> M.t (list U256.t) :=
    match stack with
    | [] => fun _ => LowM.Impossible ("function '" ++ name ++ "' not found")
    | locals :: stack =>
      match Dict.get locals.(Locals.functions) name with
      | None => get_function stack name
      | Some function => function
      end
    end.

  Definition declare_function
      (stack : t)
      (name : string)
      (body : list U256.t -> M.t (list U256.t)) :
      t :=
    match stack with
    | [] => []
    | locals :: stack =>
      locals <| Locals.functions := Dict.declare locals.(Locals.functions) name body |> :: stack
    end.
End Stack.

Module Memory.
  (** We define the memory as a function instead of an explicit list as there can be holes in it. *)
  Definition t : Set :=
    U256.t -> U256.t.

  Definition init : t :=
    fun _ => 0.

  Definition update (memory : t) (address : U256.t) (value : U256.t) : t :=
    fun current_address =>
      if address =? current_address then
        value
      else
        memory current_address.
End Memory.

Module State.
  (** The state contains the various kinds of memory that we use in a smart contract. *)
  Record t : Set := {
    stack : Stack.t;
    mem : Memory.t;
    storage : Memory.t;
    transientStorage : Memory.t;
  }.
End State.

(** We consider that all the primitives can be defined as a function over the state. *)
Definition eval_primitive {A : Set}
    (environment : Environment.t)
    (state : State.t)
    (primitive : Primitive.t A) :
    A * State.t :=
  match primitive with
  | Primitive.OpenScope =>
    (
      tt,
      state <| State.stack := Stack.open_scope state.(State.stack) |>
    )
  | Primitive.CloseScope =>
    (
      tt,
      state <| State.stack := Stack.close_scope state.(State.stack) |>
    )
  | Primitive.GetVar name =>
    (
      Stack.get_var state.(State.stack) name,
      state
    )
  | Primitive.DeclareVars names values =>
    (
      tt,
      state <| State.stack := Stack.declare_vars state.(State.stack) names values |>
    )
  | Primitive.AssignVars names values =>
    (
      tt,
      state <| State.stack := Stack.assign_vars state.(State.stack) names values |>
    )
  | Primitive.MLoad address =>
    (
      state.(State.mem) address,
      state
    )
  | Primitive.MStore address value =>
    (
      tt,
      state <| State.mem := Memory.update state.(State.mem) address value |>
    )
  | Primitive.SLoad address =>
    (
      state.(State.storage) address,
      state
    )
  | Primitive.SStore address value =>
    (
      tt,
      state <| State.storage := Memory.update state.(State.storage) address value |>
    )
  | Primitive.TLoad address =>
    (
      state.(State.transientStorage) address,
      state
    )
  | Primitive.TStore address value =>
    (
      tt,
      state <| State.transientStorage := Memory.update state.(State.transientStorage) address value |>
    )
  | Primitive.GetEnvironment =>
    (
      environment,
      state
    )
  end.

(** A function to evaluate an expression assuming that we have enough [fuel]. *)
Fixpoint eval {A : Set}
    (fuel : nat)
    (environment : Environment.t)
    (state : State.t)
    (e : LowM.t A) :
    (A + string) * State.t :=
  match fuel with
  | O => (inr "out of fuel", state)
  | S fuel =>
    match e with
    | LowM.Pure output => (inl output, state)
    | LowM.Primitive primitive k =>
      let '(value, state_inter) := eval_primitive environment state primitive in
      eval fuel environment state_inter (k value)
    | LowM.DeclareFunction name body k =>
      let state_inter :=
        state <| State.stack := Stack.declare_function state.(State.stack) name body |> in
      eval fuel environment state_inter k
    | LowM.CallFunction name arguments k =>
      let function := Stack.get_function state.(State.stack) name in
      let (results, stack_inter) := eval fuel environment state (function arguments) in
      match results with
      | inl results => eval fuel environment stack_inter (k results)
      | inr message => (inr message, state)
      end
    | LowM.Let e1 k =>
      let (output_inter, stack_inter) := eval fuel environment state e1 in
      match output_inter with
      | inl output_inter => eval fuel environment stack_inter (k output_inter)
      | inr message => (inr message, state)
      end
    | LowM.Impossible message => (inr ("Impossible: " ++ message)%string, state)
    end
  end.

Module Run.
  Reserved Notation "{{ environment , state | e ⇓ output | state' }}"
    (at level 70, no associativity).

  Inductive t {A : Set} (environment : Environment.t) (state : State.t) (output : A) :
      LowM.t A -> State.t -> Prop :=
  | Pure : {{ environment, state | LowM.Pure output ⇓ output | state }}
  | Primitive {B : Set} (primitive : Primitive.t B) (k : B -> LowM.t A) state' :
    let value_inter_state := eval_primitive environment state primitive in
    (* Because we are not allowed to destructure a value in an inductive definition, so we use
       the [fst] and [snd] functions instead of a pattern. *)
    let value := fst value_inter_state in
    let state_inter := snd value_inter_state in
    {{ environment, state_inter | k value ⇓ output | state' }} ->
    {{ environment, state | LowM.Primitive primitive k ⇓ output | state' }}
  | DeclareFunction name body k state' :
    let state_inter :=
      state <| State.stack := Stack.declare_function state.(State.stack) name body |> in
    {{ environment, state_inter | k ⇓ output | state' }} ->
    {{ environment, state | LowM.DeclareFunction name body k ⇓ output | state' }}
  | CallFunction name arguments k results stack_inter state' :
    let function := Stack.get_function state.(State.stack) name in
    {{ environment, state | function arguments ⇓ results | stack_inter }} ->
    {{ environment, stack_inter | k results ⇓ output | state' }} ->
    {{ environment, state | LowM.CallFunction name arguments k ⇓ output | state' }}
  | Let {B : Set} (e1 : LowM.t B) k stack_inter output_inter state' :
    {{ environment, state | e1 ⇓ output_inter | stack_inter }} ->
    {{ environment, stack_inter | k output_inter ⇓ output | state' }} ->
    {{ environment, state | LowM.Let e1 k ⇓ output | state' }}

  where "{{ environment , state | e ⇓ output | state' }}" :=
    (t environment state output e state').
End Run.

Import Run.

(** The [eval] function follows the semantics given by [Run.t]. *)
Fixpoint eval_is_run {A : Set}
    (fuel : nat)
    (environment : Environment.t)
    (state : State.t)
    (e : LowM.t A)
    (output : A)
    (state' : State.t) :
  eval fuel environment state e = (inl output, state') ->
  {{ environment, state | e ⇓ output | state' }}.
Proof.
  destruct fuel as [|fuel]; [discriminate|].
  destruct e; cbn; intros H_eval.
  { (* Pure *)
    inversion H_eval; constructor.
  }
  { (* Primitive *)
    destruct primitive;
      cbn in H_eval;
      constructor;
      eapply eval_is_run;
      eassumption.
  }
  { (* DeclareFunction *)
    constructor.
    eapply eval_is_run.
    eassumption.
  }
  { (* CallFunction *)
    destruct eval as [[results | message] locals_inter] eqn:H_eval_inter in H_eval.
    { econstructor;
        eapply eval_is_run;
        eassumption.
    }
    { discriminate. }
  }
  { (* Let *)
    destruct eval as [[results | message] locals_inter] eqn:H_eval_inter in H_eval.
    { econstructor;
        eapply eval_is_run;
        eassumption.
    }
    { discriminate. }
  }
  { (* Impossible *)
    discriminate.
  }
Qed.

Module Stdlib.
  Definition return_ (p s : U256.t) : M.t unit :=
    LowM.Pure (Result.Return p s Revert.Without).

  Definition stop : M.t unit :=
    return_ 0 0.

  Definition add (x y : U256.t) : U256.t :=
    (x + y) mod (2 ^ 256).

  Definition sub (x y : U256.t) : U256.t :=
    (x - y) mod (2 ^ 256).

  Definition mul (x y : U256.t) : U256.t :=
    (x * y) mod (2 ^ 256).

  Definition div (x y : U256.t) : U256.t :=
    if y =? 0 then 0 else x / y.

  Definition sdiv (x y : U256.t) : M.t U256.t :=
    LowM.Impossible "sdiv".

  Definition mod_ (x y : U256.t) : U256.t :=
    if y =? 0 then 0 else x mod y.

  Definition smod (x y : U256.t) : M.t U256.t :=
    LowM.Impossible "smod".

  Definition exp (x y : U256.t) : U256.t :=
    x ^ y.

  Definition not (x : U256.t) : U256.t :=
    Z.lnot x.

  Definition lt (x y : U256.t) : U256.t :=
    if x <? y then 1 else 0.

  Definition gt (x y : U256.t) : U256.t :=
    if x >? y then 1 else 0.

  (* Signed version of [lt] *)
  Definition slt (x y : U256.t) : M.t U256.t :=
    LowM.Impossible "slt".

  Definition sgt (x y : U256.t) : M.t U256.t :=
    LowM.Impossible "sgt".

  Definition eq (x y : U256.t) : U256.t :=
    if x =? y then 1 else 0.

  Definition iszero (x : U256.t) : U256.t :=
    if x =? 0 then 1 else 0.

  Definition and (x y : U256.t) : U256.t :=
    Z.land x y.

  Definition or (x y : U256.t) : U256.t :=
    Z.lor x y.

  Definition xor (x y : U256.t) : U256.t :=
    Z.lxor x y.

  Definition byte (n x : U256.t) : M.t U256.t :=
    LowM.Impossible "byte".

  Definition shl (x y : U256.t) : M.t U256.t :=
    LowM.Impossible "shl".

  Definition shr (x y : U256.t) : M.t U256.t :=
    LowM.Impossible "shr".

  Definition sar (x y : U256.t) : M.t U256.t :=
    LowM.Impossible "sar".

  Definition addmod (x y m : U256.t) : U256.t :=
    (x + y) mod m.

  Definition mulmod (x y m : U256.t) : U256.t :=
    (x * y) mod m.

  Definition signextend (i x : U256.t) : M.t U256.t :=
    LowM.Impossible "signextend".

  Definition keccak256 (p n : U256.t) : M.t U256.t :=
    LowM.Impossible "keccak256".

  Definition pc : M.t U256.t :=
    LowM.Impossible "pc".

  Definition pop (x : U256.t) : M.t unit :=
    LowM.Impossible "pop".

  Definition mload (address : U256.t) : M.t U256.t :=
    LowM.Primitive (Primitive.MLoad address) M.pure.

  Definition mstore (address value : U256.t) : M.t unit :=
    LowM.Primitive (Primitive.MStore address value) M.pure.

  Definition mstore8 (address value : U256.t) : M.t unit :=
    LowM.Impossible "mstore8".

  Definition sload (address : U256.t) : M.t U256.t :=
    LowM.Primitive (Primitive.SLoad address) M.pure.

  Definition sstore (address value : U256.t) : M.t unit :=
    LowM.Primitive (Primitive.SStore address value) M.pure.

  Definition tload (address : U256.t) : M.t U256.t :=
    LowM.Primitive (Primitive.TLoad address) M.pure.

  Definition tstore (address value : U256.t) : M.t unit :=
    LowM.Primitive (Primitive.TStore address value) M.pure.

  Definition msize : M.t U256.t :=
    LowM.Impossible "msize".

  Definition gas : M.t U256.t :=
    LowM.Impossible "gas".

  Definition address : M.t U256.t :=
    LowM.Impossible "address".

  Definition balance (a : U256.t) : M.t U256.t :=
    LowM.Impossible "balance".

  Definition selfbalance : M.t U256.t :=
    LowM.Impossible "selfbalance".

  Definition caller : M.t U256.t :=
    LowM.Primitive Primitive.GetEnvironment (fun env => M.pure env.(Environment.caller)).

  Definition callvalue : M.t U256.t :=
    LowM.Primitive Primitive.GetEnvironment (fun env => M.pure env.(Environment.callvalue)).

  Definition calldataload (p : U256.t) : M.t U256.t :=
    LowM.Impossible "calldataload".

  Definition calldatasize : M.t U256.t :=
    LowM.Impossible "calldatasize".

  Definition calldatacopy (t f s : U256.t) : M.t unit :=
    LowM.Impossible "calldatacopy".

  Definition codesize : M.t U256.t :=
    LowM.Impossible "codesize".

  Definition codecopy (t f s : U256.t) : M.t unit :=
    LowM.Impossible "codecopy".

  Definition extcodesize (a : U256.t) : M.t U256.t :=
    LowM.Impossible "extcodesize".

  Definition extcodecopy (a t f s : U256.t) : M.t unit :=
    LowM.Impossible "extcodecopy".

  Definition returndatasize : M.t U256.t :=
    LowM.Impossible "returndatasize".

  Definition returndatacopy (t f s : U256.t) : M.t unit :=
    LowM.Impossible "returndatacopy".

  Definition mcopy (t f s : U256.t) : M.t unit :=
    LowM.Impossible "mcopy".

  Definition extcodehash (a : U256.t) : M.t U256.t :=
    LowM.Impossible "extcodehash".

  Definition create (v p n : U256.t) : M.t U256.t :=
    LowM.Impossible "create".

  Definition create2 (v p n s : U256.t) : M.t U256.t :=
    LowM.Impossible "create2".

  Definition call (g a v in_ insize out outsize : U256.t) : M.t U256.t :=
    LowM.Impossible "call".

  Definition callcode (g a v in_ insize out outsize : U256.t) : M.t U256.t :=
    LowM.Impossible "callcode".

  Definition delegatecall (g a in_ insize out outsize : U256.t) : M.t U256.t :=
    LowM.Impossible "delegatecall".

  Definition staticcall (g a in_ insize out outsize : U256.t) : M.t U256.t :=
    LowM.Impossible "staticcall".

  Definition revert (p s : U256.t) : M.t unit :=
    LowM.Pure (Result.Return p s Revert.With).

  Definition selfdestruct (a : U256.t) : M.t unit :=
    LowM.Impossible "selfdestruct".

  Definition invalid : M.t unit :=
    LowM.Impossible "invalid".

  Definition log0 (p s : U256.t) : M.t unit :=
    LowM.Impossible "log0".

  Definition log1 (p s t1 : U256.t) : M.t unit :=
    LowM.Impossible "log1".

  Definition log2 (p s t1 t2 : U256.t) : M.t unit :=
    LowM.Impossible "log2".

  Definition log3 (p s t1 t2 t3 : U256.t) : M.t unit :=
    LowM.Impossible "log3".

  Definition log4 (p s t1 t2 t3 t4 : U256.t) : M.t unit :=
    LowM.Impossible "log4".

  Definition chainid : M.t U256.t :=
    LowM.Impossible "chainid".

  Definition basefee : M.t U256.t :=
    LowM.Impossible "basefee".

  Definition blobbasefee : M.t U256.t :=
    LowM.Impossible "blobbasefee".

  Definition origin : M.t U256.t :=
    LowM.Impossible "origin".

  Definition gasprice : M.t U256.t :=
    LowM.Impossible "gasprice".

  Definition blockhash (b : U256.t) : M.t U256.t :=
    LowM.Impossible "blockhash".

  Definition blobhash (i : U256.t) : M.t U256.t :=
    LowM.Impossible "blobhash".

  Definition coinbase : M.t U256.t :=
    LowM.Impossible "coinbase".

  Definition timestamp : M.t U256.t :=
    LowM.Impossible "timestamp".

  Definition number : M.t U256.t :=
    LowM.Impossible "number".

  Definition difficulty : M.t U256.t :=
    LowM.Impossible "difficulty".

  Definition prevrandao : M.t U256.t :=
    LowM.Impossible "prevrandao".

  Definition gaslimit : M.t U256.t :=
    LowM.Impossible "gaslimit".

  (** Additional functions for the object mode of Yul. *)
  Module Object.
    (** We assume that the optimizer does not use any additional memory. *)
    Definition memoryguard (size : U256.t) : M.t U256.t :=
      pure size.
  End Object.

  Notation "'fn' p '=>' body" :=
    (fun arguments =>
      match arguments with
      | p => body
      | _ => LowM.Impossible "wrong number of arguments"
      end)
    (at level 200, p pattern).

  Definition return_unit (body : M.t unit) : M.t (list U256.t) :=
    M.let_ body (fun _ => pure []).

  Definition return_u256 (body : M.t U256.t) : M.t (list U256.t) :=
    M.let_ body (fun result => pure [result]).

  Definition functions : list (string * (list U256.t -> M.t (list U256.t))) := [
    ("stop", fn [] => return_unit stop);
    ("add", fn [x; y] => return_u256 (pure (add x y)));
    ("sub", fn [x; y] => return_u256 (pure (sub x y)));
    ("mul", fn [x; y] => return_u256 (pure (mul x y)));
    ("div", fn [x; y] => return_u256 (pure (div x y)));
    ("sdiv", fn [x; y] => return_u256 (sdiv x y));
    ("mod", fn [x; y] => return_u256 (pure (mod_ x y)));
    ("smod", fn [x; y] => return_u256 (smod x y));
    ("exp", fn [x; y] => return_u256 (pure (exp x y)));
    ("not", fn [x] => return_u256 (pure (not x)));
    ("lt", fn [x; y] => return_u256 (pure (lt x y)));
    ("gt", fn [x; y] => return_u256 (pure (gt x y)));
    ("slt", fn [x; y] => return_u256 (slt x y));
    ("sgt", fn [x; y] => return_u256 (sgt x y));
    ("eq", fn [x; y] => return_u256 (pure (eq x y)));
    ("iszero", fn [x] => return_u256 (pure (iszero x)));
    ("and", fn [x; y] => return_u256 (pure (and x y)));
    ("or", fn [x; y] => return_u256 (pure (or x y)));
    ("xor", fn [x; y] => return_u256 (pure (xor x y)));
    ("byte", fn [n; x] => return_u256 (byte n x));
    ("shl", fn [x; y] => return_u256 (shl x y));
    ("shr", fn [x; y] => return_u256 (shr x y));
    ("sar", fn [x; y] => return_u256 (sar x y));
    ("addmod", fn [x; y; m] => return_u256 (pure (addmod x y m)));
    ("mulmod", fn [x; y; m] => return_u256 (pure (mulmod x y m)));
    ("signextend", fn [i; x] => return_u256 (signextend i x));
    ("keccak256", fn [p; n] => return_u256 (keccak256 p n));
    ("pc", fn [] => return_u256 pc);
    ("pop", fn [x] => return_unit (pop x));
    ("mload", fn [p] => return_u256 (mload p));
    ("mstore", fn [p; v] => return_unit (mstore p v));
    ("mstore8", fn [p; v] => return_unit (mstore8 p v));
    ("sload", fn [p] => return_u256 (sload p));
    ("sstore", fn [p; v] => return_unit (sstore p v));
    ("tload", fn [p] => return_u256 (tload p));
    ("tstore", fn [p; v] => return_unit (tstore p v));
    ("msize", fn [] => return_u256 msize);
    ("gas", fn [] => return_u256 gas);
    ("address", fn [] => return_u256 address);
    ("balance", fn [a] => return_u256 (balance a));
    ("selfbalance", fn [] => return_u256 selfbalance);
    ("caller", fn [] => return_u256 caller);
    ("callvalue", fn [] => return_u256 callvalue);
    ("calldataload", fn [p] => return_u256 (calldataload p));
    ("calldatasize", fn [] => return_u256 calldatasize);
    ("calldatacopy", fn [p; s; n] => return_unit (calldatacopy p s n));
    ("codesize", fn [] => return_u256 codesize);
    ("codecopy", fn [p; s; n] => return_unit (codecopy p s n));
    ("extcodesize", fn [a] => return_u256 (extcodesize a));
    ("extcodecopy", fn [a; p; s; n] => return_unit (extcodecopy a p s n));
    ("returndatasize", fn [] => return_u256 returndatasize);
    ("returndatacopy", fn [p; s; n] => return_unit (returndatacopy p s n));
    ("mcopy", fn [p; s; n] => return_unit (mcopy p s n));
    ("extcodehash", fn [a] => return_u256 (extcodehash a));
    ("create", fn [v; p; n] => return_u256 (create v p n));
    ("create2", fn [v; p; n; s] => return_u256 (create2 v p n s));
    ("call", fn [g; a; v; in_; insize; out; outsize] =>
      return_u256 (call g a v in_ insize out outsize));
    ("callcode", fn [g; a; v; in_; insize; out; outsize] =>
      return_u256 (callcode g a v in_ insize out outsize));
    ("delegatecall", fn [g; a; in_; insize; out; outsize] =>
      return_u256 (delegatecall g a in_ insize out outsize));
    ("staticcall", fn [g; a; in_; insize; out; outsize] =>
      return_u256 (staticcall g a in_ insize out outsize));
    ("revert", fn [p; s] => return_unit (revert p s));
    ("selfdestruct", fn [a] => return_unit (selfdestruct a));
    ("invalid", fn [] => return_unit invalid);
    ("log0", fn [p; s] => return_unit (log0 p s));
    ("log1", fn [p; s; t1] => return_unit (log1 p s t1));
    ("log2", fn [p; s; t1; t2] => return_unit (log2 p s t1 t2));
    ("log3", fn [p; s; t1; t2; t3] => return_unit (log3 p s t1 t2 t3));
    ("log4", fn [p; s; t1; t2; t3; t4] => return_unit (log4 p s t1 t2 t3 t4));
    ("chainid", fn [] => return_u256 chainid);
    ("basefee", fn [] => return_u256 basefee);
    ("blobbasefee", fn [] => return_u256 blobbasefee);
    ("origin", fn [] => return_u256 origin);
    ("gasprice", fn [] => return_u256 gasprice);
    ("blockhash", fn [b] => return_u256 (blockhash b));
    ("blobhash", fn [i] => return_u256 (blobhash i));
    ("coinbase", fn [] => return_u256 coinbase);
    ("timestamp", fn [] => return_u256 timestamp);
    ("number", fn [] => return_u256 number);
    ("difficulty", fn [] => return_u256 difficulty);
    ("prevrandao", fn [] => return_u256 prevrandao);
    ("gaslimit", fn [] => return_u256 gaslimit);
    ("memoryguard", fn [p] => return_u256 (Object.memoryguard p))
  ].

  Definition init_stack : Stack.t :=
    [
      {|
        Locals.functions := Stdlib.functions;
        Locals.variables := [];
      |}
    ].

  Definition init_state : State.t :=
    {|
      State.stack := init_stack;
      State.mem := Memory.init;
      State.storage := Memory.init;
      State.transientStorage := Memory.init;
    |}.
End Stdlib.

Require test.libsolidity.semanticTests.various.erc20.ERC20.

Definition foo_env : Environment.t := {|
  Environment.caller := 123;
  Environment.callvalue := 0;
|}.

Definition foo : _ * State.t := eval 100 foo_env Stdlib.init_state ERC20.ERC20_403.code.

Compute fst foo.
