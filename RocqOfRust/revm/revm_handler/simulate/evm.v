Require Import simulate.RocqOfRust.
Require Import core.links.result.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.host.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_handler.simulate.frame.
Require Import revm.revm_handler.simulate.frame_data.
Require Import revm.revm_interpreter.simulate.eth_interpreter.

(** The frame pool in Rust is an allocation optimization. Here the head of the
    list is the current frame; completed frames are removed explicitly. *)
Module Evm.
  Record t (DB Error : Set) : Set := {
    ctx : Context.t DB Error;
    frame_stack : list EthFrame.t;
  }.

  Arguments ctx {DB Error}.

  Arguments frame_stack {DB Error}.
End Evm.

Module Impl_Evm.
  Definition frame_init {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (self : Evm.t DB Error) (input : FrameInit.t)
      : option (Result.t (ItemOrResult.t unit FrameResult.t) (ContextError.t Error) * Evm.t DB Error) :=
    match Impl_EthFrame.init_with_context self.(Evm.ctx) input with
    | None => None
    | Some (result, ctx) =>
      let self := self <| Evm.ctx := ctx |> in
      match result with
      | Result.Err error => Some (Result.Err error, self)
      | Result.Ok (ItemOrResult.Result result) => Some (Result.Ok (ItemOrResult.Result result), self)
      | Result.Ok (ItemOrResult.Item frame) =>
        Some (Result.Ok (ItemOrResult.Item tt), self <| Evm.frame_stack := frame :: self.(Evm.frame_stack) |>)
      end
    end.

  Definition frame_run {DB Error : Set} `{Database.C DB Error}
      (fuel : nat) (self : Evm.t DB Error)
      : option (ItemOrResult.t FrameInit.t FrameResult.t * Evm.t DB Error * nat) :=
    match self.(Evm.frame_stack) with
    | [] => None
    | frame :: parents =>
      match Impl_EthInterpreter.run_plain fuel frame.(EthFrame.interpreter) self.(Evm.ctx) with
      | None => None
      | Some (action, interpreter, ctx, fuel) =>
        let frame := frame <| EthFrame.interpreter := interpreter |> in
        match Impl_EthFrame.process_next_action frame ctx action with
        | None => None
        | Some (result, ctx) =>
          let frame := match result with
            | ItemOrResult.Item _ => frame
            | ItemOrResult.Result _ => frame <| EthFrame.is_finished := true |>
            end in
          Some (result, {| Evm.ctx := ctx; Evm.frame_stack := frame :: parents |}, fuel)
        end
      end
    end.

  Definition frame_return_result {DB Error : Set} (self : Evm.t DB Error) (result : FrameResult.t)
      : option (Result.t (option FrameResult.t) (ContextError.t Error) * Evm.t DB Error) :=
    match self.(Evm.frame_stack) with
    | [] => None
    | frame :: parents =>
      let frames := if frame.(EthFrame.is_finished) then parents else self.(Evm.frame_stack) in
      let self := self <| Evm.frame_stack := frames |> in
      match frames with
      | [] => Some (Result.Ok (Some result), self)
      | parent :: parents =>
        match Impl_EthFrame.return_result parent self.(Evm.ctx) result with
        | None => None
        | Some (Result.Err error, ctx) => Some (Result.Err error, self <| Evm.ctx := ctx |>)
        | Some (Result.Ok parent, ctx) =>
          Some (Result.Ok None, {| Evm.ctx := ctx; Evm.frame_stack := parent :: parents |})
        end
      end
    end.
End Impl_Evm.

Module ExecutionLoop.
  (** Rust's Handler::run_exec_loop, with an explicit evaluator bound. The
      instruction budget returned by run_plain is shared by every child frame.
      loop_bound bounds action processing separately; every new action requires
      an instruction, so the entry point starts it at S fuel. *)
  Fixpoint run {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (loop_bound fuel : nat) (self : Evm.t DB Error) {struct loop_bound}
      : option (Result.t FrameResult.t (ContextError.t Error) * Evm.t DB Error * nat) :=
    match loop_bound with
    | O => None
    | S loop_bound =>
      match Impl_Evm.frame_run fuel self with
      | None => None
      | Some (action, self, fuel) =>
        let result := match action with
          | ItemOrResult.Result result => Some (Result.Ok (ItemOrResult.Result result), self)
          | ItemOrResult.Item input => Impl_Evm.frame_init self input
          end in
        match result with
        | None => None
        | Some (Result.Err error, self) => Some (Result.Err error, self, fuel)
        | Some (Result.Ok (ItemOrResult.Item _), self) => run loop_bound fuel self
        | Some (Result.Ok (ItemOrResult.Result result), self) =>
          match Impl_Evm.frame_return_result self result with
          | None => None
          | Some (Result.Err error, self) => Some (Result.Err error, self, fuel)
          | Some (Result.Ok None, self) => run loop_bound fuel self
          | Some (Result.Ok (Some result), self) => Some (Result.Ok result, self, fuel)
          end
        end
      end
    end.

  Definition run_exec_loop {DB Error : Set} `{Database.C DB Error} `{PrecompileProvider.C DB Error}
      (fuel : nat) (self : Evm.t DB Error) (input : FrameInit.t)
      : option (Result.t FrameResult.t (ContextError.t Error) * Evm.t DB Error * nat) :=
    match Impl_Evm.frame_init self input with
    | None => None
    | Some (Result.Err error, self) => Some (Result.Err error, self, fuel)
    | Some (Result.Ok (ItemOrResult.Result result), self) => Some (Result.Ok result, self, fuel)
    | Some (Result.Ok (ItemOrResult.Item _), self) => run (S fuel) fuel self
    end.
End ExecutionLoop.
