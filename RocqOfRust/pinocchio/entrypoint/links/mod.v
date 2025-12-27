Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.array.
Require Import pinocchio.links.account_info.
Require Import pinocchio.entrypoint.mod.

Module entrypoint.
  Module deserialize.

    Parameter MAX_ACCOUNTS : Usize.t.

    Definition Self : Set := (Ref.t Pointer.Kind.Ref U8.t *
                              Usize.t *
                              Ref.t Pointer.Kind.Ref (list U8.t))%type.

    Instance run_deserialize
      (input : Ref.t Pointer.Kind.Raw U8.t)
      (accounts : Ref.t Pointer.Kind.Ref (array.t AccountInfo.t MAX_ACCOUNTS)) :
      Run.Trait
        pinocchio.entrypoint.mod.entrypoint.deserialize
        [φ MAX_ACCOUNTS] []
        [ φ input; φ accounts ]
        Self.
    Proof.
      constructor.
      run_symbolic.
      - admit. 
      - admit.
      - admit.
    Admitted.
    Global Opaque run_deserialize.
  End deserialize.

  Module parse.
    Parameter MAX_ACCOUNTS : Usize.t.

    Definition Self : Set := (Ref.t Pointer.Kind.Raw U8.t *
                              Usize.t *
                              Ref.t Pointer.Kind.Ref (list U8.t))%type.

    Instance run
      (input : Ref.t Pointer.Kind.Raw U8.t)
      (accounts : Ref.t Pointer.Kind.Ref (array.t AccountInfo.t MAX_ACCOUNTS)) :
      Run.Trait
        pinocchio.entrypoint.mod.entrypoint.parse
        [φ MAX_ACCOUNTS] []
        [ φ input; φ accounts ]
        Self.
    Proof.
      constructor.
      run_symbolic.
      - admit. 
      - admit.
      - admit. 
    Admitted.
    Global Opaque run.
  End parse.
End entrypoint.
