Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.array.
Require Import pinocchio.links.account_info.
Require Import pinocchio.entrypoint.mod.

Module entrypoint.
  Module deserialize.

    Parameter MAX_ACCOUNTS : usize.

    Definition Self : Set := ('& u8 *
                              usize *
                              '& (list u8))%type.

    Instance run_deserialize
      (input : '* u8)
      (accounts : '& (array.t AccountInfo.t MAX_ACCOUNTS)) :
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
    Parameter MAX_ACCOUNTS : usize.

    Definition Self : Set := ('* u8 *
                              usize *
                              '& (list u8))%type.

    Instance run
      (input : '* u8)
      (accounts : '& (array.t AccountInfo.t MAX_ACCOUNTS)) :
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
