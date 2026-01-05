Require Import RocqOfRust.RocqOfRust.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloc.vec.links.mod.
Require Import core.links.result.
Require Import revm_bytecode.eof.header.

Module EofHeader.
  Record t : Set := {
    types_size: u16;
    code_sizes: Vec.t u16 Global.t;
    container_sizes: Vec.t u16 Global.t;
    data_size: u16;
    sum_code_sizes: usize;
    sum_container_sizes: usize;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::header::EofHeader";
    φ '(Build_t types_size code_sizes container_sizes data_size sum_code_sizes sum_container_sizes) :=
      Value.StructRecord "revm_bytecode::eof::header::EofHeader" [] [] [
        ("types_size", φ types_size);
        ("code_sizes", φ code_sizes);
        ("container_sizes", φ container_sizes);
        ("data_size", φ data_size);
        ("sum_code_sizes", φ sum_code_sizes);
        ("sum_container_sizes", φ sum_container_sizes)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::header::EofHeader").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
      types_size' types_size
      code_sizes' code_sizes
      container_sizes' container_sizes
      data_size' data_size
      sum_code_sizes' sum_code_sizes
      sum_container_sizes' sum_container_sizes :
    types_size' = φ types_size ->
    code_sizes' = φ code_sizes ->
    container_sizes' = φ container_sizes ->
    data_size' = φ data_size ->
    sum_code_sizes' = φ sum_code_sizes ->
    sum_container_sizes' = φ sum_container_sizes ->
    Value.StructRecord "revm_bytecode::eof::header::EofHeader" [] [] [
      ("types_size", types_size');
      ("code_sizes", code_sizes');
      ("container_sizes", container_sizes');
      ("data_size", data_size');
      ("sum_code_sizes", sum_code_sizes');
      ("sum_container_sizes", sum_container_sizes')
    ] =
    φ (Build_t types_size code_sizes container_sizes data_size sum_code_sizes sum_container_sizes).
  Proof.
    intros; now subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.

  Definition of_value
      types_size' (types_size : u16)
      code_sizes' (code_sizes : Vec.t u16 Global.t)
      container_sizes' (container_sizes : Vec.t u16 Global.t)
      data_size' (data_size : u16)
      sum_code_sizes' (sum_code_sizes : usize)
      sum_container_sizes' (sum_container_sizes : usize) :
    types_size' = φ types_size ->
    code_sizes' = φ code_sizes ->
    container_sizes' = φ container_sizes ->
    data_size' = φ data_size ->
    sum_code_sizes' = φ sum_code_sizes ->
    sum_container_sizes' = φ sum_container_sizes ->
    OfValue.t (
      Value.StructRecord "revm_bytecode::eof::header::EofHeader" [] [] [
        ("types_size", types_size');
        ("code_sizes", code_sizes');
        ("container_sizes", container_sizes');
        ("data_size", data_size');
        ("sum_code_sizes", sum_code_sizes');
        ("sum_container_sizes", sum_container_sizes')
      ]
    ).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add unshelve eapply of_value : of_value.

  Module SubPointer.
    Definition get_types_size : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::header::EofHeader" "types_size") :=
    {|
      SubPointer.Runner.projection x := Some x.(types_size);
      SubPointer.Runner.injection x y := Some (x <| types_size := y |>);
    |}.

    Lemma get_types_size_is_valid :
      SubPointer.Runner.Valid.t get_types_size.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_types_size_is_valid : run_sub_pointer.

    Definition get_code_sizes : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::header::EofHeader" "code_sizes") :=
    {|
      SubPointer.Runner.projection x := Some x.(code_sizes);
      SubPointer.Runner.injection x y := Some (x <| code_sizes := y |>);
    |}.

    Lemma get_code_sizes_is_valid :
      SubPointer.Runner.Valid.t get_code_sizes.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_code_sizes_is_valid : run_sub_pointer.

    Definition get_container_sizes : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::header::EofHeader" "container_sizes") :=
    {|
      SubPointer.Runner.projection x := Some x.(container_sizes);
      SubPointer.Runner.injection x y := Some (x <| container_sizes := y |>);
    |}.

    Lemma get_container_sizes_is_valid :
      SubPointer.Runner.Valid.t get_container_sizes.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_container_sizes_is_valid : run_sub_pointer.

    Definition get_data_size : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::header::EofHeader" "data_size") :=
    {|
      SubPointer.Runner.projection x := Some x.(data_size);
      SubPointer.Runner.injection x y := Some (x <| data_size := y |>);
    |}.

    Lemma get_data_size_is_valid :
      SubPointer.Runner.Valid.t get_data_size.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_data_size_is_valid : run_sub_pointer.

    Definition get_sum_code_sizes : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::header::EofHeader" "sum_code_sizes") :=
    {|
      SubPointer.Runner.projection x := Some x.(sum_code_sizes);
      SubPointer.Runner.injection x y := Some (x <| sum_code_sizes := y |>);
    |}.

    Lemma get_sum_code_sizes_is_valid :
      SubPointer.Runner.Valid.t get_sum_code_sizes.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_sum_code_sizes_is_valid : run_sub_pointer.

    Definition get_sum_container_sizes : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::header::EofHeader" "sum_container_sizes") :=
    {|
      SubPointer.Runner.projection x := Some x.(sum_container_sizes);
      SubPointer.Runner.injection x y := Some (x <| sum_container_sizes := y |>);
    |}.

    Lemma get_sum_container_sizes_is_valid :
      SubPointer.Runner.Valid.t get_sum_container_sizes.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_sum_container_sizes_is_valid : run_sub_pointer.
  End SubPointer.
End EofHeader.

Module Impl_EofHeader.
  Definition Self : Set := EofHeader.t.

  (*
    pub fn size(&self) -> usize
  *)
  Instance run_size (self : '& Self) : 
    Run.Trait header.eof.header.Impl_revm_bytecode_eof_header_EofHeader.size [] [] [φ self] usize.
  Admitted.
  Global Opaque run_size.

  (* pub fn eof_size(&self) -> usize *)
  Instance run_eof_size (self : '& Self) :
    Run.Trait header.eof.header.Impl_revm_bytecode_eof_header_EofHeader.eof_size [] [] [φ self]
      usize.
  Admitted.
  Global Opaque run_eof_size.

  (*
    pub fn encode(&self, buffer: &mut Vec<u8>)
  *)
  Instance run_encode (self : '& Self) (buffer : '*mut (Vec.t u8 Global.t)) :
    Run.Trait header.eof.header.Impl_revm_bytecode_eof_header_EofHeader.encode [] [] [φ self; φ buffer] unit.
  Admitted.
  Global Opaque run_encode.

  (* pub fn decode(input: &[u8]) -> Result<(Self, &[u8]), EofDecodeError> *)
  Instance run_decode (input : '& (list u8)) :
    Run.Trait header.eof.header.Impl_revm_bytecode_eof_header_EofHeader.decode [] [] [φ input]
      (Result.t Self ('& (list u8))).
  Admitted.
  Global Opaque run_decode.
End Impl_EofHeader.
Export Impl_EofHeader.
