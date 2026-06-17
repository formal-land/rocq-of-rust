Require Import links.RocqOfRust.
Require Import core.links.option.
Require Import core.slice.mod.
Require Import core.slice.links.index.
Require Import core.slice.links.iter.

Module Impl_Slice.
  Definition Self (T : Set) : Set :=
    list T.

  (*
    pub fn get<I>(&self, index: I) -> Option<&I::Output>
    where
        I: SliceIndex<Self>,
  *)
  Instance run_get
      (T : Set) `{Link T}
      {I : Set} `{Link I} 
      {Output : Set} `{Link Output}
      {run_SliceIndex_for_I : SliceIndex.Run I (Self T) Output}
      (self : '& (Self T)) 
      (index : I) :
    Run.Trait (slice.Impl_slice_T.get (Φ T)) [] [Φ I] [φ self; φ index]
      (option ('& Output)).
  Admitted.
  Global Opaque run_get.

  (*
    pub unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut I::Output
        where
            I: SliceIndex<Self>,
  *)
  Instance run_get_unchecked_mut 
      (T : Set) `{Link T}
      {I : Set} `{Link I} 
      {Output : Set} `{Link Output}
      {run_SliceIndex_for_I : SliceIndex.Run I (Self T) Output}
      (self : '&mut (Self T)) 
      (index : I) :
    Run.Trait (slice.Impl_slice_T.get_unchecked_mut (Φ T)) [] [Φ I] [φ self; φ index]
      ('&mut Output).
  Admitted.
  Global Opaque run_get_unchecked_mut.

  (* pub const fn len(&self) -> usize *)
  Instance run_len
      {T : Set} `{Link T}
      (self : '& (Self T)) :
    Run.Trait (slice.Impl_slice_T.len (Φ T)) [] [] [φ self]
      usize.
  Admitted.
  Global Opaque run_len.

  (* pub const fn is_empty(&self) -> bool *)
  Instance run_is_empty
      {T : Set} `{Link T}
      (self : '& (Self T)) :
    Run.Trait (slice.Impl_slice_T.is_empty (Φ T)) [] [] [φ self]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_is_empty.

  (* pub fn iter(&self) -> Iter<'_, T> *)
  Instance run_iter
      (T : Set) `{Link T}
      (self : '& (Self T)) :
    Run.Trait (slice.Impl_slice_T.iter (Φ T)) [] [] [φ self]
      (Iter.t T).
  Admitted.
  Global Opaque run_iter.

  (* pub fn iter_mut(&mut self) -> IterMut<'_, T> *)
  Instance run_iter_mut
      (T : Set) `{Link T}
      (self : '&mut (Self T)) :
    Run.Trait (slice.Impl_slice_T.iter_mut (Φ T)) [] [] [φ self]
      (IterMut.t T).
  Admitted.
  Global Opaque run_iter_mut.

  (* pub const fn last_mut(&mut self) -> Option<&mut T> *)
  Instance run_last_mut
      (T : Set) `{Link T}
      (self : '&mut (Self T)) :
    Run.Trait (slice.Impl_slice_T.last_mut (Φ T)) [] [] [φ self]
      (option ('&mut T)).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_last_mut.

  (* pub const fn as_ptr(&self) -> *const T *)
  Instance run_as_ptr
      (T : Set) `{Link T}
      (self : '& (Self T)) :
    Run.Trait (slice.Impl_slice_T.as_ptr (Φ T)) [] [] [φ self]
      ('*const T).
  Admitted.
  Global Opaque run_as_ptr.

  (* pub const fn as_mut_ptr(&mut self) -> *mut T *)
  Instance run_as_mut_ptr
      (T : Set) `{Link T}
      (self : '&mut (Self T)) :
    Run.Trait (slice.Impl_slice_T.as_mut_ptr (Φ T)) [] [] [φ self]
      ('*mut T).
  Admitted.
  Global Opaque run_as_mut_ptr.

  (* pub fn chunks_exact(&self, chunk_size: usize) -> ChunksExact<'_, T> *)
  Instance run_chunks_exact
      (T : Set) `{Link T}
      (self : '& (Self T))
      (chunk_size : usize) :
    Run.Trait (slice.Impl_slice_T.chunks_exact (Φ T)) [] [] [φ self; φ chunk_size]
      (ChunksExact.t T).
  Admitted.
  Global Opaque run_chunks_exact.

  (* pub fn rchunks_exact(&self, chunk_size: usize) -> RChunksExact<'_, T> *)
  Instance run_rchunks_exact
      (T : Set) `{Link T}
      (self : '& (Self T))
      (chunk_size : usize) :
    Run.Trait (slice.Impl_slice_T.rchunks_exact (Φ T)) [] [] [φ self; φ chunk_size]
      (RChunksExact.t T).
  Admitted.
  Global Opaque run_rchunks_exact.

  (*
  pub const fn copy_from_slice(&mut self, src: &[T])
  where
      T: Copy,
  *)
  Instance run_copy_from_slice
      (T : Set) `{Link T}
      (self : '&mut (Self T))
      (src : '& (Self T)) :
    Run.Trait (slice.Impl_slice_T.copy_from_slice (Φ T)) [] [] [φ self; φ src]
      unit.
  Admitted.
  Global Opaque run_copy_from_slice.
End Impl_Slice.
Export (hints) Impl_Slice.
