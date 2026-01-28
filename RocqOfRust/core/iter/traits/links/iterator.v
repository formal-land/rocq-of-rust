Require Import links.RocqOfRust.
Require Import core.array.links.iter_IntoIter.
Require Import core.iter.adapters.links.map_Map.
Require Import core.iter.traits.iterator.
Require Import core.links.array.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.num.links.nonzero.
Require Import core.ops.links.function.

(* pub trait Iterator *)
Module Iterator.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::iter::traits::iterator::Iterator";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  (* fn next(&mut self) -> Option<Self::Item>; *)
  Class Method_next
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
    next : PolymorphicFunction.t;
    next_is_method :: IsTraitMethod.C (trait Self) "next" next;
    run_next (self : '&mut Self) :: Run.Trait next [] [] [φ self] (option Item);
  }.

  (*
  fn next_chunk<const N: usize>(
      &mut self,
  ) -> Result<[Self::Item; N], IntoIter<Self::Item, N>>
  *)
  Class Method_next_chunk
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
    next_chunk : PolymorphicFunction.t;
    next_chunk_is_method :: IsTraitMethod.C (trait Self) "next_chunk" next_chunk;
    run_next_chunk (N : usize) (self : '&mut Self) ::
      Run.Trait next_chunk [] [] [φ self] (Result.t (array.t Item N) (IntoIter.t Item N));
  }.

  (* fn size_hint(&self) -> (usize, Option<usize>) { ... } *)
  Class Method_size_hint
      (Self : Set) `{Link Self} :
      Set := {
    size_hint : PolymorphicFunction.t;
    size_hint_is_method :: IsTraitMethod.C (trait Self) "size_hint" size_hint;
    run_size_hint (self : '& Self) :: Run.Trait size_hint [] [] [φ self] (usize * option usize);
  }.

  (* fn count(self) -> usize *)
  Class Method_count
      (Self : Set) `{Link Self} :
      Set := {
    count : PolymorphicFunction.t;
    count_is_method :: IsTraitMethod.C (trait Self) "count" count;
    run_count (self : Self) :: Run.Trait count [] [] [φ self] usize;
  }.

  (* fn last(self) -> Option<Self::Item> *)
  Class Method_last
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
    last : PolymorphicFunction.t;
    last_is_method :: IsTraitMethod.C (trait Self) "last" last;
    run_last (self : Self) :: Run.Trait last [] [] [φ self] (option Item);
  }.

  (* fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> *)
  Class Method_advance_by
      (Self : Set) `{Link Self} :
      Set := {
    advance_by : PolymorphicFunction.t;
    advance_by_is_method :: IsTraitMethod.C (trait Self) "advance_by" advance_by;
    run_advance_by (self : '&mut Self) (n : usize) ::
      Run.Trait advance_by [] [] [φ self; φ n] (Result.t unit (NonZero.t usize));
  }.

  (*
    fn nth(&mut self, n: usize) -> Option<Self::Item> { ... }
    fn step_by(self, step: usize) -> StepBy<Self> ⓘ
       where Self: Sized { ... }
    fn chain<U>(self, other: U) -> Chain<Self, U::IntoIter> ⓘ
       where Self: Sized,
             U: IntoIterator<Item = Self::Item> { ... }
    fn zip<U>(self, other: U) -> Zip<Self, U::IntoIter> ⓘ
       where Self: Sized,
             U: IntoIterator { ... }
    fn intersperse(self, separator: Self::Item) -> Intersperse<Self> ⓘ
       where Self: Sized,
             Self::Item: Clone { ... }
    fn intersperse_with<G>(self, separator: G) -> IntersperseWith<Self, G> ⓘ
       where Self: Sized,
             G: FnMut() -> Self::Item { ... }
   *)

    (*
      fn map<B, F>(self, f: F) -> Map<Self, F> ⓘ
         where Self: Sized,
               F: FnMut(Self::Item) -> B { ... }
   *)
   Class Method_map
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
    map : PolymorphicFunction.t;
    map_is_method :: IsTraitMethod.C (trait Self) "map" map;
    run_map (B F : Set) `(Link B) `(Link F) (self : Self) (f : F) ::
      Run.Trait map [] [Φ B; Φ F] [φ self; φ f] (Map.t Self F);
  }.

   (*
    fn for_each<F>(self, f: F)
       where Self: Sized,
             F: FnMut(Self::Item) { ... }
    fn filter<P>(self, predicate: P) -> Filter<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn filter_map<B, F>(self, f: F) -> FilterMap<Self, F> ⓘ
       where Self: Sized,
             F: FnMut(Self::Item) -> Option<B> { ... }
    fn enumerate(self) -> Enumerate<Self> ⓘ
       where Self: Sized { ... }
    fn peekable(self) -> Peekable<Self> ⓘ
       where Self: Sized { ... }
    fn skip_while<P>(self, predicate: P) -> SkipWhile<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn take_while<P>(self, predicate: P) -> TakeWhile<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn map_while<B, P>(self, predicate: P) -> MapWhile<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(Self::Item) -> Option<B> { ... }
    fn skip(self, n: usize) -> Skip<Self> ⓘ
       where Self: Sized { ... }
    fn take(self, n: usize) -> Take<Self> ⓘ
       where Self: Sized { ... }
    fn scan<St, B, F>(self, initial_state: St, f: F) -> Scan<Self, St, F> ⓘ
       where Self: Sized,
             F: FnMut(&mut St, Self::Item) -> Option<B> { ... }
    fn flat_map<U, F>(self, f: F) -> FlatMap<Self, U, F> ⓘ
       where Self: Sized,
             U: IntoIterator,
             F: FnMut(Self::Item) -> U { ... }
    fn flatten(self) -> Flatten<Self> ⓘ
       where Self: Sized,
             Self::Item: IntoIterator { ... }
    fn map_windows<F, R, const N: usize>(self, f: F) -> MapWindows<Self, F, N> ⓘ
       where Self: Sized,
             F: FnMut(&[Self::Item; N]) -> R { ... }
    fn fuse(self) -> Fuse<Self> ⓘ
       where Self: Sized { ... }
    fn inspect<F>(self, f: F) -> Inspect<Self, F> ⓘ
       where Self: Sized,
             F: FnMut(&Self::Item) { ... }
    fn by_ref(&mut self) -> &mut Self
       where Self: Sized { ... }
    *)

    (*
    fn collect<B: FromIterator<Self::Item>>(self) -> B
       where Self: Sized { ... }
    *)
    Class Method_collect
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
    collect : PolymorphicFunction.t;
    collect_is_method :: IsTraitMethod.C (trait Self) "collect" collect;
    run_collect (B : Set) `(Link B) (self : Self) :: Run.Trait collect [] [Φ B] [φ self] B;
  }.

    (*
    fn try_collect<B>(
        &mut self,
    ) -> <Self::Item::Residual as Residual<B>>::TryType
       where Self: Sized,
             Self::Item: Try<Residual: Residual<B>>,
             B: FromIterator<<Self::Item as Try>::Output> { ... }
    fn collect_into<E: Extend<Self::Item>>(self, collection: &mut E) -> &mut E
       where Self: Sized { ... }
    fn partition<B, F>(self, f: F) -> (B, B)
       where Self: Sized,
             B: Default + Extend<Self::Item>,
             F: FnMut(&Self::Item) -> bool { ... }
    fn partition_in_place<'a, T: 'a, P>(self, predicate: P) -> usize
       where Self: Sized + DoubleEndedIterator<Item = &'a mut T>,
             P: FnMut(&T) -> bool { ... }
    fn is_partitioned<P>(self, predicate: P) -> bool
       where Self: Sized,
             P: FnMut(Self::Item) -> bool { ... }
    fn try_fold<B, F, R>(&mut self, init: B, f: F) -> R
       where Self: Sized,
             F: FnMut(B, Self::Item) -> R,
             R: Try<Output = B> { ... }
    fn try_for_each<F, R>(&mut self, f: F) -> R
       where Self: Sized,
             F: FnMut(Self::Item) -> R,
             R: Try<Output = ()> { ... }
   *)

   (*
   fn fold<B, F>(self, init: B, f: F) -> B
      where Self: Sized,
            F: FnMut(B, Self::Item) -> B { ... }
   *)
   Class Method_fold
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
    fold : PolymorphicFunction.t;
    fold_is_method :: IsTraitMethod.C (trait Self) "fold" fold;
    run_fold (B F : Set) `(Link B) `(Link F) (self : Self) (init : B) (f : F) ::
      Run.Trait fold [] [Φ B; Φ F] [φ self; φ init; φ f] B;
  }.

   (*
    fn reduce<F>(self, f: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(Self::Item, Self::Item) -> Self::Item { ... }
    fn try_reduce<R>(
        &mut self,
        f: impl FnMut(Self::Item, Self::Item) -> R,
    ) -> <R::Residual as Residual<Option<R::Output>>>::TryType
       where Self: Sized,
             R: Try<Output = Self::Item, Residual: Residual<Option<Self::Item>>> { ... }
    fn all<F>(&mut self, f: F) -> bool
       where Self: Sized,
             F: FnMut(Self::Item) -> bool { ... }
  *)

  (*
  fn any<F>(&mut self, f: F) -> bool
      where Self: Sized,
            F: FnMut(Self::Item) -> bool { ... }
  *)
  Class Method_any
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
    any : PolymorphicFunction.t;
    any_is_method :: IsTraitMethod.C (trait Self) "any" any;
    run_any (F : Set) `(Link F) (self : '&mut Self) (f : F) `(FnMut.Run F Item bool) ::
      Run.Trait any [] [Φ F] [φ self; φ f] bool;
  }.

  (*
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn find_map<B, F>(&mut self, f: F) -> Option<B>
       where Self: Sized,
             F: FnMut(Self::Item) -> Option<B> { ... }
    fn try_find<R>(
        &mut self,
        f: impl FnMut(&Self::Item) -> R,
    ) -> <R::Residual as Residual<Option<Self::Item>>>::TryType
       where Self: Sized,
             R: Try<Output = bool, Residual: Residual<Option<Self::Item>>> { ... }
    fn position<P>(&mut self, predicate: P) -> Option<usize>
       where Self: Sized,
             P: FnMut(Self::Item) -> bool { ... }
    fn rposition<P>(&mut self, predicate: P) -> Option<usize>
       where P: FnMut(Self::Item) -> bool,
             Self: Sized + ExactSizeIterator + DoubleEndedIterator { ... }
    fn max(self) -> Option<Self::Item>
       where Self: Sized,
             Self::Item: Ord { ... }
    fn min(self) -> Option<Self::Item>
       where Self: Sized,
             Self::Item: Ord { ... }
    fn max_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item) -> B { ... }
    fn max_by<F>(self, compare: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item, &Self::Item) -> Ordering { ... }
    fn min_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item) -> B { ... }
    fn min_by<F>(self, compare: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item, &Self::Item) -> Ordering { ... }
    fn rev(self) -> Rev<Self> ⓘ
       where Self: Sized + DoubleEndedIterator { ... }
    fn unzip<A, B, FromA, FromB>(self) -> (FromA, FromB)
       where FromA: Default + Extend<A>,
             FromB: Default + Extend<B>,
             Self: Sized + Iterator<Item = (A, B)> { ... }
    fn copied<'a, T>(self) -> Copied<Self> ⓘ
       where Self: Sized + Iterator<Item = &'a T>,
             T: Copy + 'a { ... }
    fn cloned<'a, T>(self) -> Cloned<Self> ⓘ
       where Self: Sized + Iterator<Item = &'a T>,
             T: Clone + 'a { ... }
    fn cycle(self) -> Cycle<Self> ⓘ
       where Self: Sized + Clone { ... }
    fn array_chunks<const N: usize>(self) -> ArrayChunks<Self, N> ⓘ
       where Self: Sized { ... }
    fn sum<S>(self) -> S
       where Self: Sized,
             S: Sum<Self::Item> { ... }
    fn product<P>(self) -> P
       where Self: Sized,
             P: Product<Self::Item> { ... }
    fn cmp<I>(self, other: I) -> Ordering
       where I: IntoIterator<Item = Self::Item>,
             Self::Item: Ord,
             Self: Sized { ... }
    fn cmp_by<I, F>(self, other: I, cmp: F) -> Ordering
       where Self: Sized,
             I: IntoIterator,
             F: FnMut(Self::Item, I::Item) -> Ordering { ... }
    fn partial_cmp<I>(self, other: I) -> Option<Ordering>
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn partial_cmp_by<I, F>(self, other: I, partial_cmp: F) -> Option<Ordering>
       where Self: Sized,
             I: IntoIterator,
             F: FnMut(Self::Item, I::Item) -> Option<Ordering> { ... }
    fn eq<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialEq<I::Item>,
             Self: Sized { ... }
    fn eq_by<I, F>(self, other: I, eq: F) -> bool
       where Self: Sized,
             I: IntoIterator,
             F: FnMut(Self::Item, I::Item) -> bool { ... }
    fn ne<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialEq<I::Item>,
             Self: Sized { ... }
    fn lt<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn le<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn gt<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn ge<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn is_sorted(self) -> bool
       where Self: Sized,
             Self::Item: PartialOrd { ... }
    fn is_sorted_by<F>(self, compare: F) -> bool
       where Self: Sized,
             F: FnMut(&Self::Item, &Self::Item) -> bool { ... }
    fn is_sorted_by_key<F, K>(self, f: F) -> bool
       where Self: Sized,
             F: FnMut(Self::Item) -> K,
             K: PartialOrd { ... }
  *)

  Class Run
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
   (* type Item; *)
    Item_IsAssociated :
      IsTraitAssociatedType
        "core::iter::traits::iterator::Iterator" [] [] (Φ Self)
        "Item" (Φ Item);
    method_next :: Method_next Self Item;
    method_next_chunk :: Method_next_chunk Self Item;
    method_size_hint :: Method_size_hint Self;
    method_count :: Method_count Self;
    method_last :: Method_last Self Item;
    method_advance_by :: Method_advance_by Self;
    method_map :: Method_map Self Item;
    method_collect :: Method_collect Self Item;
    method_fold :: Method_fold Self Item;
    method_any :: Method_any Self Item;
  }.
End Iterator.
Export (hints) Iterator.
