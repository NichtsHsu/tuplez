//! Provides the ability to get subsets of tuples.
//!
//! Check the documentation page of [`Subset`] for details.

use crate::{Tuple, TupleLike, Unit};
use std::marker::PhantomData;

/// Helper class for [`Subset`], indicates that the current element is included by the subset.
pub struct Used<T>(PhantomData<T>);

/// Helper class for [`Subset`], indicates that the current element is excluded by the subset.
pub struct Unused<T>(PhantomData<T>);

/// Search for subsets of tuples.
///
/// There are currently a lot of restrictions: No two elements in the subset can have the same type,
/// all the element types of subset have only one occurrence in the superset, and the order
/// of the elements of subset must be consistent with the order of the superset.
pub trait Subset<Set, I>: TupleLike
where
    Set: TupleLike,
{
    /// Take out the subset.
    ///
    /// Add a type annotation to the subset to let [`subset()`](TupleLike::subset()) know.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`subset()`](TupleLike::subset()) method as the wrapper
    /// for this [`subset()`](Subset::subset()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(12, "hello", 24, 3.14, true);
    /// let subset: tuple_t!(&str, bool) = tup.subset();
    /// assert_eq!(subset, tuple!("hello", true));
    ///
    /// // `i32` appears twice in superset, cannot infer which to use.
    /// // let subset: tuple_t!(i32, bool) = tup.subset();
    ///
    /// // The order of elements in the subset is inconsistent with the superset.
    /// // Cannot compile.
    /// // let subset: tuple_t!(bool, &str) = tup.subset();
    /// ```
    fn subset(self) -> Set;

    /// Get a subset, but all its elements are immutable references to the superset's elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`subset_ref()`](TupleLike::subset_ref()) method as
    /// the wrapper for this [`subset_ref()`](Subset::subset_ref()) method.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation ,
    /// so you need to call it like:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(12, "hello", vec![1, 2, 3], 24, 3.14, true);
    /// let subset = tup.subset_ref::<tuple_t!(&'static str, bool), _>();
    /// assert_eq!(subset, tuple!(&"hello", &true));
    /// ```
    fn subset_ref(&self) -> Set::AsRefOutput<'_>;

    /// Get a subset, but all its elements are mutable references to the superset's elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`subset_mut()`](TupleLike::subset_mut()) method as
    /// the wrapper for this [`subset_mut()`](Subset::subset_mut()) method.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation ,
    /// so you need to call it like:
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(12, "hello", vec![1, 2, 3], 24, 3.14, true);
    /// let subset = tup.subset_mut::<tuple_t!(&'static str, bool), _>();
    /// *get!(subset; 0) = "world";
    /// *get!(subset; 1) = false;
    /// assert_eq!(tup, tuple!(12, "world", vec![1, 2, 3], 24, 3.14, false));
    /// ```
    fn subset_mut(&mut self) -> Set::AsMutOutput<'_>;
}

impl Subset<Unit, Unit> for Unit {
    fn subset(self) -> Unit {
        Unit
    }
    fn subset_ref(&self) -> <Unit as TupleLike>::AsRefOutput<'_> {
        Unit
    }
    fn subset_mut(&mut self) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }
}

impl<First, Other1, Other2, I> Subset<Tuple<First, Other2>, Used<I>> for Tuple<First, Other1>
where
    Other1: TupleLike + Subset<Other2, I>,
    Other2: TupleLike,
{
    fn subset(self) -> Tuple<First, Other2> {
        Tuple(self.0, Subset::subset(self.1))
    }
    fn subset_ref(&self) -> <Tuple<First, Other2> as TupleLike>::AsRefOutput<'_> {
        Tuple(&self.0, Subset::subset_ref(&self.1))
    }
    fn subset_mut(&mut self) -> <Tuple<First, Other2> as TupleLike>::AsMutOutput<'_> {
        Tuple(&mut self.0, Subset::subset_mut(&mut self.1))
    }
}

impl<First, Other, T, I> Subset<T, Unused<I>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: TupleLike + Subset<T, I>,
{
    fn subset(self) -> T {
        Subset::subset(self.1)
    }

    fn subset_ref(&self) -> <T as TupleLike>::AsRefOutput<'_> {
        Subset::subset_ref(&self.1)
    }

    fn subset_mut(&mut self) -> <T as TupleLike>::AsMutOutput<'_> {
        Subset::subset_mut(&mut self.1)
    }
}
