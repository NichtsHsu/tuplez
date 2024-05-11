//! Provides the ability to search tuple elements by type.
//!
//! Check the documentation page of [`Search`] for details.

use crate::{Tuple, TupleLenEqTo, TupleLike, Unit};
use std::marker::PhantomData;

/// Helper type indicates that the search has been completed.
pub struct Complete;

/// Helper type indicates that current element is excluded by the search result.
pub struct Unused<I>(PhantomData<I>);

/// Helper type indicates that current element is included by the search result.
pub struct Used<T>(PhantomData<T>);

/// Search for an element of a specific type in a tuple.
///
/// There is currently a restriction: only one element in the tuple can be of the type being searched.
pub trait Search<T, I>: TupleLike {
    /// The type of the remainder of the tuple after taking out the searched element.
    type TakeRemainder: TupleLike;

    /// Take out the searched element, and get the remainder of tuple.
    ///
    /// Add a type annotation to the searched element to let [`take()`](TupleLike::take()) know which one you want.
    ///
    /// If you want to take out the element at a specific index, see [`take!`](crate::take!).
    ///
    /// If you want to take out the first or last element, see [`pop()`][TupleLike::pop()].
    ///
    /// Hint: The [`TupleLike`] trait provides the [`take()`](TupleLike::take()) method as the wrapper
    /// for this [`take()`](Search::take()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let (value, remainder): (i32, _) = tup.take();      // Add type annotation for `value`
    /// assert_eq!(value, 5);
    /// assert_eq!(remainder, tuple!(3.14, "hello", [1, 2, 3]));
    /// ```
    ///
    /// If you cannot add a type annotation, you can also use the [`take!`](crate::take!) macro:
    ///
    /// ```
    /// use tuplez::{take, tuple};
    ///
    /// let tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let (value, remainder) = take!(tup; i32);
    /// assert_eq!(value, 5);
    /// assert_eq!(remainder, tuple!(3.14, "hello", [1, 2, 3]));
    /// ```
    fn take(self) -> (T, Self::TakeRemainder);

    /// Get an immutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`get_ref()`](TupleLike::get_ref()) know which one you want.
    ///
    /// If you want to get the element by its index, see [`get!`](crate::get!);
    ///
    /// Hint: The [`TupleLike`] trait provides the [`get_ref()`](TupleLike::get_ref()) method as the wrapper
    /// for this [`get_ref()`](Search::get_ref()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let arr: &[i32; 3] = tup.get_ref();
    /// assert_eq!(arr, &[1, 2, 3]);
    /// ```
    fn get_ref(&self) -> &T;

    /// Get a mutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`get_mut()`](TupleLike::get_mut()) know which one you want.
    ///
    /// If you want to get the element by its index, see [`get!`](crate::get!);
    ///
    /// Hint: The [`TupleLike`] trait provides the [`get_mut()`](TupleLike::get_mut()) method as the wrapper
    /// for this [`get_mut()`](Search::get_mut()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let s: &mut &str = tup.get_mut();
    /// *s = "world";
    /// assert_eq!(tup, tuple!(3.14, "world", 5, [1, 2, 3]));
    /// ```
    fn get_mut(&mut self) -> &mut T;
}

impl<First, Other> Search<First, Complete> for Tuple<First, Other>
where
    Other: TupleLike,
{
    type TakeRemainder = Other;

    fn take(self) -> (First, Self::TakeRemainder) {
        (self.0, self.1)
    }

    fn get_ref(&self) -> &First {
        &self.0
    }

    fn get_mut(&mut self) -> &mut First {
        &mut self.0
    }
}

impl<First, Other, T, I> Search<T, Unused<I>> for Tuple<First, Other>
where
    Other: Search<T, I>,
{
    type TakeRemainder = Tuple<First, Other::TakeRemainder>;

    fn take(self) -> (T, Self::TakeRemainder) {
        let (value, remainder) = Search::take(self.1);
        (value, Tuple(self.0, remainder))
    }

    fn get_ref(&self) -> &T {
        Search::get_ref(&self.1)
    }

    fn get_mut(&mut self) -> &mut T {
        Search::get_mut(&mut self.1)
    }
}

/// replace tail elements of the tuple.
pub trait TailReplaceable<T: TupleLike, I>: TupleLike {
    /// The type of the tuple after replacing its elements.
    type ReplaceOutput: TupleLike;

    /// The type of the tuple that collect all replaced elements.
    type Replaced: TupleLike;

    /// Replace the last N elements of the tuple with all elements of another tuple of N elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`replace_tail()`](TupleLike::replace_tail()) method as the wrapper
    /// for this [`replace_tail()`](TailReplaceable::replace_tail()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "2", 3.0, Some(4));
    /// let tup2 = tuple!("z", 8);
    /// let (output, replaced) = tup.replace_tail(tup2);
    /// assert_eq!(output, tuple!(1, "2", "z", 8));
    /// assert_eq!(replaced, tuple!(3.0, Some(4)));
    /// ```
    fn replace_tail(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced);
}

impl<T, U> TailReplaceable<T, Complete> for U
where
    T: TupleLenEqTo<U>,
    U: TupleLike,
{
    type ReplaceOutput = T;
    type Replaced = U;

    fn replace_tail(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced) {
        (rhs, self)
    }
}

impl<First, Other, T, I> TailReplaceable<T, Unused<I>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: TailReplaceable<T, I>,
{
    type ReplaceOutput = Tuple<First, Other::ReplaceOutput>;
    type Replaced = Other::Replaced;

    fn replace_tail(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced) {
        let (output, replaced) = TailReplaceable::replace_tail(self.1, rhs);
        (Tuple(self.0, output), replaced)
    }
}

/// Search for subsequences of tuples.
///
/// The subsequence must have one and only one candidate in the supersequence.
pub trait Subseq<Seq, I>: TupleLike
where
    Seq: TupleLike,
{
    /// Take out a subsequence.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Add a type annotation to the subsequence to let [`subseq()`](Subseq::subseq()) know.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`subseq()`](TupleLike::subseq()) method as the wrapper
    /// for this [`subseq()`](Subseq::subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(12, "hello", 24, 3.14, true);
    /// let subseq: tuple_t!(&str, bool) = tup.subseq();
    /// assert_eq!(subseq, tuple!("hello", true));
    ///
    /// // Two candidates available: `(12, true)` or `(24, true)`.
    /// // let subseq: tuple_t!(i32, bool) = tup.subseq();
    ///
    /// // No candidates available.
    /// // `(true, "hello")` cannot be a candidate, since its element order is
    /// // different from the supersequence.
    /// // let subseq: tuple_t!(bool, &str) = tup.subseq();
    ///
    /// // Although `24` is also `i32`, but only `(12, "hello")` is a candidate.
    /// let subseq: tuple_t!(i32, &str) = tup.subseq();
    /// assert_eq!(subseq, tuple!(12, "hello"));
    ///
    /// // It's OK to pick all `i32`s since there is only one candidate.
    /// let subseq: tuple_t!(i32, i32) = tup.subseq();
    /// assert_eq!(subseq, tuple!(12, 24));
    /// ```
    fn subseq(self) -> Seq;

    /// Similar to [`subseq()`](Subseq::subseq()),
    /// but all its elements are immutable references to the supersequence's elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`subseq_ref()`](TupleLike::subseq_ref()) method as
    /// the wrapper for this [`subseq_ref()`](Subseq::subseq_ref()) method.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation,
    /// so you need to call it like:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(12, "hello", vec![1, 2, 3], 24, 3.14, true);
    /// let subseq = tup.subseq_ref::<tuple_t!(&'static str, bool), _>();
    /// assert_eq!(subseq, tuple!(&"hello", &true));
    /// ```
    fn subseq_ref(&self) -> Seq::AsRefOutput<'_>;

    /// Similar to [`subseq()`](Subseq::subseq()),
    /// but all its elements are mutable references to the supersequence's elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`subseq_mut()`](TupleLike::subseq_mut()) method as
    /// the wrapper for this [`subseq_mut()`](Subseq::subseq_mut()) method.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation,
    /// so you need to call it like:
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(12, "hello", vec![1, 2, 3], 24, 3.14, true);
    /// let subseq = tup.subseq_mut::<tuple_t!(&'static str, bool), _>();
    /// *get!(subseq; 0) = "world";
    /// *get!(subseq; 1) = false;
    /// assert_eq!(tup, tuple!(12, "world", vec![1, 2, 3], 24, 3.14, false));
    /// ```
    fn subseq_mut(&mut self) -> Seq::AsMutOutput<'_>;

    /// Swap elements with a subsequence.
    ///
    /// See [`subseq()`](Subseq::subseq()) to see which inputs are subsequence.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`swap_subseq()`](TupleLike::swap_subseq()) method as
    /// the wrapper for this [`swap_subseq()`](Subseq::swap_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, Some("hello"), 2, Some(()), 3.14, 3);
    /// let mut tup2 = tuple!(Some("world"), 9.8);
    /// tup.swap_subseq(&mut tup2);
    /// assert_eq!(tup, tuple!(1, Some("world"), 2, Some(()), 9.8, 3));
    /// assert_eq!(tup2, tuple!(Some("hello"), 3.14));
    /// ```
    fn swap_subseq(&mut self, subseq: &mut Seq);

    /// Replace elements with a subsequence.
    ///
    /// See [`subseq()`](Subseq::subseq()) to see which inputs are subsequence.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// It returns a subsequence consisting of the replaced elements.
    ///
    /// Hint: If you don't want to consume the input tuple,
    /// then what you are looking for might be [`swap_subseq()`](Subseq::swap_subseq()).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`replace_subseq()`](TupleLike::replace_subseq()) method as
    /// the wrapper for this [`replace_subseq()`](Subseq::replace_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, Some("hello"), 2, Some(()), 3.14, 3);
    /// let replaced = tup.replace_subseq(tuple!(Some("world"), 9.8));
    /// assert_eq!(tup, tuple!(1, Some("world"), 2, Some(()), 9.8, 3));
    /// assert_eq!(replaced, tuple!(Some("hello"), 3.14));
    /// ```
    fn replace_subseq(&mut self, mut subseq: Seq) -> Seq {
        Subseq::swap_subseq(self, &mut subseq);
        subseq
    }
}

impl Subseq<Unit, Complete> for Unit {
    fn subseq(self) -> Unit {
        Unit
    }
    fn subseq_ref(&self) -> <Unit as TupleLike>::AsRefOutput<'_> {
        Unit
    }
    fn subseq_mut(&mut self) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }
    fn swap_subseq(&mut self, _: &mut Unit) {}
}

impl<First, Other1, Other2, I> Subseq<Tuple<First, Other2>, Used<I>> for Tuple<First, Other1>
where
    Other1: TupleLike + Subseq<Other2, I>,
    Other2: TupleLike,
{
    fn subseq(self) -> Tuple<First, Other2> {
        Tuple(self.0, Subseq::subseq(self.1))
    }

    fn subseq_ref(&self) -> <Tuple<First, Other2> as TupleLike>::AsRefOutput<'_> {
        Tuple(&self.0, Subseq::subseq_ref(&self.1))
    }

    fn subseq_mut(&mut self) -> <Tuple<First, Other2> as TupleLike>::AsMutOutput<'_> {
        Tuple(&mut self.0, Subseq::subseq_mut(&mut self.1))
    }

    fn swap_subseq(&mut self, subseq: &mut Tuple<First, Other2>) {
        std::mem::swap(&mut self.0, &mut subseq.0);
        Subseq::swap_subseq(&mut self.1, &mut subseq.1);
    }
}

impl<First, Other, T, I> Subseq<T, Unused<I>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: TupleLike + Subseq<T, I>,
{
    fn subseq(self) -> T {
        Subseq::subseq(self.1)
    }

    fn subseq_ref(&self) -> <T as TupleLike>::AsRefOutput<'_> {
        Subseq::subseq_ref(&self.1)
    }

    fn subseq_mut(&mut self) -> <T as TupleLike>::AsMutOutput<'_> {
        Subseq::subseq_mut(&mut self.1)
    }

    fn swap_subseq(&mut self, subseq: &mut T) {
        Subseq::swap_subseq(&mut self.1, subseq);
    }
}

/// Search for contiguous subsequences of tuples.
///
/// Unlike [`Subseq`], this trait requires that all elements of the subsequence are
/// contiguous in the supersequence.
///
/// The contiguous subsequence must have one and only one candidate in the supersequence.
pub trait ConSubseq<Seq, I>: TupleLike
where
    Seq: TupleLike,
{
    /// Take out a contiguous subsequence.
    ///
    /// Unlike [`subseq()`](Subseq::subseq()), this method requires that all elements of the subsequence are
    /// contiguous in the supersequence. Sometimes it can do things that [`subseq()`](Subseq::subseq()) can't.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Add a type annotation to the contiguous subsequence to let [`con_subseq()`](ConSubseq::con_subseq()) know.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`con_subseq()`](TupleLike::con_subseq()) method as the wrapper
    /// for this [`con_subseq()`](ConSubseq::con_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(12, "hello", 24, true, false);
    ///
    /// // For `subseq`, 4 candidates available:
    /// //      `(12, true)`,
    /// //      `(12, false)`,
    /// //      `(24, true)`,
    /// //      `(24, false)`,
    /// // so this cannot be compiled.
    /// // let subseq: tuple_t!(i32, bool) = tup.subseq();
    ///
    /// // But for `con_subseq`，only `(24, true)` is a candidate.
    /// let subseq: tuple_t!(i32, bool) = tup.con_subseq();
    /// assert_eq!(subseq, tuple!(24, true));
    /// ```
    fn con_subseq(self) -> Seq;

    /// Similar to [`con_subseq()`](ConSubseq::con_subseq()),
    /// but all its elements are immutable references to the supersequence's elements.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation,
    /// so you need to call it like:
    ///
    /// Hint: The [`TupleLike`] trait provides the [`con_subseq_ref()`](TupleLike::con_subseq_ref()) method
    /// as the wrapper for this [`con_subseq_ref()`](ConSubseq::con_subseq_ref()) method.
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(12, "hello", vec![1, 2, 3], 24, 3.14, true);
    /// let subseq = tup.con_subseq_ref::<tuple_t!(i32, f32), _>();
    /// assert_eq!(subseq, tuple!(&24, &3.14));
    /// ```
    fn con_subseq_ref(&self) -> Seq::AsRefOutput<'_>;

    /// Similar to [`con_subseq()`](ConSubseq::con_subseq()),
    /// but all its elements are mutable references to the supersequence's elements.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation,
    /// so you need to call it like:
    ///
    /// Hint: The [`TupleLike`] trait provides the [`con_subseq_mut()`](TupleLike::con_subseq_mut()) method
    /// as the wrapper for this [`con_subseq_mut()`](ConSubseq::con_subseq_mut()) method.
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(12, "hello", vec![1, 2, 3], "world", 24, 36);
    /// let subseq = tup.con_subseq_mut::<tuple_t!(&'static str, i32), _>();
    /// *get!(subseq; 0) = "rust";
    /// *get!(subseq; 1) = 0;
    /// assert_eq!(tup, tuple!(12, "hello", vec![1, 2, 3], "rust", 0, 36));
    /// ```
    fn con_subseq_mut(&mut self) -> Seq::AsMutOutput<'_>;

    /// Swap elements with a contiguous subsequence.
    ///
    /// Unlike [`swap_subseq()`](Subseq::swap_subseq()), this method requires that all
    /// elements of the subsequence are contiguous in the supersequence.
    /// Sometimes it can do things that [`swap_subseq()`](Subseq::swap_subseq()) can't.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`swap_con_subseq()`](TupleLike::swap_con_subseq()) method
    /// as the wrapper for this [`swap_con_subseq()`](ConSubseq::swap_con_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, Some("hello"), 2, Some(()), 3.14, 3);
    /// let mut tup2 = tuple!(4, None::<()>);
    /// tup.swap_con_subseq(&mut tup2);
    /// assert_eq!(tup, tuple!(1, Some("hello"), 4, None::<()>, 3.14, 3));
    /// assert_eq!(tup2, tuple!(2, Some(())));
    /// ```
    fn swap_con_subseq(&mut self, subseq: &mut Seq);

    /// Replace elements with a contiguous subsequence.
    ///
    /// Unlike [`replace_subseq()`](Subseq::replace_subseq()), this method requires that
    /// all elements of the subsequence are contiguous in the supersequence.
    /// Sometimes it can do things that [`replace_subseq()`](Subseq::replace_subseq()) can't.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// It returns a contiguous subsequence consisting of the replaced elements.
    ///
    /// Hint: If you don't want to consume the input tuple,
    /// then what you are looking for might be [`swap_con_subseq()`](TupleLike::swap_con_subseq()).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`replace_con_subseq()`](TupleLike::replace_con_subseq()) method
    /// as the wrapper for this [`replace_con_subseq()`](ConSubseq::replace_con_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, Some("hello"), 2, Some(()), 3.14, 3);
    /// let replaced = tup.replace_con_subseq(tuple!(4, None::<()>));
    /// assert_eq!(tup, tuple!(1, Some("hello"), 4, None::<()>, 3.14, 3));
    /// assert_eq!(replaced, tuple!(2, Some(())));
    /// ```
    fn replace_con_subseq(&mut self, mut subseq: Seq) -> Seq {
        ConSubseq::swap_con_subseq(self, &mut subseq);
        subseq
    }
}

impl<First, Other> ConSubseq<Unit, Complete> for Tuple<First, Other>
where
    Other: TupleLike,
{
    fn con_subseq(self) -> Unit {
        Unit
    }

    fn con_subseq_ref(&self) -> <Unit as TupleLike>::AsRefOutput<'_> {
        Unit
    }

    fn con_subseq_mut(&mut self) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }

    fn swap_con_subseq(&mut self, _: &mut Unit) {}
}

impl<First, Other1, Other2> ConSubseq<Tuple<First, Other2>, Complete> for Tuple<First, Other1>
where
    Other1: ConSubseq<Other2, Complete>,
    Other2: TupleLike,
{
    fn con_subseq(self) -> Tuple<First, Other2> {
        Tuple(self.0, ConSubseq::con_subseq(self.1))
    }

    fn con_subseq_ref(&self) -> <Tuple<First, Other2> as TupleLike>::AsRefOutput<'_> {
        Tuple(&self.0, ConSubseq::con_subseq_ref(&self.1))
    }

    fn con_subseq_mut(&mut self) -> <Tuple<First, Other2> as TupleLike>::AsMutOutput<'_> {
        Tuple(&mut self.0, ConSubseq::con_subseq_mut(&mut self.1))
    }

    fn swap_con_subseq(&mut self, subseq: &mut Tuple<First, Other2>) {
        std::mem::swap(&mut self.0, &mut subseq.0);
        ConSubseq::swap_con_subseq(&mut self.1, &mut subseq.1);
    }
}

impl<First, Other, T, I> ConSubseq<T, Unused<I>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: ConSubseq<T, I>,
{
    fn con_subseq(self) -> T {
        ConSubseq::con_subseq(self.1)
    }

    fn con_subseq_ref(&self) -> <T as TupleLike>::AsRefOutput<'_> {
        ConSubseq::con_subseq_ref(&self.1)
    }

    fn con_subseq_mut(&mut self) -> <T as TupleLike>::AsMutOutput<'_> {
        ConSubseq::con_subseq_mut(&mut self.1)
    }

    fn swap_con_subseq(&mut self, subseq: &mut T) {
        ConSubseq::swap_con_subseq(&mut self.1, subseq)
    }
}
