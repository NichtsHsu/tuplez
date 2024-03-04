//! Provides the ability to search tuple elements by type.
//!
//! Check the documentation page of [`Search`] for details.

use crate::{Tuple, TupleLenEqTo, TupleLike, Unit};

/// Helper class for [`Search`], indicates that the current element is the one searched for.
pub struct Searched;

/// Helper class for [`Search`], indicates that the current element is not the one searched for.
pub struct Searching<Result>(Result);

/// Search for an element of a specific type in a tuple.
///
/// There is currently a restriction: only one element in the tuple can be of the type being searched.
pub trait Search<T, Result>: TupleLike {
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

impl<First, Other> Search<First, Searched> for Tuple<First, Other>
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

impl<First, Other, T, Result> Search<T, Searching<Result>> for Tuple<First, Other>
where
    Other: Search<T, Result>,
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
pub trait TailReplaceable<T: TupleLike, Result>: TupleLike {
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

impl<T, U> TailReplaceable<T, Searched> for U
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

impl<First, Other, T, Result> TailReplaceable<T, Searching<Result>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: TailReplaceable<T, Result>,
{
    type ReplaceOutput = Tuple<First, Other::ReplaceOutput>;
    type Replaced = Other::Replaced;

    fn replace_tail(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced) {
        let (output, replaced) = TailReplaceable::replace_tail(self.1, rhs);
        (Tuple(self.0, output), replaced)
    }
}

/// Replace a sequence of elements in the tuple with all elements of another tuple.
pub trait ReplaceWith<T: TupleLike, Result>: TupleLike {
    /// Replace a sequence of elements in the tuple with all elements of another tuple.
    ///
    /// The tuple will search for a sequence of elements whose types are exactly the same as
    /// the sequence of all the elements of the provided tuple, and then replace the elements
    /// of this sequence with the elements of the provided tuple.
    ///
    /// This means that this method does not change the type of the tuple, which is why this
    /// method requires `&mut self` instead of `self`.
    ///
    /// Finally, it returns the sequence of the replaced elements.
    ///
    /// NOTE: If you don't want to consume the input tuple,
    /// then what you are looking for might be [`swap_with()`](ReplaceWith::swap_with()).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`replace_with()`](TupleLike::replace_with()) method as the wrapper
    /// for this [`replace_with()`](ReplaceWith::replace_with()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, Some("hello"), 2, 3.14, 3);
    /// let replaced = tup.replace_with(tuple!(4, 9.8));
    /// assert_eq!(tup, tuple!(1, Some("hello"), 4, 9.8, 3));
    /// assert_eq!(replaced, tuple!(2, 3.14));
    /// ```
    fn replace_with(&mut self, rhs: T) -> T;

    /// Swap a sequence of elements in the tuple with all elements of another tuple.
    ///
    /// The tuple will search for a sequence of elements whose types are exactly the same as
    /// the sequence of all the elements of the provided tuple, and then swaps the elements
    /// of this sequence with the elements of the provided tuple.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`swap_with()`](TupleLike::swap_with()) method as the wrapper
    /// for this [`swap_with()`](ReplaceWith::swap_with()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, Some("hello"), 2, 3.14, 3);
    /// let mut tup2 = tuple!(4, 9.8);
    /// tup.swap_with(&mut tup2);
    /// assert_eq!(tup, tuple!(1, Some("hello"), 4, 9.8, 3));
    /// assert_eq!(tup2, tuple!(2, 3.14));
    /// ```
    fn swap_with(&mut self, rhs: &mut T);
}

impl<First, Other> ReplaceWith<Unit, Searched> for Tuple<First, Other>
where
    Other: TupleLike,
{
    fn replace_with(&mut self, rhs: Unit) -> Unit {
        rhs
    }

    fn swap_with(&mut self, _: &mut Unit) {}
}

impl<First, Other1, Other2> ReplaceWith<Tuple<First, Other2>, Searched> for Tuple<First, Other1>
where
    Other1: ReplaceWith<Other2, Searched>,
    Other2: TupleLike,
{
    fn replace_with(&mut self, mut rhs: Tuple<First, Other2>) -> Tuple<First, Other2> {
        ReplaceWith::swap_with(self, &mut rhs);
        rhs
    }

    fn swap_with(&mut self, rhs: &mut Tuple<First, Other2>) {
        std::mem::swap(&mut self.0, &mut rhs.0);
        ReplaceWith::swap_with(&mut self.1, &mut rhs.1);
    }
}

impl<First, Other, T, Result> ReplaceWith<T, Searching<Result>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: ReplaceWith<T, Result>,
{
    fn replace_with(&mut self, mut rhs: T) -> T {
        ReplaceWith::swap_with(&mut self.1, &mut rhs);
        rhs
    }

    fn swap_with(&mut self, rhs: &mut T) {
        ReplaceWith::swap_with(&mut self.1, rhs)
    }
}
