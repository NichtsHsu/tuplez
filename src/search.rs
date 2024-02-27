//! Provides the ability to search tuple elements by type.
//!
//! Check the documentation page of [`Search`] for details.

use crate::{Tuple, TupleLike};

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
