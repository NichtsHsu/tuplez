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
    /// Add a type annotation to the searched element to let [`take()`](Search::take()) know which one you want.
    ///
    /// If you want to take out the element at a specific index, see [`take!`](crate::take!).
    ///
    /// If you want to take out the first or last element, see [`Popable`][crate::Popable].
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::*;
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
    /// use tuplez::*;
    ///
    /// let tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let (value, remainder) = take!(tup; i32);
    /// assert_eq!(value, 5);
    /// assert_eq!(remainder, tuple!(3.14, "hello", [1, 2, 3]));
    /// ```
    fn take(self) -> (T, Self::TakeRemainder);

    /// Get an immutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`ref_of()`](Search::ref_of()) know which one you want.
    ///
    /// If you want to get the element by its index, see [`get!`](crate::get!);
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::*;
    ///
    /// let tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let arr: &[i32; 3] = tup.ref_of();
    /// assert_eq!(arr, &[1, 2, 3]);
    /// ```
    fn ref_of(&self) -> &T;

    /// Get a mutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`mut_of()`](Search::mut_of()) know which one you want.
    ///
    /// If you want to get the element by its index, see [`get!`](crate::get!);
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::*;
    ///
    /// let mut tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let s: &mut &str = tup.mut_of();
    /// *s = "world";
    /// assert_eq!(tup, tuple!(3.14, "world", 5, [1, 2, 3]));
    /// ```
    fn mut_of(&mut self) -> &mut T;
}

impl<First, Other> Search<First, Searched> for Tuple<First, Other>
where
    Other: TupleLike,
{
    type TakeRemainder = Other;

    fn take(self) -> (First, Self::TakeRemainder) {
        (self.0, self.1)
    }

    fn ref_of(&self) -> &First {
        &self.0
    }

    fn mut_of(&mut self) -> &mut First {
        &mut self.0
    }
}

impl<First, Other, T, Result> Search<T, Searching<Result>> for Tuple<First, Other>
where
    Other: TupleLike + Search<T, Result>,
{
    type TakeRemainder = Tuple<First, Other::TakeRemainder>;

    fn take(self) -> (T, Self::TakeRemainder) {
        let (value, remainder) = self.1.take();
        (value, Tuple(self.0, remainder))
    }

    fn ref_of(&self) -> &T {
        self.1.ref_of()
    }

    fn mut_of(&mut self) -> &mut T {
        self.1.mut_of()
    }
}
