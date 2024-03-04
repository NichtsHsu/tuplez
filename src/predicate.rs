//! Provides the ability to test tuples.

use crate::{foreach::Mapper, Tuple, TupleLike, Unit};

/// Define a unary predicate that accepts immutable reference of a value and produces a `bool` result.
///
/// Call [`any()`](TupleLike::any()) and [`all()`](TupleLike::all()) on a tuple requires a unary predicate
/// that implements [`UnaryPredicate`].
///
/// Note that the predicate always receives an immutable reference to the element of the tuple.
///
/// # Quickly build a unary predicate by macros
///
/// Here are two ways you can quickly build a folder.
///
/// ## Test tuples by element types
///
/// The [`unary_pred!`](crate::unary_pred!) macro helps you build a unary predicate that test tuples according to their element types.
///
/// For example:
///
/// ```
/// use tuplez::{tuple, TupleLike, unary_pred};
///
/// let tup = tuple!(1, "2", |x: i32| x >= 0);
/// let result = tup.all(
///     unary_pred! {
///         |x: i32| { *x >= 0 }
///         |x: &str| { !x.is_empty() }
///         <T: Fn(i32) -> bool> |f: T| { f(1) }
///     }
/// );
/// assert_eq!(result, true);
/// ```
///
/// ## Test tuples in order of their elements
///
/// You can create a new tuple with the same number of elements, whose elements are all callable objects that accepts
/// an immutable reference to an element and returns a `bool` value ([`FnOnce(&T) -> bool`](std::ops::FnOnce)),
/// then, you can use that tuple as a unary predicate.
///
/// For example:
///
/// ```
/// use tuplez::{tuple, TupleLike};
///
/// let tup = tuple!(1, 2, "3");
/// let result = tup.any(
///     tuple!(
///         |x: &i32| *x < 0,
///         |x: &i32| *x > 100,
///         |x: &&str| *x == "1",
///     )
/// );
/// assert_eq!(result, false);
/// ```
///
/// # Custom unary predicate
///
/// NOTE: In general, a unary predicate is equivalent to a mapper that accepts immutable references
/// to elements and returns a `bool` value. Therefore, instead of [`UnaryPredicate<T>`],
/// you should implement [`Mapper<&T, Output=bool>`](Mapper) for your custom type, and use it as a unary predicate.
/// In fact, this is what the [`unary_pred!`](crate::unary_pred!) macro does.
///
/// Here is an example:
///
/// ```
/// use std::ops::Range;
/// use tuplez::{foreach::Mapper, tuple, TupleLike};
///
/// #[derive(Clone)]
/// struct Basis(Range<i32>);
///
/// impl Mapper<&i32> for Basis {
///     type Output = bool;
///     type NextMapper = Self;
///     fn map(self, value: &i32) -> (Self::Output, Self::NextMapper) {
///         (self.0.contains(value), self)
///     }
/// }
///
/// impl Mapper<&&str> for Basis {
///     type Output = bool;
///     type NextMapper = Self;
///     fn map(self, value: &&str) -> (Self::Output, Self::NextMapper) {
///         (
///             value.parse::<i32>().is_ok_and(|s| self.0.contains(&s)),
///             self,
///         )
///     }
/// }
///
/// let basis = Basis(0..5); // Let us assume that `basis` is known only at runtime
///
/// let tup = tuple!(1, 2, "3");
/// let result = tup.all(basis.clone());
/// assert_eq!(result, true);
///
/// let tup = tuple!(-1, 8, "10");
/// let result = tup.any(basis.clone());
/// assert_eq!(result, false);
/// ```
pub trait UnaryPredicate<'a, T: 'a> {
    /// Type of next unary predicate to be use.
    type NextUnaryPredicate;

    /// Test a value with its immutable reference
    fn test(self, testee: &'a T) -> (bool, Self::NextUnaryPredicate);
}

impl<'a, T, F> UnaryPredicate<'a, T> for F
where
    T: 'a,
    F: Mapper<&'a T, Output = bool>,
{
    type NextUnaryPredicate = <F as Mapper<&'a T>>::NextMapper;
    fn test(self, testee: &'a T) -> (bool, Self::NextUnaryPredicate) {
        self.map(testee)
    }
}

/// Tests if any element of the tuple matches a predicate.
///
/// # The unary predicate `Pred`
///
/// For testing [`Tuple<T0, T1, ... Tn>`](crate::Tuple), you need to build a unary predicate,
/// which needs to implement [`UnaryPredicate<T0>`], and the [`NextUnaryPredicate`](UnaryPredicate::NextUnaryPredicate)
/// needs to implement [`UnaryPredicate<T1>`], and so on.
///
/// See the documentation page of [`UnaryPredicate`] for details.
pub trait TestAny<Pred>: TupleLike {
    /// Tests if any element of the tuple matches a predicate.
    ///
    /// Check out [`UnaryPredicate`]'s documentation page to learn how to build
    /// a unary predicate that can be passed to [`any()`](TestAny::any()).
    ///
    /// [`any()`](TestAny::any()) is short-circuiting; in other words, it will stop processing as soon as it finds a `true`,
    /// given that no matter what else happens, the result will also be `true`.
    ///
    /// An empty tuple returns `false`.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`any()`](TupleLike::any()) method as the wrapper
    /// for this [`any()`](TestAny::any()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, unary_pred};
    ///
    /// let predicate = unary_pred! {
    ///     |x: i32| { (0..10).contains(x) },
    ///     |x: &str| { x.parse::<i32>().is_ok() },
    /// };
    ///
    /// let tup = tuple!(100, 2, "world");
    /// let result = tup.any(predicate);
    /// assert_eq!(result, true);
    ///
    /// let tup = tuple!(-1, 96, "hello");
    /// let result = tup.any(predicate);
    /// assert_eq!(result, false);
    /// ```
    fn any(&self, predicate: Pred) -> bool;
}

impl<Pred> TestAny<Pred> for Unit {
    fn any(&self, _: Pred) -> bool {
        false
    }
}

impl<Pred, First, Other> TestAny<Pred> for Tuple<First, Other>
where
    for<'a> Pred: UnaryPredicate<'a, First>,
    for<'a> Other: TestAny<<Pred as UnaryPredicate<'a, First>>::NextUnaryPredicate>,
{
    fn any(&self, predicate: Pred) -> bool {
        let (res, next) = predicate.test(&self.0);
        res || TestAny::any(&self.1, next)
    }
}

/// Tests if every element of the tuple matches a predicate.
///
/// # The unary predicate `Pred`
///
/// For testing [`Tuple<T0, T1, ... Tn>`](crate::Tuple), you need to build a unary predicate,
/// which needs to implement [`UnaryPredicate<T0>`], and the [`NextUnaryPredicate`](UnaryPredicate::NextUnaryPredicate)
/// needs to implement [`UnaryPredicate<T1>`], and so on.
///
/// See the documentation page of [`UnaryPredicate`] for details.
pub trait TestAll<Pred>: TupleLike {
    /// Tests if every element of the tuple matches a predicate.
    ///
    /// Check out [`UnaryPredicate`]'s documentation page to learn how to build
    /// a unary predicate that can be passed to [`all()`](TestAll::all()).
    ///
    /// [`all()`](TestAll::all()) is short-circuiting; in other words, it will stop processing as soon as it finds a `false`,
    /// given that no matter what else happens, the result will also be `false`.
    ///
    /// An empty tuple returns `true`.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`all()`](TupleLike::all()) method as the wrapper
    /// for this [`all()`](TestAll::all()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, unary_pred};
    ///
    /// let predicate = unary_pred! {
    ///     |x: i32| { (0..10).contains(x) },
    ///     |x: &str| { x.parse::<i32>().is_ok() },
    /// };
    ///
    /// let tup = tuple!(1, 2, "3");
    /// let result = tup.all(predicate);
    /// assert_eq!(result, true);
    ///
    /// let tup = tuple!(7, 8, "hello");
    /// let result = tup.all(predicate);
    /// assert_eq!(result, false);
    /// ```
    fn all(&self, predicate: Pred) -> bool;
}

impl<Pred> TestAll<Pred> for Unit {
    fn all(&self, _: Pred) -> bool {
        true
    }
}

impl<Pred, First, Other> TestAll<Pred> for Tuple<First, Other>
where
    for<'a> Pred: UnaryPredicate<'a, First>,
    for<'a> Other: TestAll<<Pred as UnaryPredicate<'a, First>>::NextUnaryPredicate>,
{
    fn all(&self, predicate: Pred) -> bool {
        let (res, next) = predicate.test(&self.0);
        res && TestAll::all(&self.1, next)
    }
}
