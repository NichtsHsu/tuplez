//! Provides the ability to unwrap elements of tuples.
//!
//! This module is only available when the `unwrap` feature is enabled (enabled by default).
//!
//! Since this module introduces the [`unwrap()`](Unwrap::unwrap()) method that may cause panic,
//! you may choose to disable it to avoid. Even if you accept it, it is more recommended that you use [`unwrap_or_default()`](UnwrapOrDefault::unwrap_or_default()) or
//! [`try_unwrap()`](Tuple::try_unwrap()) to avoid panic.

use crate::{Tuple, TupleLike, Unit};

/// Indicate that a type is a wrapper of a value and can be unwrapped into it.
///
/// Only available if the `unwrap` feature is enabled (enabled by default).
///
/// [`Unwrap`] is implemented by default for four types:
/// * [`Option<T>`](std::option::Option)
/// * [`Result<T, E>`](std::result::Result)
/// * [`Unit`]
/// * [`Tuple<T0, T1, ... Tn>`](crate::Tuple) if all types `T0`, `T1`, ... `Tn` implement [`Unwrap`].
///
/// Implement [`Unwrap`] for your own wrapper types so that a [`Tuple`] containing your wrappers can be [`unwrap()`](Unwrap::unwrap()).
pub trait Unwrap {
    /// Type of the contained value.
    type Output;

    /// Get the contained value.
    ///
    /// Because this function may panic, its use is generally discouraged. Instead,
    /// use [`unwrap_or_default()`](UnwrapOrDefault::unwrap_or_default()) or
    /// [`try_unwrap()`](Tuple::try_unwrap()).
    ///
    /// # Panic
    ///
    /// Panic if self does not contain a value.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, unwrap::Unwrap};
    ///
    /// let tup = tuple!(Some(1), Ok::<f32, ()>(3.14), Some("hello"));
    /// assert_eq!(tup.unwrap(), tuple!(1, 3.14, "hello"));
    /// ```
    fn unwrap(self) -> Self::Output;

    /// Check if self contains a value.
    ///
    /// Soundess requirement: When [`has_value()`](Unwrap::has_value()) returns true, [`unwrap()`](Unwrap::unwrap()) cannot panic.
    fn has_value(&self) -> bool;
}

/// Indicate that a type is a wrapper of a value and can be unwrapped into it or the default value.
///
/// Only available if the `unwrap` feature is enabled (enabled by default).
///
/// Unlike [`Unwrap`], the trait [`UnwrapOrDefault`] indicates that when the wrapper does not contain a value,
/// it's able to create a default value instead of panic.
///
/// [`UnwrapOrDefault`] is implemented by default for four types:
/// * [`Option<T>`](std::option::Option)
/// * [`Result<T, E>`](std::result::Result)
/// * [`Unit`]
/// * [`Tuple<T0, T1, ... Tn>`](crate::Tuple) if all types `T0`, `T1`, ... `Tn` implement [`UnwrapOrDefault`].
///
/// Implement [`UnwrapOrDefault`] for your own wrapper types so that a [`Tuple`] containing your wrappers can
/// be [`unwrap_or_default()`](UnwrapOrDefault::unwrap_or_default()).
pub trait UnwrapOrDefault {
    /// Type of the contained value.
    type Output;

    /// Get the contained value, or the default value if self does not contain a value.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, unwrap::UnwrapOrDefault};
    ///
    /// let tup = tuple!(Some(1), Err::<f32, &str>("failed"), Some("hello"));
    /// assert_eq!(tup.unwrap_or_default(), tuple!(1, 0.0, "hello"));
    /// ```
    fn unwrap_or_default(self) -> Self::Output;
}

impl<T> Unwrap for Option<T> {
    type Output = T;
    fn unwrap(self) -> Self::Output {
        self.unwrap()
    }
    fn has_value(&self) -> bool {
        self.is_some()
    }
}

impl<T, E: std::fmt::Debug> Unwrap for Result<T, E> {
    type Output = T;
    fn unwrap(self) -> Self::Output {
        self.unwrap()
    }
    fn has_value(&self) -> bool {
        self.is_ok()
    }
}

impl<T: Default> UnwrapOrDefault for Option<T> {
    type Output = T;
    fn unwrap_or_default(self) -> Self::Output {
        self.unwrap_or_default()
    }
}

impl<T: Default, E> UnwrapOrDefault for Result<T, E> {
    type Output = T;
    fn unwrap_or_default(self) -> Self::Output {
        self.unwrap_or_default()
    }
}

impl Unwrap for Unit {
    type Output = Unit;
    fn unwrap(self) -> Self::Output {
        Self
    }
    fn has_value(&self) -> bool {
        true
    }
}

impl<First, Other> Unwrap for Tuple<First, Other>
where
    Other: TupleLike + Unwrap,
    First: Unwrap,
{
    type Output = Tuple<<First as Unwrap>::Output, <Other as Unwrap>::Output>;
    fn unwrap(self) -> Self::Output {
        Tuple(self.0.unwrap(), self.1.unwrap())
    }
    fn has_value(&self) -> bool {
        self.0.has_value() && self.1.has_value()
    }
}

impl UnwrapOrDefault for Unit {
    type Output = Unit;
    fn unwrap_or_default(self) -> Self::Output {
        Self
    }
}

impl<First, Other> Tuple<First, Other>
where
    Other: TupleLike + Unwrap,
    First: Unwrap,
{
    /// Convert `Tuple<Wrapper0<T0>, Wrapper1<T1>, ... Wrappern<Tn>>` to `Option<Tuple<T0, T1, ..., Tn>>`,
    /// when all element types `Wrapper0`, `Wrapper1` ... `Wrappern` implmenet [`Unwrap`].
    ///
    /// Only available if the `unwrap` feature is enabled (enabled by default).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::tuple;
    ///
    /// let tup = tuple!(Some(1), Ok::<f32, ()>(3.14));
    /// assert_eq!(tup.try_unwrap(), Some(tuple!(1, 3.14)));
    /// let tup2 = tuple!(Some("hello"), Err::<i32, &str>("failed"));
    /// assert_eq!(tup2.try_unwrap(), None);
    /// ```
    pub fn try_unwrap(self) -> Option<<Self as Unwrap>::Output> {
        if self.has_value() {
            Some(self.unwrap())
        } else {
            None
        }
    }
}

impl<First, Other> UnwrapOrDefault for Tuple<First, Other>
where
    Other: TupleLike + UnwrapOrDefault,
    First: UnwrapOrDefault,
{
    type Output = Tuple<<First as UnwrapOrDefault>::Output, <Other as UnwrapOrDefault>::Output>;
    fn unwrap_or_default(self) -> Self::Output {
        Tuple(self.0.unwrap_or_default(), self.1.unwrap_or_default())
    }
}
