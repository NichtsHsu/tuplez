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
    type UnwrapOutput;

    /// Get the contained value.
    ///
    /// Because this function may panic, its use is generally discouraged. Instead,
    /// use [`unwrap_or_default()`](UnwrapOrDefault::unwrap_or_default()) or
    /// [`try_unwrap()`](Tuple::try_unwrap()).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`unwrap()`](TupleLike::unwrap()) method as the wrapper
    /// for this [`unwrap()`](Unwrap::unwrap()) method.
    ///
    /// # Panic
    ///
    /// Panic if self does not contain a value.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(Some(1), Ok::<f32, ()>(3.14), Some("hello"));
    /// assert_eq!(tup.unwrap(), tuple!(1, 3.14, "hello"));
    /// ```
    fn unwrap(self) -> Self::UnwrapOutput;

    /// Check if self contains a value.
    ///
    /// Soundess requirement: When [`has_value()`](Unwrap::has_value()) returns true, [`unwrap()`](Unwrap::unwrap()) cannot panic.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`has_value()`](TupleLike::has_value()) method as the wrapper
    /// for this [`has_value()`](Unwrap::has_value()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// assert_eq!(tuple!(Some(1), Some(3.14), Ok::<&str, ()>("hello")).has_value(), true);
    /// assert_eq!(tuple!(None::<i32>, Some(3.14), Err::<&str, ()>(())).has_value(), false);
    /// ```
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
    type UnwrapOutput;

    /// Get the contained value, or the default value if self does not contain a value.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`unwrap_or_default()`](TupleLike::unwrap_or_default())
    /// method as the wrapper for this [`unwrap_or_default()`](UnwrapOrDefault::unwrap_or_default()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(Some(1), Err::<f32, &str>("failed"), Some("hello"));
    /// assert_eq!(tup.unwrap_or_default(), tuple!(1, 0.0, "hello"));
    /// ```
    fn unwrap_or_default(self) -> Self::UnwrapOutput;
}

impl<T> Unwrap for Option<T> {
    type UnwrapOutput = T;
    fn unwrap(self) -> Self::UnwrapOutput {
        self.unwrap()
    }
    fn has_value(&self) -> bool {
        self.is_some()
    }
}

impl<T, E: std::fmt::Debug> Unwrap for Result<T, E> {
    type UnwrapOutput = T;
    fn unwrap(self) -> Self::UnwrapOutput {
        self.unwrap()
    }
    fn has_value(&self) -> bool {
        self.is_ok()
    }
}

impl<T: Default> UnwrapOrDefault for Option<T> {
    type UnwrapOutput = T;
    fn unwrap_or_default(self) -> Self::UnwrapOutput {
        self.unwrap_or_default()
    }
}

impl<T: Default, E> UnwrapOrDefault for Result<T, E> {
    type UnwrapOutput = T;
    fn unwrap_or_default(self) -> Self::UnwrapOutput {
        self.unwrap_or_default()
    }
}

impl Unwrap for Unit {
    type UnwrapOutput = Unit;
    fn unwrap(self) -> Self::UnwrapOutput {
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
    type UnwrapOutput = Tuple<First::UnwrapOutput, Other::UnwrapOutput>;
    fn unwrap(self) -> Self::UnwrapOutput {
        Tuple(Unwrap::unwrap(self.0), Unwrap::unwrap(self.1))
    }
    fn has_value(&self) -> bool {
        Unwrap::has_value(&self.0) && Unwrap::has_value(&self.1)
    }
}

impl UnwrapOrDefault for Unit {
    type UnwrapOutput = Unit;
    fn unwrap_or_default(self) -> Self::UnwrapOutput {
        Self
    }
}

impl Unit {
    /// Always be `Some(tuple!())`.
    pub fn try_unwrap(self) -> Option<Self> {
        Some(self)
    }
}

impl<First, Other> UnwrapOrDefault for Tuple<First, Other>
where
    Other: TupleLike + UnwrapOrDefault,
    First: UnwrapOrDefault,
{
    type UnwrapOutput = Tuple<First::UnwrapOutput, Other::UnwrapOutput>;
    fn unwrap_or_default(self) -> Self::UnwrapOutput {
        Tuple(
            UnwrapOrDefault::unwrap_or_default(self.0),
            UnwrapOrDefault::unwrap_or_default(self.1),
        )
    }
}
