#![cfg_attr(feature = "any_array", allow(incomplete_features))]
#![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
#![cfg_attr(feature = "any_array", feature(maybe_uninit_uninit_array))]
#![cfg_attr(feature = "any_array", feature(maybe_uninit_array_assume_init))]
#![cfg_attr(feature = "any_array", feature(maybe_uninit_uninit_array_transpose))]

//! Tuples represented in recursive form rather than parallel form.
//!
//! # Motivation
//!
//! The [primitive tuple types](https://doc.rust-lang.org/std/primitive.tuple.html) are represented in parallel form, like:
//!
//! ```text
//! (a, b, c, d ...)
//! ```
//!
//! Since Rust doesn't support variadic generics, we cannot add methods to primitive tuples with any number of elements.
//!
//! Currently, most tuple crates use declarative macros to implement methods for tuples whose number of elements is less than
//! a certain limit (usually 32).
//!
//! To solve this, tuplez introduces a [`Tuple`] type represented in recursive form, like:
//!
//! ```text
//! Tuple(a, Tuple(b, Tuple(c, Tuple(d, ...))))
//! ```
//!
//! The advantage of this representation is that [you can implement methods recursively for all tuples](Tuple#trait-implementations-on-tuple),
//! and there is no longer a limit on the number of tuple's elements. And, in almost all cases, the [`Tuple`] takes no more memory than
//! the primitive tuples.
//!
//! # Functionality
//!
//! * [Create tuples](tuple!) with any number of elements.
//! * [Access elements](get!) in a tuple at any index.
//! * [Push element](TupleLike::push()) to a tuple or [pop element](Popable::pop()) from a tuple.
//! * [Join](TupleLike::join()) two tuples or [split](split_at!) a tuple into two parts.
//! * [Reverse](TupleLike::rev()), [left rotate](Rotatable::rot_l()), or [right rotate](Rotatable::rot_r()) a tuple.
//! * If all element types implement a `Trait` (e.g. `Eq`, `Add`), then the [`Tuple`] also implement that `Trait`.
//! [See which traits are supported and learn how to implement your custom traits for `Tuple`](Tuple#trait-implementations-on-tuple).
//! * [Traverse all elements](Tuple#traverse-tuples) of a tuple.
//! * When the number of elements of a tuple doesn't exceed 32, then it can be converted from/to [a primitive tuple](Tuple#convert-fromto-primitive-tuples)
//! or [a primitive array](Tuple#convert-fromto-primitive-arrays).
//!
//! # Optional features
//!
//! * `any_array`: Use Rust's unstable feature to implement conversion from/to primitive arrays on tuples with any number of elements.
//! This feature requires compiling with rustc released to nightly channel.
//! * `unwrap` (by default): Allows converting a tuple whose elements are all wrappers into a tuple of the values those wrappers contain.
//! See [`Unwrap`] and [`UnwrapOrDefault`].
//!
//! # Examples
//!
//! ```
//! // Enable Rust's `generic_const_exprs` feature if you enable tuplez's `any_array` feature.
//! #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
//!
//! use tuplez::*;
//!
//! let tup = tuple!(1, "hello".to_string(), 3.14);
//! let tup2 = Tuple::from((2, " world", -3.14));
//! let tup3 = tup + tup2;
//! assert_eq!(tup3, tuple!(3, "hello world".to_string(), 0.0));
//!
//! let tup4 = tup3.push(Some([1, 2, 3]));
//! let (tup5, popped) = tup4.pop_front();
//! assert_eq!(
//!     tup5,
//!     tuple!("hello world".to_string(), 0.0, Some([1, 2, 3]))
//! );
//! assert_eq!(popped, 3);
//!
//! let tup6 = tup5.rev();
//! assert_eq!(
//!     tup6,
//!     tuple!(Some([1, 2, 3]), 0.0, "hello world".to_string())
//! );
//! let tup7 = tup6.rot_l();
//! assert_eq!(
//!     tup7,
//!     tuple!(0.0, "hello world".to_string(), Some([1, 2, 3]))
//! );
//!
//! let tup8 = tup7.foreach_once(mapper_once! {
//!     x : f64 => String : x.to_string();
//!     x : Option<[i32; 3]> => String: format!("{:?}", x.unwrap());
//!     x : String : x
//! });
//! let arr = tup8.to_array();
//! assert_eq!(
//!     arr,
//!     [
//!         "0".to_string(),
//!         "hello world".to_string(),
//!         "[1, 2, 3]".to_string()
//!     ]
//! );
//! ```
//!
//! Please check [`Tuple`]'s documentation page for detailed usage.

#[macro_use]
mod macros;
mod mapper;
mod tuple;

#[cfg(feature = "any_array")]
mod any_array;

#[cfg(feature = "unwrap")]
mod unwrap;

pub use mapper::*;
pub use tuple::*;

#[cfg(feature = "any_array")]
pub use any_array::*;

#[cfg(feature = "unwrap")]
pub use unwrap::*;

/// Generate a tuple from a list of expressions.
///
/// # Syntax
///
/// `tuple!( [ Expr1 [; Count], Expr2 [; Count], ... ] )`
///
/// *The `[` and `]` markers only indicate optional content but not that the `[` and `]` need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Examples
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(1, "hello", 3.14);
/// let tup2 = tuple!("world", 2;3, 9.8);   // Repeat `2` three times
/// assert_eq!(tup2, tuple!("world", 2, 2, 2, 9.8));
///
/// let unit = tuple!();
/// assert_eq!(unit, Unit);
/// ```
///
/// Remember that macros do not directly evaluate expressions, so:
///
/// ```
/// use tuplez::*;
///
/// let mut x = 0;
/// assert_eq!(tuple!({x += 1; x}; 3), tuple!(1, 2, 3));
/// ```
pub use tuplez_macros::tuple;

/// Generate the complete type signature for tuples.
///
/// # Syntax
///
/// `tuple_t!([T0 [; Count], T1 [; Count], ... ])`
///
/// *The `[` and `]` markers only indicate optional content but not that the `[` and `]` need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Examples
///
/// ```
/// use tuplez::*;
///
/// let tup = <tuple_t!(i32, f64, String)>::default();
/// assert_eq!(tup, tuple!(0, 0.0, String::new()));
///
/// let unit: tuple_t!() = From::from(());
/// assert_eq!(unit, tuple!());
///
/// let tup2: tuple_t!(i32, f64;3, i32) = tuple!(1, 2.0, 3.0, 4.0, 5);
///
/// fn use_tuple(tup: tuple_t!(i32, &dyn std::fmt::Debug, tuple_t!(String, String))) {
///     todo!()
/// }
/// ```
pub use tuplez_macros::tuple_t;

/// Generate patterns for tuples.
///
/// # Syntax
///
/// `tuple_pat!([#] [Pat0 [; Count], Pat1 [; Count], ... ])`
///
/// *The `[` and `]` markers only indicate optional content but not that the `[` and `]` need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Examples
///
/// When the number of patterns you provide is less than the number of elements of the tuple,
/// the following elements will not be matched. For example:
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(3.14, "hello", 1, [9.8]);
/// let tuple_pat!(a, b, c) = tup;
/// assert_eq!(a, 3.14);
/// assert_eq!(b, "hello");
/// assert_eq!(c, 1);
/// ```
///
/// If you want the last pattern to match all remaining elements, you can add a `#` mark:
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(3.14, "hello", 1, [9.8]);
/// let tuple_pat!(# a, b, c) = tup;
/// assert_eq!(a, 3.14);
/// assert_eq!(b, "hello");
/// assert_eq!(c, tuple!(1, [9.8]));
/// ```
///
/// But this has a bad side effect, even though the number of patterns is equal to the number of elements of the tuple,
/// the last pattern still matches a tuple containing only one element:
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(3.14, "hello", 1, [9.8]);
/// let tuple_pat!(# a, b, c, d) = tup;
/// assert_eq!(a, 3.14);
/// assert_eq!(b, "hello");
/// assert_eq!(c, 1);
/// assert_eq!(d, tuple!([9.8]));   // Not `[9.8]`
/// ```
///
/// In this case, just remove the `#` mark. Or, you can also add an extra `_` pattern to unpack the last tuple:
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(3.14, "hello", 1, [9.8]);
/// let tuple_pat!(# a, b, c, d, _) = tup;
/// assert_eq!(a, 3.14);
/// assert_eq!(b, "hello");
/// assert_eq!(c, 1);
/// assert_eq!(d, [9.8]);
/// ```
pub use tuplez_macros::tuple_pat;

/// Get the element at a specific index of the tuple.
///
/// # Syntax
///
/// `get!(Expr; Index)`
///
/// **The index must be an integer literal** since procedural macros do not yet support evaluating constants.
///
/// # Explanation
///
/// This macro will be expanded to standard member access syntax:
///
/// ```text
/// get!(tup; 0) => tup.0
/// get!(tup; 1) => tup.1.0
/// get!(tup; 2) => tup.1.1.0
/// ```
///
/// Expressions are automatically quoted, so don't worry:
///
/// ```text
/// get!(tup1 + tup2; 3) => (tup1 + tup2).1.1.1.0
/// ```
///
/// You can use `&` and `&mut` directly on the output of [`get!`], like:
///
/// ```
/// use tuplez::*;
///
/// fn add(x: &i32, y: &i32) -> i32 { x + y }
///
/// fn add_one(x: &mut i32) { *x += 1; }
///
/// let mut tup = tuple!(1, "hello", 3.14);
///
/// let x = add(&get!(tup; 0), &2);             // Immutably reference the first element of `tup`
/// assert_eq!(tup, tuple!(1, "hello", 3.14));  // Then `tup` remains unchanged
/// assert_eq!(x, 3);
///
/// add_one(&mut get!(tup; 0));                 // Mutably reference the first element of `tup`
/// assert_eq!(tup, tuple!(2, "hello", 3.14));  // Then `tup` changes
///
/// get!(tup; 1) = "world";                     // Direct access the second element of `tup`
/// assert_eq!(tup, tuple!(2, "world", 3.14));
/// ```
///
/// It's not a problem for nested tuples either:
///
/// ```
/// use tuplez::*;
///
/// fn push_world(s: &mut String) {
///     s.push_str(" world");
/// }
///
/// let mut tup = tuple!(1, tuple!("hello".to_string(), 3.14));
/// push_world(&mut get!(get!(tup; 1); 0));
/// assert_eq!(tup, tuple!(1, tuple!("hello world".to_string(), 3.14)));
/// ```
pub use tuplez_macros::get;

/// Split the tuple into two tuples at a specific index.
///
/// # Syntax
///
/// `split_at!(Expr; Index)`
///
/// **The index must be an integer literal** since procedural macros do not yet support evaluating constants.
///
/// # Examples
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3]);
///
/// let (left, right) = split_at!(tup; 2);
/// assert_eq!(left, tuple!(1, "hello"));
/// assert_eq!(right, tuple!(3.14, [1, 2, 3]));
///
/// let (left, right) = split_at!(tup; 0);
/// assert_eq!(left, tuple!());
/// assert_eq!(right, tup);
///
/// let (left, right) = split_at!(tup; 4);
/// assert_eq!(left, tup);
/// assert_eq!(right, tuple!());
/// ```
pub use tuplez_macros::split_at;
