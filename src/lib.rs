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
//! * [Access elements](get!) in a tuple at any index, or by their types.
//! * [Push element](TupleLike::push()) to a tuple or [pop element](Popable::pop()) from a tuple.
//! * [Join](TupleLike::join()) two tuples or [split](split_at!) a tuple into two parts.
//! * [Reverse](TupleLike::rev()), [left rotate](Rotatable::rot_l()), or [right rotate](Rotatable::rot_r()) a tuple.
//! * If all element types implement a `Trait` (e.g. `Eq`, `Add`), then the [`Tuple`] also implement that `Trait`.
//! [See which traits are supported and learn how to implement your custom traits for `Tuple`](Tuple#trait-implementations-on-tuple).
//! * [Traverse all elements](Tuple#traverse-tuples) of a tuple, or [fold](Tuple#fold-tuples) a tuple.
//! * When the number of elements of a tuple doesn't exceed 32, then it can be converted from/to [a primitive tuple](Tuple#convert-fromto-primitive-tuples)
//! or [a primitive array](Tuple#convert-fromto-primitive-arrays).
//!
//! # Optional features
//!
//! * `any_array`: Use Rust's unstable feature to implement conversion from/to primitive arrays on tuples with any number of elements.
//! This feature requires compiling with rustc released to nightly channel.
//! * `unwrap` (by default): Allows converting a tuple whose elements are all wrappers into a tuple of the values those wrappers contain.
//! See [`Unwrap`](crate::unwrap::Unwrap) and [`UnwrapOrDefault`](crate::unwrap::UnwrapOrDefault).
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
//! let tup8 = tup7.foreach(mapper! {
//!     |x: f64| -> String { x.to_string() }
//!     |x: Option<[i32; 3]>| -> String { format!("{:?}", x.unwrap()) }
//!     |x: String| { x }
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
//!
//! let tup9 = tuple!(1, "2", 3.0);
//! let result = tup9.fold(
//!     seq_folder!(
//!         |acc, x| (acc + x) as f64,
//!         |acc: f64, x: &str| acc.to_string() + x,
//!         |acc: String, x| acc.parse::<i32>().unwrap() + x as i32,
//!     ),
//!     0,
//! );
//! assert_eq!(result, 15);
//! ```
//!
//! Please check [`Tuple`]'s documentation page for detailed usage.

extern crate self as tuplez;

#[macro_use]
mod macros;
pub mod fold;
pub mod foreach;
pub mod search;
mod tuple;

#[cfg(feature = "any_array")]
mod any_array;

#[cfg(feature = "unwrap")]
pub mod unwrap;

pub use tuple::*;

pub use search::Search;

#[cfg(feature = "any_array")]
pub use any_array::*;

/// Generate a tuple from a list of expressions.
///
/// # Syntax
///
/// `tuple!( [ Expr1 [; Count], Expr2 [; Count], ... ] )`
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Examples
///
/// ```
/// use tuplez::{tuple, Unit};
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
/// use tuplez::tuple;
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
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Examples
///
/// ```
/// use tuplez::{tuple, tuple_t};
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
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Examples
///
/// When the number of patterns you provide is less than the number of elements of the tuple,
/// the following elements will not be matched. For example:
///
/// ```
/// use tuplez::{tuple, tuple_pat};
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
/// use tuplez::{tuple, tuple_pat};
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
/// use tuplez::{tuple, tuple_pat};
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
/// use tuplez::{tuple, tuple_pat};
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
/// The [`ref_of()`](crate::search::Search::ref_of()) and [`mut_of()`](crate::Search::mut_of())
/// provide another way to get elements by their type.
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
/// use tuplez::{get, tuple};
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
/// use tuplez::{get, tuple};
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

/// Take the element at a specific index of the tuple and get the remainder.
///
/// When the type of element is provided instead of its index, this macro expands to
/// [`take()`](crate::Search::take()).
///
/// The [`Popable`] also provide methods to pop elements from the front or back of the tuple.
///
/// # Syntax
///
/// 1. `take!(Expr; Index)`
///
///     **The index must be an integer literal** since procedural macros do not yet support evaluating constants.
///
/// 2. `take!(Expr; Type)`
///
///     There is currently a restriction: only one element in the tuple can be of the type being searched.
///
/// # Examples
///
/// Use indexes:
///
/// ```
/// use tuplez::{take, tuple};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3]);
/// let (element, remainder) = take!(tup; 2);
/// assert_eq!(element, 3.14);
/// assert_eq!(remainder, tuple!(1, "hello", [1, 2, 3]));
///
/// let tup = tuple!(1);
/// let (element, remainder) = take!(tup; 0);
/// assert_eq!(element, 1);
/// assert_eq!(remainder, tuple!());
/// ```
///
/// Use types:
///
/// ```
/// use tuplez::{take, tuple};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3]);
/// let (element, remainder) = take!(tup; &str);
/// assert_eq!(element, "hello");
/// assert_eq!(remainder, tuple!(1, 3.14, [1, 2, 3]));
///
/// let tup = tuple!(1);
/// let (element, remainder) = take!(tup; i32);
/// assert_eq!(element, 1);
/// assert_eq!(remainder, tuple!());
/// ```
pub use tuplez_macros::take;

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
/// use tuplez::{split_at, tuple};
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

/// Provides a simple way to build a functor that implements [`Mapper`](crate::foreach::Mapper).
///
/// # Syntax
///
/// ```text
/// Generic = [Lifetime1, Lifetime2, ...] [Type1 [: Bound1], Type2 [: Bound2], ...]
/// Rule    = [ < Generic > ] | Variable : InputType | [-> OutputType] { Body }
///
/// mapper!( [Rule1 Rule2 ... ] )
/// ```
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Explanation
///
/// A mapping rule is much like a closure, except that it must annotate the argument type and the return type:
///
/// ```text
/// |x: i32| -> i64 { x as i64 }
/// ```
///
/// Also supports adding `mut`:
///
/// ```text
/// |mut x: i32| -> i64 { x += 1; x as i64 }
/// ```
///
/// If the return value requires a lifetime, you need to explicitly introduce the lifetime annotation, since Rust binds the lifetime
/// of return value to the functor instead of the element by default:
///
/// ```text
/// <'a> |x: &'a str| -> &'a [u8] { x.as_bytes() }
/// ```
///
/// You can omit the return type when the return type is the same as the element type.
/// Note: Do not misunderstand that the return type is automatically deduced or is a `()`.
///
/// ```text
/// |x: i32| { x + 1 }
/// ```
///
/// You can also introduce generic types like this:
///
/// ```text
/// <T> |x: Option<T>| -> T { x.unwrap() }
/// ```
///
/// Many times, you may also need to add bounds to the generic type:
///
/// ```text
/// <T: ToString> |x: Option<T>| -> String { x.unwrap().to_string() }
/// ```
///
/// Construct mapping rules for all element types in the tuple,
/// and then combine them in the [`mapper!`](crate::mapper!) macro to traverse the tuple:
///
/// ```
/// use tuplez::{mapper, tuple, TupleLike};
///
/// let tup = tuple!(1, "hello", Some(3.14)).foreach(mapper! {
///     |mut x: i32| -> i64 { x += 1; x as i64 }
///     <T: ToString> |x: Option<T>| -> String { x.unwrap().to_string() }
///     <'a> |x: &'a str| -> &'a [u8] { x.as_bytes() }
/// });
/// assert_eq!(tup, tuple!(2i64, b"hello" as &[u8], "3.14".to_string()));
/// ```
///
/// Tip: If you don't want to consume the tuple, call its [`as_ref()`](crate::TupleLike::as_ref()) before traversing.
/// Likewise, if you want to modify elements of tuple, call its [`as_mut()`](crate::TupleLike::as_mut()) before traversing.
///
/// ```
/// use tuplez::{mapper, tuple, TupleLike};
///
/// let mut tup = tuple!(1, "hello", Some(3.14));
/// let tup2 = tup.as_ref().foreach(mapper!{
///     |x: &i32| -> i32 { *x + 1 }
///     <T: ToString> |x: &Option<T>| -> String { x.as_ref().unwrap().to_string() }
///     <'a> |x: &&'a str| -> &'a [u8] { x.as_bytes() }
/// });
/// assert_eq!(tup2, tuple!(2, b"hello" as &[u8], "3.14".to_string()));
/// assert_eq!(tup, tuple!(1, "hello", Some(3.14)));  // And the original tuple is not consumed
///
/// _ = tup.as_mut().foreach(mapper!{
///     |x: &mut i32| -> () { *x += 1; }
///     <T: ToString> |x: &mut Option<T>| -> () { x.take(); }
///     |x: &mut &str| -> () { *x = "world" }
/// });
/// assert_eq!(tup, tuple!(2, "world", None));
/// ```
pub use tuplez_macros::mapper;

/// Provides a simple way to build a folder that implements [`Folder`](crate::fold::Folder).
///
/// # Syntax
///
/// ```text
/// Generic = [Lifetime1, Lifetime2, ...] [Type1 [: Bound1], Type2 [: Bound2], ...]
/// Rule    = [ < Generic > ] | Variable1, Variable2 : InputType | { Body }
///
/// folder!( OutputType; [Rule1 Rule2 ... ] )
/// ```
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Explanation
///
/// A folding rule is much like a closure, except that it must annotate the element type:
///
/// ```text
/// |acc, x: i32| { acc + x }
/// ```
///
/// NOTE: You'd better not annotate types for the accumulation value and return value,
/// because they must to be annotated uniformly. Of course you can do that,
/// but there would be no advantage other than potential compilation errors.
///
/// Also supports adding `mut`:
///
/// ```text
/// |mut acc, mut x: i32| -> i64 { acc += 1; x += 1; acc + x }
/// ```
///
/// You can also introduce generic types like this:
///
/// ```text
/// <T: ToString> |x: Option<T>| { x.unwrap().to_string() }
/// ```
///
/// You need to determine the type of the accumulation value, for example, `i32`.
/// Then, construct folding rules for all element types in the tuple,
/// and then combine them in the [`folder!`](crate::folder!) macro to folding the tuple:
///
/// ```
/// use std::convert::AsRef;
/// use tuplez::{folder, tuple, TupleLike};
///
/// let tup = tuple!(1, "2", 3.0);
/// let result = tup.fold(
///     folder!{i32;        // Annotate the accumulation value type
///         |acc, x: i32| { acc + x }
///         |acc, x: f32| { acc + (x as i32) }
///         // `str` is a DST, so `?Sized` bound is required.
///         <T: AsRef<str> + ?Sized > |acc, x: &T| { acc + x.as_ref().parse::<i32>().unwrap() }
///     },
///     0
/// );
/// assert_eq!(result, 6);
/// ```
pub use tuplez_macros::folder;

/// Provides a simple way to build a folder that implements [`Folder`](crate::fold::Folder).
///
/// # Syntax
///
/// ```text
/// seq_folder!( [ Closure1, Closure2, ...] )
/// ```
///
/// # Explanation
///
/// Unlike [`folder!`], the [`seq_folder!`] does not do any processing of closures and just wraps them.
/// So your input must fully conform to Rust's closure syntax, and this means:
///
/// 1. You cannot introduce generic types and lifetimes like [`folder!`].
/// 2. You don't need to add braces for closures that only have a single expression, but instead you
/// need to add commas between closures to separate them.
///
/// For example:
///
/// ```
/// use tuplez::{fold::SeqFolder, seq_folder, tuple, TupleLike};
///
/// let tup = tuple!(1, "2", 3.0);
/// let folder = seq_folder!(
///     |acc, x| (acc + x) as f64,
///     |acc: f64, x: &str| acc.to_string() + x,
///     |acc: String, x| acc.parse::<i32>().unwrap() + x as i32,
/// );
/// let tup_folder = folder.to_tuple();
/// let folder = SeqFolder::from(tup_folder);
/// let result = tup.fold(folder, 0);
/// assert_eq!(result, 15);
/// ```
pub use tuplez_macros::seq_folder;
