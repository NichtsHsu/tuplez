#![cfg_attr(feature = "any_array", allow(incomplete_features))]
#![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
#![cfg_attr(feature = "any_array", feature(maybe_uninit_uninit_array))]
#![cfg_attr(feature = "any_array", feature(maybe_uninit_array_assume_init))]
#![cfg_attr(feature = "any_array", feature(maybe_uninit_uninit_array_transpose))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

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
//! The advantage of this representation is that
//! [you can implement methods recursively for all tuples](Tuple#trait-implementations-on-tuple),
//! and there is no longer a limit on the number of tuple's elements. And, in almost all cases,
//! the [`Tuple`] takes no more memory than the primitive tuples.
//!
//! # Functionality
//!
//! * [Create tuples](tuple!) with any number of elements.
//! * [Access elements](get!) in a tuple at any index, or by their types.
//! * [Push element](TupleLike::push()) to a tuple or [pop element](TupleLike::pop()) from a tuple.
//! * [Join](TupleLike::join()) two tuples or [split](split_at!) a tuple into two parts.
//! * [Rich tuple operations](TupleLike), e.g.: [reverse](TupleLike::rev()),
//!   [left rotate](TupleLike::rot_l()), [zip](TupleLike::zip()).
//! * [Get subsequences](Tuple#get-subsequences).
//! * If all element types implement a `Trait` (e.g. `Eq`, `Add`), then the [`Tuple`] also implement that `Trait`.
//!   [See which traits are supported and learn how to implement your custom traits for `Tuple`](Tuple#trait-implementations-on-tuple).
//! * [Traverse all elements](Tuple#traverse-tuples) of a tuple, or [fold](Tuple#fold-tuples) a tuple.
//! * When the number of elements of a tuple doesn't exceed 32, then it can be converted from/to
//!   [a primitive tuple](Tuple#convert-fromto-primitive-tuples)
//!   or [a primitive array](Tuple#convert-fromto-primitive-arrays).
//!
//! # Optional features
//!
//! * `unwrap` : (*by default*) Allows converting a tuple whose elements are all wrappers
//!   into a tuple of the values those wrappers contain.
//! * `uninit`: Add APIs for tuples consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
//! * `serde`: Derive `Serialize` and `Deserialize` for tuples.
//! * `std`: (*by default*) Use standard library. It also enables `std` feature of [serde](https://crates.io/crates/serde).
//! * `alloc`: Use standard `alloc` library. It also enables `alloc` feature of [serde](https://crates.io/crates/serde).
//!   This feature is usually used when `std` is disabled.
//! * `any_array`: (*nightly*) Use Rust's unstable feature to implement conversion
//!   from/to primitive arrays on tuples with any number of elements.
//!   This feature requires compiling with rustc released to nightly channel.
//!
//! Bundles:
//!
//! * `default`: Enable default features, which are: `std`, `unwrap`.
//! * `full-no-std`: Enable all features available on stable Rust without `std`, which are: `serde`, `uninit` and `unwrap`.
//!   Note that `default-features = false` is necessary.
//! * `full`: Enable all features available on stable Rust, which are: `serde`, `std`, `uninit` and `unwrap`.
//! * `full-nightly`: Enable all features (requires nightly Rust).
//!
//! # Examples
//!
//! ```
//! # #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
//! #
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
//!     tuple!(
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

#[cfg(not(feature = "std"))]
extern crate core as std;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc;

pub mod fold;
pub mod foreach;
mod macros;
pub mod ops;
pub mod predicate;
pub mod search;
mod tuple;
mod tupleize;

#[cfg(feature = "uninit")]
#[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
pub mod uninit;

#[cfg(feature = "any_array")]
mod any_array;

#[cfg(feature = "unwrap")]
#[cfg_attr(docsrs, doc(cfg(feature = "unwrap")))]
pub mod unwrap;

pub use tuple::*;

pub use tupleize::Tupleize;

// Used for re-exporting.
#[doc(hidden)]
pub use tuplez_macros::{
    folder as folder_inner, mapper as mapper_inner, split_at as split_at_inner, take as take_inner,
    tuple as tuple_inner, tuple_pat as tuple_pat_inner, tuple_t as tuple_t_inner,
    unary_pred as unary_pred_inner,
};

/// Get the element at a specific index of the tuple.
///
/// The [`get_ref()`](TupleLike::get_ref()) and [`get_mut()`](TupleLike::get_mut())
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

/// Pick some elements from a tuple.
///
/// # Syntax
///
/// ```text
/// IndicesGroup      = Index [ - Index ]
///
/// pick!(Expr; IndicesGroup1 [, IndicesGroup2, ...] )
/// ```
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputting `...`.*
///
/// **The index must be an integer literal** since procedural macros do not yet support evaluating constants.
///
/// # Explanation
///
/// The `pick!` macro allows you to pick some elements you want from a tuple to a new tuple,
/// and the unpicked elements will be put into a new tuple.
///
/// ```
/// use tuplez::{pick, tuple};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3], Some(9.8), 'c');
/// let (picked, unpicked) = pick!(tup; 3, 1, 5);
/// assert_eq!(picked, tuple!([1, 2, 3], "hello", 'c'));
/// assert_eq!(unpicked, tuple!(1, 3.14, Some(9.8)));
/// ```
///
/// You can abbreviate the continuous part as `start - end`:
///
/// ```
/// use tuplez::{pick, tuple};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3], Some(9.8), 'c');
/// let (picked, unpicked) = pick!(tup; 4, 1-3);
/// assert_eq!(picked, tuple!(Some(9.8), "hello", 3.14, [1, 2, 3]));
/// assert_eq!(unpicked, tuple!(1, 'c'));
/// ```
///
/// Of course, reverse ranges are also supported:
///
/// ```
/// use tuplez::{pick, tuple};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3], Some(9.8), 'c');
/// let (picked, unpicked) = pick!(tup; 4, 3-1);    // `3-1` is reverse range
/// assert_eq!(picked, tuple!(Some(9.8), [1, 2, 3], 3.14, "hello"));
/// assert_eq!(unpicked, tuple!(1, 'c'));
/// ```
///
/// If Rust's move checker allows it, then you can pick the same element multiple times:
///
/// ```
/// use tuplez::{pick, tuple};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3], Some(9.8), 'c');
/// let (picked, unpicked) = pick!(tup; 1, 1, 1, 5, 5);
/// assert_eq!(picked, tuple!("hello", "hello", "hello", 'c', 'c'));
/// assert_eq!(unpicked, tuple!(1, 3.14, [1, 2, 3], Some(9.8)));
/// ```
///
/// Another common use is when you want to pick references to some elements of the original tuple:
///
/// ```
/// use tuplez::{get, pick, tuple, TupleLike};
///
/// let mut tup = tuple!(1, "hello", 3.14, [1, 2, 3], Some(9.8), 'c');
/// let (picked, _) = pick!(tup.as_mut(); 3, 0);
/// get!(picked; 0).rotate_left(1);
/// *get!(picked; 1) += 100;
/// assert_eq!(tup, tuple!(101, "hello", 3.14, [2, 3, 1], Some(9.8), 'c'));
/// ```
///
/// NOTE: Unlike [`take!`], even if you [`pick!`] only one element, you still get a tuple.
pub use tuplez_macros::pick;

/// Swap two parts of a tuple.
///
/// # Syntax
///
/// ```text
/// IndicesGroup      = Index [ - Index ]
///
/// swap_at!(Expr; IndicesGroup1 , IndicesGroup2 )
/// ```
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// **The index must be an integer literal** since procedural macros do not yet support evaluating constants.
///
/// # Explanation
///
/// You can swap two elements of a tuple, then generating a new tuple:
///
/// ```
/// use tuplez::{swap_at, tuple};
///
/// let tup = tuple!(1, "2", 3.14, [1, 2, 3], Some(9.8), 'c', 14);
/// let tup2 = swap_at!(tup; 0, 4);
/// assert_eq!(tup2, tuple!(Some(9.8), "2", 3.14, [1, 2, 3], 1, 'c', 14));
/// ```
///
/// You can also specify a continuous range of elements via `start - end`,
/// but the number of elements on both sides must be equal:
///
/// ```
/// use tuplez::{swap_at, tuple};
///
/// let tup = tuple!(1, "2", 3.14, [1, 2, 3], Some(9.8), 'c', 14);
/// let tup2 = swap_at!(tup; 0-2, 3-5);
/// assert_eq!(tup2, tuple!([1, 2, 3], Some(9.8), 'c', 1, "2", 3.14, 14));
/// ```
///
/// Of course, reverse ranges are also supported:
///
/// ```
/// use tuplez::{swap_at, tuple};
///
/// let tup = tuple!(1, "2", 3.14, [1, 2, 3], Some(9.8), 'c', 14);
/// let tup2 = swap_at!(tup; 0-2, 5-3);
/// assert_eq!(tup2, tuple!('c', Some(9.8), [1, 2, 3], 3.14, "2", 1, 14));
/// ```
pub use tuplez_macros::swap_at;

/// Pass the elements of a tuple as arguments to a function or method.
///
/// # Syntax
///
/// ```text
/// ArgsGroup   = [ & [mut] ] Index [ - Index ]
///
/// apply!( Expr => Func ( [ArgsGroup1, ArgsGroup2, ...] ) )
/// ```
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputting `...`.*
///
/// **The index must be an integer literal** since procedural macros do not yet support evaluating constants.
///
/// # Explanation
///
/// You can pass the elements of the tuple into the function or method in the order you want:
///
/// ```
/// use tuplez::{tuple, apply};
///
/// fn test(_: i32, _: f64, _: &str) {}
///
/// let tup = tuple!(3.4, 2, "hello", [1, 2, 3], 8);
/// apply!(tup => test(4, 0, 2));   // Expand to `test(8, 3.4, "hello")`
/// ```
///
/// Parts in the same order can be omitted in the form `start - end`:
///
/// ```
/// use tuplez::{tuple, apply};
///
/// fn test(_: i32, _: f64, _: &str, _: [i32; 3]) {}
///
/// let tup = tuple!([1, 2, 3], 2, 3.4, "hello", 9);
/// apply!(tup => test(1-3, 0));    // `1-3` expands to `1, 2, 3`
/// ```
///
/// And reverse ranges are also supported:
///
/// ```
/// use tuplez::{tuple, apply};
///
/// fn test(_: &str, _: f64, _: i32, _: [i32; 3]) {}
///
/// let tup = tuple!([1, 2, 3], 2, 3.4, "hello", 9);
/// apply!(tup => test(3-1, 0));    // `3-1` expands to `3, 2, 1`
/// ```
///
/// You can add `&` or `&mut` to elements to borrow them. Here is a slightly more complex example:
///
/// ```
/// use tuplez::{tuple, apply};
///
/// struct DoIt<T>(T);
/// impl<T> DoIt<T> {
///     fn do_sth(&self, _: String, _: f64, _: &str, _: &mut i32, _: &mut [T; 3], _: &i32) {}
/// }
///
/// let tup = tuple!(
///     1,
///     [5, 2, 4],
///     9.8,
///     "world".to_string(),
///     3.14,
///     "hello",
///     7,
///     "zzz"
/// );
/// apply!(tup => DoIt::<i32>(7).do_sth(3-5, &mut 0-1, &6));
/// ```
///
/// NOTE: [`apply!`] consumes the tuple, even if you add `&` or `&mut` to each elements.
/// Sometimes you can avoid this by adding a `&` or `&mut` before the tuple:
///
/// ```
/// use tuplez::{tuple, apply};
///
/// fn push(v: &mut Vec<i32>, x: i32) {
///     v.push(x)
/// }
///
/// let mut tup = tuple!(vec![1, 2], 3);
/// apply!(&mut tup => push(&mut 0, 1));
/// assert_eq!(tup, tuple!(vec![1, 2, 3], 3));
/// ```
///
/// It is worth mentioning that the input tuple can be any expression.
/// The `&tup` and the `&mut tup` are just two of the many possible inputs.
///
/// You can use the same element multiple times as long as Rust's move checker and borrow checker allow it:
///
/// ```
/// use tuplez::{tuple, apply};
///
/// fn test(_: i32, _: i32, _: i32, _: &i32, _: &i32, _: &mut i32) {}
///
/// let tup = tuple!(1, 2, 3);
/// apply!(tup => test(0-2, &1-2, &mut 0));
/// ```
pub use tuplez_macros::apply;

/// Derive [`Tupleize`] on struct.
pub use tuplez_macros::Tupleize;
