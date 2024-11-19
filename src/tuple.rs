#[cfg(feature = "uninit")]
use crate::uninit::*;
#[cfg(feature = "unwrap")]
use crate::unwrap::*;
use crate::{fold::Foldable, foreach::Foreach, macros::*, ops::*, predicate::*, search::*};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "uninit")]
use std::mem::MaybeUninit;
use std::{
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    pin::Pin,
};
use tuplez_macros::tuple_traits_impl;

/// The unit type that represents tuples of zero elements.
///
/// Compared with [`Tuple`] type, the unit type does not implement the [`Poppable`] trait.
///
/// Suggestion: Use the parameterless [`tuple!`](crate::tuple!) macro to create a unit:
///
/// ```
/// use tuplez::tuple;
/// let unit = tuple!();
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Unit;

/// The type used to represent tuples containing at least one element.
///
/// See [`Unit`] type which represents tuples containing no elements.
///
/// The [`TupleLike`] trait defines the basic methods of all [`Tuple`] types and [`Unit`] type.
/// Check out [`TupleLike`]'s documentation page to see exactly what APIs are available.
///
/// # Build a tuple
///
/// You can create a tuple quickly and easily using the [`tuple!`](crate::tuple!) macro:
///
/// ```
/// use tuplez::tuple;
/// let tup = tuple!(1, "hello", 3.14);
/// ```
///
/// Use `;` to indicate repeated elements:
///
/// ```
/// use tuplez::tuple;
/// assert_eq!(tuple!(1.0, 2;3, "3"), tuple!(1.0, 2, 2, 2, "3"));
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
///
/// # Representation
///
/// Unlike [primitive tuple types](https://doc.rust-lang.org/std/primitive.tuple.html),
/// [`Tuple`] uses a recursive form of representation:
///
/// ```text
/// Primitive tuple representation:
///     (T0, T1, T2, T3)
/// `Tuple` representation:
///     Tuple<T0, Tuple<T1, Tuple<T2, Tuple<T3, Unit>>>>
/// ```
///
/// ... but don’t worry, in almost all cases [`Tuple`] will not take up more memory:
///
/// ```
/// use std::mem::size_of;
/// use tuplez::{Tuple, Unit};
///
/// assert_eq!(size_of::<(i32, f64, &str)>(),
///     size_of::<Tuple<i32, Tuple<f64, Tuple<&str, Unit>>>>());
/// ```
///
/// The advantage of using the recursive form of representation is that we can implement
/// a variety of methods on tuples of any length, instead of only implementing these methods
/// on tuples of length less than 12 (or 32).
///
/// **As a shorthand, we use `Tuple<T0, T1, ... Tn>` to represent a [`Tuple`] type containing `N+1` elements**
/// **in the following text, please keep in mind that this is not a true [`Tuple`] representation.**
///
/// A [`Tuple`] can also be used as one of the elements of another [`Tuple`], without restriction.
///
/// # Explicit tuple types
///
/// In most cases, `Tuple` or `Tuple<_, _>` is sufficient to meet the syntax requirements:
///
/// ```
/// # #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
///
/// use tuplez::Tuple;
///
/// let tup = Tuple::from((1, "hello", 3.14)); // or
/// let tup: Tuple<_, _> = From::from((1, "hello", 3.14));
/// ```
///
/// But sometimes, you may still need to annotate the complete tuple type explicitly.
/// At this point, you can use the [`tuple_t!`](crate::tuple_t) macro to generate it:
///
/// ```
/// use tuplez::{tuple, tuple_t};
///
/// let tup: tuple_t!(i32, String, f64) = Default::default();
/// assert_eq!(tup, tuple!(0, String::new(), 0.0));
///
/// let unit: tuple_t!() = Default::default();
/// assert_eq!(unit, tuple!());
///
/// fn use_tuple(tup: tuple_t!(i32, &dyn std::fmt::Debug, tuple_t!(String, String))) {
///     todo!()
/// }
/// ```
///
/// Use `;` to indicate repeated types:
///
/// ```
/// use tuplez::{tuple, tuple_t};
///
/// let tup: tuple_t!(i32, f64;3, i32) = tuple!(1, 2.0, 3.0, 4.0, 5);
/// ```
///
/// Sometimes, you may want to know the exact type of a tuple variable, so that you can call an associated method
/// of this tuple type, such as, [`Default::default()`]. However, the signature of this type can be very long
/// and complex, and you may not want to write it out completely via [`tuple_t!`](crate::tuple_t!).
///
/// Here's a little trick that might help:
///
/// ```
/// use tuplez::tuple;
///
/// fn default_by<T: Default>(_: &T) -> T {
///     T::default()
/// }
///
/// let tup = tuple!([1, 2, 3], tuple!("hello".to_string(), 3.14), 8);
/// let tup2 = default_by(&tup);
/// assert_eq!(tup2, tuple!([0; 3], tuple!(String::new(), 0.0), 0));
/// ```
///
/// # Element access
///
/// There is a [`get!`](crate::get) macro that can be used to get elements,
/// the only restriction is that the index must be an integer literal:
///
/// ```
/// use tuplez::{get, tuple};
///
/// let tup = tuple!(1, "hello", 3.14);
/// assert_eq!(get!(tup; 0), 1);
/// assert_eq!(get!(tup; 1), "hello");
/// assert_eq!(get!(tup; 2), 3.14);
/// ```
///
/// This macro will be expanded to standard member access syntax:
///
/// ```text
/// get!(tup; 0) => tup.0
/// get!(tup; 1) => tup.1.0
/// get!(tup; 2) => tup.1.1.0
/// ```
///
/// ... so, here's an example of modifying elements:
///
/// ```
/// use tuplez::{get, tuple};
///
/// fn add_one(x: &mut i32) { *x += 1; }
///
/// let mut tup = tuple!(1, "hello", 3.14);
/// add_one(&mut get!(tup; 0));
/// assert_eq!(tup, tuple!(2, "hello", 3.14));
/// ```
///
/// # Push, pop, join and split
///
/// Any tuple can push further elements, or join another one, with no length limit.
///
/// ```
/// use tuplez::{tuple, TupleLike};
///
/// let tup = tuple!();
///
/// let tup2 = tup.push(1);             // Push element to back
/// assert_eq!(tup2, tuple!(1));
///
/// let tup3 = tup2.push_back("hello"); // Same as `push`, push element to back
/// assert_eq!(tup3, tuple!(1, "hello"));
///
/// let tup4 = tup3.push_front(3.14);   // Push element to front
/// assert_eq!(tup4, tuple!(3.14, 1, "hello"));
///
/// let tup5 = tup3.join(tup4);         // Join two tuples
/// assert_eq!(tup5, tuple!(1, "hello", 3.14, 1, "hello"));
/// ```
///
/// [`Unit`]s are not [`Poppable`], and all [`Tuple`]s are [`Poppable`]:
///
/// ```
/// use tuplez::{tuple, TupleLike};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3]);
///
/// let (tup2, arr) = tup.pop();        // Pop element from back
/// assert_eq!(tup2, tuple!(1, "hello", 3.14));
/// assert_eq!(arr, [1, 2, 3]);
///
/// let (tup3, pi) = tup2.pop_back();   // Same as `pop`, pop element from back
/// assert_eq!(tup3, tuple!(1, "hello"));
/// assert_eq!(pi, 3.14);
///
/// let (tup4, num) = tup3.pop_front();  // Pop element from front
/// assert_eq!(tup4, tuple!("hello"));
/// assert_eq!(num, 1);
///
/// let (unit, hello) = tup4.pop();
/// assert_eq!(unit, tuple!());
/// assert_eq!(hello, "hello");
///
/// // _ = unit.pop()                   // Error: cannot pop a `Unit`
/// ```
///
/// The [`take!`](crate::take!) macro can take out an element by its index or type:
///
/// ```
/// use tuplez::{take, tuple};
///
/// let tup = tuple!(1, "hello", 3.14, [1, 2, 3]);
///
/// let (element, remainder) = take!(tup; 2);
/// assert_eq!(element, 3.14);
/// assert_eq!(remainder, tuple!(1, "hello", [1, 2, 3]));
///
/// let (element, remainder) = take!(tup; &str);
/// assert_eq!(element, "hello");
/// assert_eq!(remainder, tuple!(1, 3.14, [1, 2, 3]));
/// ```
///
/// You can use the [`split_at!`](crate::split_at) macro to split a tuple into two parts.
/// Like the [`get!`](crate::get) macro, the index must be an integer literal:
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
///
/// # Get subsequences
///
/// You can get a subsequence of a tuple via the [`subseq()`](TupleLike::subseq()) method:
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
///
/// You can also get a continuous subsequence via the [`con_subseq()`](TupleLike::con_subseq()),
/// it may do somethings that [`subseq()`](TupleLike::subseq) cannot do:
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
///
/// There are also many methods about subsequence: [`subseq_ref()`](TupleLike::subseq_ref()),
/// [`subseq_mut()`](TupleLike::subseq_mut()), [`swap_subseq()`](TupleLike::swap_subseq()),
/// [`replace_subseq()`](TupleLike::replace_subseq()), [`con_subseq_ref()`](TupleLike::con_subseq_ref()),
/// [`con_subseq_mut()`](TupleLike::con_subseq_mut()), [`swap_con_subseq()`](TupleLike::swap_con_subseq()),
/// [`replace_con_subseq()`](TupleLike::replace_con_subseq()).
/// Please refer to their own documentation.
///
/// # Trait implementations on [`Tuple`]
///
/// For `Tuple<T0, T1, ... Tn>`, when all types `T0`, `T1`, ... `Tn` implement the [`Debug`] /
/// [`Clone`] / [`Copy`] / [`PartialEq`] / [`Eq`] / [`PartialOrd`] / [`Ord`] / [`Hash`] / [`Default`] /
/// [`Neg`] / [`Not`] trait(s), then the `Tuple<T0, T1, ... Tn>` also implements it/them.
///
/// For example:
///
/// ```
/// use tuplez::tuple;
///
/// let tup = tuple!(false, true, 26u8);            // All elements implement `Not`
/// assert_eq!(!tup, tuple!(true, false, 229u8));   // So `Tuple` also implements `Not`
/// ```
///
/// For `Tuple<T0, T1, ... Tn>` and `Tuple<U0, U1, ... Un>`, when each `Ti` implements
/// `Trait<Ui>` if the `Trait` is [`Add`] / [`AddAssign`] / [`Sub`] / [`SubAssign`] /
/// [`Mul`] / [`MulAssign`] / [`Div`] / [`DivAssign`] / [`Rem`] / [`RemAssign`] /
/// [`BitAnd`] / [`BitAndAssign`] / [`BitOr`] / [`BitOrAssign`] / [`BitXor`] / [`BitXorAssign`]
/// / [`Shl`] / [`ShlAssign`] / [`Shr`] / [`ShrAssign`],
/// then `Tuple<T0, T1, ... Tn>` also implements `Trait<Tuple<U0, U1, ... Un>>`.
///
/// For example:
///
/// ```
/// use tuplez::tuple;
///
/// let tup1 = tuple!(5, "hello ".to_string());
/// let tup2 = tuple!(4, "world");
/// assert_eq!(tup1 + tup2, tuple!(9, "hello world".to_string()));
/// ```
///
/// If the number of elements on both sides is not equal, then the excess will be retained as is:
///
/// ```
/// use tuplez::tuple;
///
/// let x = tuple!(10, "hello".to_string(), 3.14, vec![1, 2]);
/// let y = tuple!(5, " world");
/// assert_eq!(x + y, tuple!(15, "hello world".to_string(), 3.14, vec![1, 2]));
/// ```
///
/// # Traverse tuples
///
/// You can traverse tuples by [`foreach()`](TupleLike::foreach()).
///
/// Call [`foreach()`](TupleLike::foreach()) on a tuple requires a mapper implementing
/// [`Mapper`](crate::foreach::Mapper) as the parameter. Check its documentation page for examples.
///
/// However, here are two ways you can quickly build a mapper.
///
/// ## Traverse tuples by element types
///
/// The [`mapper!`](crate::mapper!) macro helps you build a mapper that traverses tuples according to their element types.
///
/// For example:
///
/// ```
/// use tuplez::{mapper, tuple, TupleLike};
///
/// let tup = tuple!(1, "hello", 3.14).foreach(mapper! {
///     |x: i32| -> i64 { x as i64 }
///     |x: f32| -> String { x.to_string() }
///     <'a> |x: &'a str| -> &'a [u8] { x.as_bytes() }
/// });
/// assert_eq!(tup, tuple!(1i64, b"hello" as &[u8], "3.14".to_string()));
/// ```
///
/// ## Traverse tuples in order of their elements
///
/// You can create a new tuple with the same number of elements, whose elements are all callable objects that accepts an element
/// and returns another value ([`FnOnce(T) -> U`](std::ops::FnOnce)), then, you can use that tuple as a mapper.
//
/// ```
/// use tuplez::{tuple, TupleLike};
///
/// let tup = tuple!(1, 2, 3);
/// let result = tup.foreach(
///     tuple!(
///         |x| x as f32,
///         |x: i32| x.to_string(),
///         |x: i32| Some(x),
///     )
/// );
/// assert_eq!(result, tuple!(1.0, "2".to_string(), Some(3)));
/// ```
///
/// # Fold tuples
///
/// You can fold tuples by [`fold()`](TupleLike::fold()).
///
/// Call [`fold()`](TupleLike::fold()) on a tuple requires a folder implementing
/// [`Folder`](crate::fold::Folder) as the parameter. Check its documentation page for examples.
///
/// However, here are two ways you can quickly build a folder.
///
/// ## Fold tuples by element types
///
/// The [`folder!`](crate::folder!) macro helps you build a folder that folds tuples according to their element types.
///
/// For example:
///
/// ```
/// use tuplez::{folder, tuple, TupleLike};
///
/// let tup = tuple!(Some(1), "2", Some(3.0));
/// let result = tup.fold(
///     folder! { String; // Type of `acc` of all closures must be the same and annotated at the front
///         |acc, x: &str| { acc + &x.to_string() }
///         <T: ToString> |acc, x: Option<T>| { acc + &x.unwrap().to_string() }
///     },
///     String::new(),
/// );
/// assert_eq!(result, "123".to_string());
/// ```
///
/// ## Fold tuples in order of their elements
///
/// You can create a new tuple with the same number of elements, whose elements are all callable objects that accepts the accumulation value
/// and an element and returns new accumulation value ([`FnOnce(Acc, T) -> Acc`](std::ops::FnOnce)), then, you can use that tuple as a folder.
///
/// For example:
///
/// ```
/// use tuplez::{tuple, TupleLike};
///
/// let tup = tuple!(1, "2", 3.0);
/// let result = tup.fold(
///     tuple!(
///         |acc, x| (acc + x) as f64,
///         |acc: f64, x: &str| acc.to_string() + x,
///         |acc: String, x| acc.parse::<i32>().unwrap() + x as i32,
///     ),  // Type of `acc` of each closure is the return type of the previous closure.
///     0,
/// );
/// assert_eq!(result, 15);
/// ```
///
/// # Convert from/to primitive tuples
///
/// Okay, we're finally talking about the only interfaces of [`Tuple`] that limits the maximum number of elements.
///
/// Since Rust does not have a way to represent [primitive tuple types](https://doc.rust-lang.org/std/primitive.tuple.html) with an arbitrary number of elements,
/// the interfaces for converting from/to primitive tuple types is only implemented for [`Tuple`]s with no more than 32 elements.
///
/// ```
/// # #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
///
/// use tuplez::{ToPrimitive, tuple, Tuple, tuple_t};
///
/// let tup = tuple!(1, "hello", 3.14);
/// let prim_tup = (1, "hello", 3.14);
/// assert_eq!(tup.primitive(), prim_tup);
/// assert_eq!(tup, Tuple::from(prim_tup));
///
/// let unit = tuple!();
/// let prim_unit = ();
/// assert_eq!(unit.primitive(), prim_unit);
/// assert_eq!(unit, <tuple_t!()>::from(prim_unit));
/// ```
///
/// # Convert from/to primitive arrays
///
/// If all elements of a tuple are of the same type, then it can be converted from/to [primitive arrays](std::array).
///
/// Currently tuples cannot be converted from/to primitive arrays with no limit on the number of elements,
/// since the [generic constant expressions](https://github.com/rust-lang/rust/issues/76560) feature is still unstable yet.
///
/// Therefore, by default only tuples with no more than 32 elements are supported to be converted from/to primitive arrays.
///
/// However, if you are OK with using rustc released to nightly channel to compile codes with unstable features,
/// you can enable the `any_array` feature, then tuplez will use unstable features to implement conversion from/to
/// primitive arrays on tuples of any number of elements.
///
/// ```toml
/// tuplez = { features = [ "any_array" ] }
/// ```
///
/// For examples:
///
/// ```
/// // Enable Rust's `generic_const_exprs` feature if you enable tuplez's `any_array` feature.
/// #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
///
/// use tuplez::{ToArray, tuple, tuple_t};
///
/// assert_eq!(tuple!(1, 2, 3, 4, 5, 6).to_array(), [1, 2, 3, 4, 5, 6]);
/// assert_eq!(<tuple_t!(i32; 4)>::from([1, 2, 3, 4]), tuple!(1, 2, 3, 4));
///
/// // `Unit` can be converted from/to array of any element type
/// let _ : [i32; 0] = tuple!().to_array();
/// let _ : [String; 0] = tuple!().to_array();
/// let _ = <tuple_t!()>::from([3.14; 0]);
/// let _ = <tuple_t!()>::from([""; 0]);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Tuple<First, Other>(
    /// First element.
    pub First,
    /// Other elements. See [representation](Tuple#representation).
    pub Other,
);

/// Define the basic methods of tuples.
///
/// NOTE: Due to the limitation that Rust does not support the variadic to represent
/// [primitive tuple types]((https://doc.rust-lang.org/std/primitive.tuple.html)) containing any number of elements,
/// we cannot make [`TupleLike`] trait contain a method that converts tuple to the primitive tuple type.
/// Therefore, this method is provided by the trait [`ToPrimitive`] and is only implemented for tuples with no more than 32 elements.
pub trait TupleLike {
    /// The type of tuple containing immutable references to all elements of the tuple.
    type AsRefOutput<'a>: TupleLike
    where
        Self: 'a;

    /// The type of tuple containing mutable references to all elements of the tuple.
    type AsMutOutput<'a>: TupleLike
    where
        Self: 'a;

    /// The type of tuple containing pointers to all elements of the tuple.
    type AsPtrOutput: TupleLike;

    /// The type of tuple containing mutable pointers to all elements of the tuple.
    type AsMutPtrOutput: TupleLike;

    /// The type of tuple containing [`Pin`]s of immutable references to all elements of the tuple.
    type AsPinRefOutput<'a>: TupleLike
    where
        Self: 'a;

    /// The type of tuple containing [`Pin`]s of mutable references to all elements of the tuple.
    type AsPinMutOutput<'a>: TupleLike
    where
        Self: 'a;

    /// The type of tuple generated by pushing an element to the front of the tuple.
    type PushFrontOutput<T>: TupleLike;

    /// The type of tuple generated by pushing an element to the back of the tuple.
    type PushBackOutput<T>: TupleLike;

    /// The type of tuple generated by reversing the tuple.
    type RevOutput: TupleLike;

    /// The type of tuple generated by joining two tuples.
    type JoinOutput<T>: TupleLike
    where
        T: TupleLike;

    /// The type of tuple after wrapping all elements into [`Option`](std::option::Option).
    type ToSomeOutput: TupleLike;

    /// The type of tuple after wrapping all elements into [`Result`](std::result::Result).
    type ToOkOutput<E>: TupleLike;

    /// The type of tuple after wrapping all elements into [`Tuple`].
    type ToTupleOutput: TupleLike;

    /// The type of tuple after wrapping all elements into [`MaybeUninit`].
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    type Uninit: TupleLike;

    /// The number of elements in the tuple.
    const LEN: usize;

    /// Get the number of elements in the tuple.
    /// MUST always return [`LEN`](TupleLike::LEN).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    /// assert_eq!(tuple!(1, "hello", 3.14).len(), 3);
    /// ```
    fn len(&self) -> usize {
        Self::LEN
    }

    /// Check if tuple is empty.
    ///
    /// Always be `false` if tuple is [`Unit`],
    /// and always be `true` if tuple is [`Tuple`].
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// assert_eq!(tuple!().is_empty(), true);
    /// assert_eq!(tuple!(1, "hello", 3.14).is_empty(), false);
    /// ```
    fn is_empty(&self) -> bool {
        Self::LEN == 0
    }

    /// Creates a “by reference” adapter for this instance.
    ///
    /// It will simply borrow this current tuple.
    fn by_ref(&mut self) -> &mut Self
    where
        Self: Sized,
    {
        self
    }

    /// Convert from `tuple!(x, y, z, ...)` to `tuple!((0, x), (1, y), (2, z), ...)`.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!("hello", Some([1, 2, 3]), tuple!(3.14, 12));
    /// assert_eq!(tup.enumerate(), tuple!(
    ///     (0, "hello"),
    ///     (1, Some([1, 2, 3])),
    ///     (2, tuple!(3.14, 12)),
    /// ));
    /// ```
    fn enumerate(self) -> Self::EnumerateOutput
    where
        Self: Sized + Enumerable,
    {
        Enumerable::enumerate(self, 0)
    }

    /// Take out the searched element, and get the remainder of tuple.
    ///
    /// Add a type annotation to the searched element to let [`take()`](TupleLike::take()) know which one you want.
    ///
    /// **NOTE**: The type of this element must exist only once in the tuple.
    ///
    /// If you want to take out the element at a specific index, see [`take!`](crate::take!).
    ///
    /// If you want to take out the first or last element, see [`pop()`][TupleLike::pop()].
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
    fn take<T, I>(self) -> (T, Self::TakeRemainder)
    where
        Self: Search<T, I> + Sized,
    {
        Search::take(self)
    }

    /// Get an immutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`get_ref()`](TupleLike::get_ref()) know which one you want.
    ///
    /// **NOTE**: The type of this element must exist only once in the tuple.
    ///
    /// If you want to get the element by its index, see [`get!`](crate::get!);
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
    fn get_ref<T, I>(&self) -> &T
    where
        Self: Search<T, I> + Sized,
    {
        Search::get_ref(self)
    }

    /// Get a mutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`get_mut()`](TupleLike::get_mut()) know which one you want.
    ///
    /// **NOTE**: The type of this element must exist only once in the tuple.
    ///
    /// If you want to get the element by its index, see [`get!`](crate::get!);
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
    fn get_mut<T, I>(&mut self) -> &mut T
    where
        Self: Search<T, I> + Sized,
    {
        Search::get_mut(self)
    }

    /// Swap a specific element of the same type with another value.
    ///
    /// **NOTE**: The type of this element must exist only once in the tuple.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let mut s = "world";
    /// tup.swap(&mut s);
    /// assert_eq!(tup, tuple!(3.14, "world", 5, [1, 2, 3]));
    /// assert_eq!(s, "hello");
    /// ```
    fn swap<T, I>(&mut self, value: &mut T)
    where
        Self: Search<T, I>,
    {
        Search::swap(self, value)
    }

    /// Replace a specific element of the same type with another value.
    ///
    /// Return the replaced value.
    ///
    /// **NOTE**: The type of this element must exist only once in the tuple.
    ///
    /// Hint: If you don’t want to consume the input tuple, then what you are looking
    /// for might be [`swap()`](TupleLike::swap()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut tup = tuple!(3.14, "hello", 5, [1, 2, 3]);
    /// let s = tup.replace("world");
    /// assert_eq!(tup, tuple!(3.14, "world", 5, [1, 2, 3]));
    /// assert_eq!(s, "hello");
    /// ```
    fn replace<T, I>(&mut self, value: T) -> T
    where
        Self: Search<T, I>,
    {
        Search::replace(self, value)
    }

    /// Replace a specific element with another value that may be of a different type.
    ///
    /// The new element is generated a the user-defined function.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, 3.14, "hello", Some([1, 2, 3]));
    /// let result = tup.map_replace(|x: f64| x.to_string());
    /// assert_eq!(result, tuple!(1, "3.14".to_string(), "hello", Some([1, 2, 3])))
    /// ```
    fn map_replace<T, U, F, I>(self, f: F) -> Self::MapReplaceOutput<U>
    where
        Self: Search<T, I> + Sized,
        F: FnOnce(T) -> U,
    {
        Search::map_replace(self, f)
    }

    // fn map_replace<T, I>(self, value: T) ->

    /// Take out a subsequence.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Add a type annotation to the subsequence to let [`subseq()`](TupleLike::subseq()) know.
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
    fn subseq<Seq, I>(self) -> Seq
    where
        Self: Subseq<Seq, I> + Sized,
        Seq: TupleLike,
    {
        Subseq::subseq(self)
    }

    /// Similar to [`subseq()`](TupleLike::subseq()),
    /// but all its elements are immutable references to the supersequence's elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
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
    fn subseq_ref<Seq, I>(&self) -> Seq::AsRefOutput<'_>
    where
        Self: Subseq<Seq, I> + Sized,
        Seq: TupleLike,
    {
        Subseq::subseq_ref(self)
    }

    /// Similar to [`subseq()`](TupleLike::subseq()),
    /// but all its elements are mutable references to the supersequence's elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
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
    fn subseq_mut<Seq, I>(&mut self) -> Seq::AsMutOutput<'_>
    where
        Self: Subseq<Seq, I> + Sized,
        Seq: TupleLike,
    {
        Subseq::subseq_mut(self)
    }

    /// Swap elements with a subsequence.
    ///
    /// See [`subseq()`](TupleLike::subseq()) to see which inputs are subsequence.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
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
    fn swap_subseq<Seq, I>(&mut self, subseq: &mut Seq)
    where
        Seq: TupleLike,
        Self: Subseq<Seq, I>,
    {
        Subseq::swap_subseq(self, subseq)
    }

    /// Replace elements with a subsequence.
    ///
    /// See [`subseq()`](TupleLike::subseq()) to see which inputs are subsequence.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// It returns a subsequence consisting of the replaced elements.
    ///
    /// Hint: If you don't want to consume the input tuple,
    /// then what you are looking for might be [`swap_subseq()`](TupleLike::swap_subseq()).
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
    fn replace_subseq<Seq, I>(&mut self, subseq: Seq) -> Seq
    where
        Seq: TupleLike,
        Self: Subseq<Seq, I>,
    {
        Subseq::replace_subseq(self, subseq)
    }

    /// Replace elements of specific subsequence with another sequence
    /// that may be of different element types.
    ///
    /// The elements of new sequence is generated from the user-defined mapper.
    ///
    /// Check out [`Mapper`](crate::foreach::Mapper)’s documentation page to learn how to build a mapper.
    ///
    /// # Example
    ///
    /// ```
    /// use std::fmt::Debug;
    /// use tuplez::{mapper, tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(1, 3.14, "hello", [1, 2, 3]);
    /// let result = tup.map_replace_subseq::<tuple_t!(f64, [i32; 3]), _, _>(mapper! {
    ///     |x: f64| -> i32 { x as i32 }
    ///     <T: Debug, const N: usize> |x: [T; N]| -> String { format!("{x:?}") }
    /// });
    /// assert_eq!(result, tuple!(1, 3, "hello", "[1, 2, 3]".to_string()))
    /// ```
    fn map_replace_subseq<Seq, F, I>(self, f: F) -> Self::MapReplaceOutput
    where
        Seq: TupleLike,
        Self: SubseqMapReplace<Seq, F, I> + Sized,
    {
        SubseqMapReplace::map_replace_subseq(self, f)
    }

    /// Replace elements of specific subsequence with another sequence
    /// that may be of different element types.
    ///
    /// Same as [`map_replace_subseq()`](TupleLike::map_replace_subseq()).
    fn foreach_subseq<Seq, F, I>(self, f: F) -> Self::MapReplaceOutput
    where
        Seq: TupleLike,
        Self: SubseqMapReplace<Seq, F, I> + Sized,
    {
        SubseqMapReplace::map_replace_subseq(self, f)
    }

    /// Take out a contiguous subsequence.
    ///
    /// Unlike [`subseq()`](TupleLike::subseq()), this method requires that all elements of the subsequence are
    /// contiguous in the supersequence. Sometimes it can do things that [`subseq()`](TupleLike::subseq()) can't.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Add a type annotation to the contiguous subsequence to let [`con_subseq()`](TupleLike::con_subseq()) know.
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
    fn con_subseq<Seq, I>(self) -> Seq
    where
        Seq: TupleLike,
        Self: ConSubseq<Seq, I> + Sized,
    {
        ConSubseq::con_subseq(self)
    }

    /// Similar to [`con_subseq()`](TupleLike::con_subseq()),
    /// but all its elements are immutable references to the supersequence's elements.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation,
    /// so you need to call it like:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!(12, "hello", vec![1, 2, 3], 24, 3.14, 36);
    /// let subseq = tup.con_subseq_ref::<tuple_t!(i32, f32), _>();
    /// assert_eq!(subseq, tuple!(&24, &3.14));
    /// ```
    fn con_subseq_ref<Seq, I>(&self) -> Seq::AsRefOutput<'_>
    where
        Seq: TupleLike,
        Self: ConSubseq<Seq, I>,
    {
        ConSubseq::con_subseq_ref(self)
    }

    /// Similar to [`con_subseq()`](TupleLike::con_subseq()),
    /// but all its elements are mutable references to the supersequence's elements.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Rust is almost impossible to infer generic types by the return type annotation,
    /// so you need to call it like:
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
    fn con_subseq_mut<Seq, I>(&mut self) -> Seq::AsMutOutput<'_>
    where
        Seq: TupleLike,
        Self: ConSubseq<Seq, I>,
    {
        ConSubseq::con_subseq_mut(self)
    }

    /// Swap elements with a contiguous subsequence.
    ///
    /// Unlike [`swap_subseq()`](TupleLike::swap_subseq()), this method requires that all
    /// elements of the subsequence are contiguous in the supersequence.
    /// Sometimes it can do things that [`swap_subseq()`](TupleLike::swap_subseq()) can't.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
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
    fn swap_con_subseq<Seq, I>(&mut self, subseq: &mut Seq)
    where
        Seq: TupleLike,
        Self: ConSubseq<Seq, I>,
    {
        ConSubseq::swap_con_subseq(self, subseq)
    }

    /// Replace elements with a contiguous subsequence.
    ///
    /// Unlike [`replace_subseq()`](TupleLike::replace_subseq()), this method requires that
    /// all elements of the subsequence are contiguous in the supersequence.
    /// Sometimes it can do things that [`replace_subseq()`](TupleLike::replace_subseq()) can't.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// It returns a contiguous subsequence consisting of the replaced elements.
    ///
    /// Hint: If you don't want to consume the input tuple,
    /// then what you are looking for might be [`swap_con_subseq()`](TupleLike::swap_con_subseq()).
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
    fn replace_con_subseq<Seq, I>(&mut self, subseq: Seq) -> Seq
    where
        Seq: TupleLike,
        Self: ConSubseq<Seq, I>,
    {
        ConSubseq::replace_con_subseq(self, subseq)
    }

    /// Replace elements of specific contiguous subsequence with another sequence
    /// that may be of different element types.
    ///
    /// The elements of new sequence is generated from the user-defined mapper.
    ///
    /// Check out [`Mapper`](crate::foreach::Mapper)’s documentation page to learn how to build a mapper.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{mapper, tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!("1", "2", "3", true, false, true);
    /// let result = tup.map_replace_con_subseq::<tuple_t!(&str, bool, bool), _, _>(mapper! {
    ///     |x: &str| -> i32 { x.parse().unwrap() }
    ///     |x: bool| -> bool { !x }
    /// });
    /// assert_eq!(result, tuple!("1", "2", 3, false, true, true));
    /// ```
    fn map_replace_con_subseq<Seq, F, I>(self, f: F) -> Self::MapReplaceOutput
    where
        Seq: TupleLike,
        Self: ConSubseqMapReplace<Seq, F, I> + Sized,
    {
        ConSubseqMapReplace::map_replace_con_subseq(self, f)
    }

    /// Replace elements of specific contiguous subsequence with another sequence
    /// that may be of different element types.
    ///
    /// Same as [`map_replace_con_subseq()`](TupleLike::map_replace_con_subseq()).
    fn foreach_con_subseq<Seq, F, I>(self, f: F) -> Self::MapReplaceOutput
    where
        Seq: TupleLike,
        Self: ConSubseqMapReplace<Seq, F, I> + Sized,
    {
        ConSubseqMapReplace::map_replace_con_subseq(self, f)
    }

    /// In the past it was used for the functionality of [`subseq()`](TupleLike::subseq()),
    /// however it did not live up to its name: you actually got a subsequence not a subset while
    /// subsets are not required to maintain a consistent element order as the superset.
    ///
    /// Therefore, it has been deprecated. You can use [`subseq()`](TupleLike::subseq()) or
    /// [`con_subseq()`](TupleLike::con_subseq()) instead.
    #[deprecated(since = "0.10.0", note = "Use subseq() or con_subseq() instead")]
    fn subset<Seq, I>(self) -> Seq
    where
        Self: Subseq<Seq, I> + Sized,
        Seq: TupleLike,
    {
        Subseq::subseq(self)
    }

    /// In the past it was used for the functionality of [`subseq_ref()`](TupleLike::subseq_ref()),
    /// however it did not live up to its name: you actually got a subsequence not a subset while
    /// subsets are not required to maintain a consistent element order as the superset.
    ///
    /// Therefore, it has been deprecated. You can use [`subseq_ref()`](TupleLike::subseq_ref()) or
    /// [`con_subseq_ref()`](TupleLike::con_subseq_ref()) instead.
    #[deprecated(
        since = "0.10.0",
        note = "Use subseq_ref() or con_subseq_ref() instead"
    )]
    fn subset_ref<Seq, I>(&self) -> Seq::AsRefOutput<'_>
    where
        Self: Subseq<Seq, I> + Sized,
        Seq: TupleLike,
    {
        Subseq::subseq_ref(self)
    }

    /// In the past it was used for the functionality of [`subseq_mut()`](TupleLike::subseq_mut()),
    /// however it did not live up to its name: you actually got a subsequence not a subset while
    /// subsets are not required to maintain a consistent element order as the superset.
    ///
    /// Therefore, it has been deprecated. You can use [`subseq_mut()`](TupleLike::subseq_mut()) or
    /// [`con_subseq_mut()`](TupleLike::con_subseq_mut()) instead.
    #[deprecated(
        since = "0.10.0",
        note = "Use subseq_mut() or con_subseq_mut() instead"
    )]
    fn subset_mut<Seq, I>(&mut self) -> Seq::AsMutOutput<'_>
    where
        Self: Subseq<Seq, I> + Sized,
        Seq: TupleLike,
    {
        Subseq::subseq_mut(self)
    }

    /// In the past it was used for the functionality of
    /// [`swap_con_subseq()`](TupleLike::swap_con_subseq()),
    /// but with the addition of [`swap_subseq()`](TupleLike::swap_subseq()),
    /// the functionality of this method becomes very unclear.
    ///
    /// Therefore, it has been deprecated. You can use [`swap()`](TupleLike::swap()),
    /// [`swap_subseq()`](TupleLike::swap_subseq()) or
    /// [`swap_con_subseq()`](TupleLike::swap_con_subseq()) instead.
    #[deprecated(
        since = "0.10.0",
        note = "Use swap(), swap_subseq() or swap_con_subseq() instead"
    )]
    fn swap_with<Seq, I>(&mut self, subseq: &mut Seq)
    where
        Seq: TupleLike,
        Self: ConSubseq<Seq, I>,
    {
        ConSubseq::swap_con_subseq(self, subseq)
    }

    /// In the past it was used for the functionality of
    /// [`replace_con_subseq()`](TupleLike::replace_con_subseq()),
    /// but with the addition of [`replace_subseq()`](TupleLike::replace_subseq()),
    /// the functionality of this method becomes very unclear.
    ///
    /// Therefore, it has been deprecated. You can use [`replace()`](TupleLike::replace()),
    /// [`replace_subseq()`](TupleLike::replace_subseq()) or
    /// [`replace_con_subseq()`](TupleLike::replace_con_subseq()) instead.
    #[deprecated(
        since = "0.10.0",
        note = "Use replace(), replace_subseq() or replace_con_subseq() instead"
    )]
    fn replace_with<Seq, I>(&mut self, subseq: Seq) -> Seq
    where
        Seq: TupleLike,
        Self: ConSubseq<Seq, I>,
    {
        ConSubseq::replace_con_subseq(self, subseq)
    }

    /// Generate a tuple containing immutable references to all elements of the tuple.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let tup = tuple!([1, 2], "hello".to_string());
    /// let tup_ref: tuple_t!(&[i32; 2], &String) = tup.as_ref();
    /// assert_eq!(tup_ref, tuple!(&[1, 2], &String::from("hello")));
    /// ```
    fn as_ref(&self) -> Self::AsRefOutput<'_>;

    /// Generate a tuple containing mutable reference to all elements of the tuple.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, "hello");
    /// let tup_mut = tup.as_mut();
    /// *get!(tup_mut; 0) += 1;
    /// *get!(tup_mut; 1) = "world";
    /// assert_eq!(tup, tuple!(2, "world"));
    /// ```
    fn as_mut(&mut self) -> Self::AsMutOutput<'_>;

    /// Generate a tuple containing pointers to all elements of the tuple.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike};
    ///
    /// let tup = tuple!(1, 3.14, "hello", vec![1, 2, 3]);
    /// let tup_ptr = tup.as_ptr();
    /// let pi = unsafe { &*get!(tup_ptr; 1) };
    /// assert_eq!(pi, &3.14);
    /// ```
    fn as_ptr(&self) -> Self::AsPtrOutput;

    /// Generate a tuple containing mutable pointers to all elements of the tuple.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike};
    ///
    /// let mut tup = tuple!(1, 3.14, "hello", vec![1, 2, 3]);
    /// let tup_ptr = tup.as_mut_ptr();
    /// let v = unsafe { &mut *get!(tup_ptr; 3) };
    /// v.push(4);
    /// assert_eq!(v.len(), 4);
    /// ```
    fn as_mut_ptr(&mut self) -> Self::AsMutPtrOutput;

    /// Convert from [`Pin<&Tuple<T0, T1, T2, ..>`](Pin) to `Tuple<Pin<&T0>, Pin<&T1>, Pin<&T2>, ...>`.
    fn as_pin_ref(self: Pin<&Self>) -> Self::AsPinRefOutput<'_>;

    /// Convert from [`Pin<&mut Tuple<T0, T1, T2, ..>`](Pin) to `Tuple<Pin<&mut T0>, Pin<&mut T1>, Pin<&mut T2>, ...>`.
    fn as_pin_mut(self: Pin<&mut Self>) -> Self::AsPinMutOutput<'_>;

    /// Convert from `&Tuple<T0, T1, T2, ...>` to `Tuple<&T0::Target, &T1::Target, &T2::Target, ..>`
    /// while all the elements of the tuple implement [`Deref`](std::ops::Deref).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(String::from("hello"), Box::new(12), vec![1, 2, 3]);
    /// assert_eq!(tup.as_deref(), tuple!("hello", &12, &[1, 2, 3] as &[_]));
    /// ```
    fn as_deref(&self) -> Self::AsDerefOutput<'_>
    where
        Self: AsDeref,
    {
        AsDeref::as_deref(self)
    }

    /// Convert from `&mut Tuple<T0, T1, T2, ...>` to `Tuple<&mut T0::Target, &mut T1::Target, &mut T2::Target, ..>`
    /// while all the elements of the tuple implement [`DerefMut`](std::ops::DerefMut).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(String::from("hello"), Box::new(12), vec![1, 2, 3]);
    /// let _: tuple_t!(&mut str, &mut i32, &mut [i32]) = tup.as_deref_mut();
    /// ```
    fn as_deref_mut(&mut self) -> Self::AsDerefMutOutput<'_>
    where
        Self: AsDerefMut,
    {
        AsDerefMut::as_deref_mut(self)
    }

    /// If the elements of the tuple are all references, clone its elements to a new tuple.
    ///
    /// # Example:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut string = String::from("hello");
    /// let tup = tuple!(&1, &mut string, &3.14);
    /// assert_eq!(tup.cloned(), tuple!(1, String::from("hello"), 3.14));
    /// ```
    fn cloned(&self) -> Self::ClonedOutput
    where
        Self: Cloned,
    {
        Cloned::cloned(self)
    }

    /// If the elements of the tuple are all references, copy its elements to a new tuple.
    ///
    /// # Example:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut ch = 'c';
    /// let tup = tuple!(&1, &mut ch, &3.14);
    /// assert_eq!(tup.copied(), tuple!(1, 'c', 3.14));
    /// ```
    fn copied(&self) -> Self::CopiedOutput
    where
        Self: Copied,
    {
        Copied::copied(self)
    }

    /// If the elements of the tuple are all references, clone its elements to a new tuple.
    ///
    /// Much like [`cloned()`](TupleLike::cloned()), but can work on types like `&str` or slices.
    ///
    /// # Example:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut arr = [1, 2, 3];
    /// let tup = tuple!(&1, &mut arr as &mut [i32], "hello");
    /// assert_eq!(tup.owned(), tuple!(1, vec![1, 2, 3], "hello".to_string()));
    /// ```
    #[cfg(any(feature = "std", feature = "alloc"))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
    fn owned(&self) -> Self::OwnedOutput
    where
        Self: Owned,
    {
        Owned::owned(self)
    }

    /// Push an element to the back of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let tup2 = tup.push(44);
    /// assert_eq!(tup2, tuple!(1, "hello", 3.14, 44));
    /// ```
    fn push<T>(self, value: T) -> Self::PushBackOutput<T>;

    /// Push an element to the front of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let tup2 = tup.push_front(44);
    /// assert_eq!(tup2, tuple!(44, 1, "hello", 3.14));
    /// ```
    fn push_front<T>(self, value: T) -> Self::PushFrontOutput<T>;

    /// Push an element to the back of the tuple. Same as [`push()`](TupleLike::push()).
    fn push_back<T>(self, value: T) -> Self::PushBackOutput<T>;

    /// Pop an element from the back of the tuple.
    ///
    /// Note: The [`Unit`] type is not [`Poppable`].
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let (tup2, popped) = tup.pop();
    /// assert_eq!(tup2, tuple!(1, "hello"));
    /// assert_eq!(popped, 3.14);
    /// ```
    fn pop(self) -> (Self::PopBackOutput, Self::PopBackElement)
    where
        Self: Poppable + Sized,
    {
        Poppable::pop(self)
    }

    /// Pop an element from the front of the tuple.
    ///
    /// Note: The [`Unit`] type is not [`Poppable`].
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let (tup2, popped) = tup.pop_front();
    /// assert_eq!(tup2, tuple!("hello", 3.14));
    /// assert_eq!(popped, 1);
    /// ```
    fn pop_front(self) -> (Self::PopFrontOutput, Self::PopFrontElement)
    where
        Self: Poppable + Sized,
    {
        Poppable::pop_front(self)
    }

    /// Pop an element from the back of the tuple. Same as [`pop()`](TupleLike::pop()).
    ///
    /// Note: The [`Unit`] type is not [`Poppable`].
    fn pop_back(self) -> (Self::PopBackOutput, Self::PopBackElement)
    where
        Self: Poppable + Sized,
    {
        Poppable::pop_back(self)
    }

    /// Left rotates the elements of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "2", 3.0, 4);
    /// let tup2 = tup.rot_l();
    /// assert_eq!(tup2, tuple!("2", 3.0, 4, 1));
    /// ```
    fn rot_l(self) -> Self::RotLeftOutput
    where
        Self: Rotatable + Sized,
    {
        Rotatable::rot_l(self)
    }

    /// Right rotates the elements of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "2", 3.0, 4);
    /// let tup2 = tup.rot_r();
    /// assert_eq!(tup2, tuple!(4, 1, "2", 3.0));
    /// ```
    fn rot_r(self) -> Self::RotRightOutput
    where
        Self: Rotatable + Sized,
    {
        Rotatable::rot_r(self)
    }

    /// Reverse elements of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let tup2 = tup.rev();
    /// assert_eq!(tup2, tuple!(3.14, "hello", 1));
    /// ```
    fn rev(self) -> Self::RevOutput;

    /// Join two tuples.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let tup2 = tuple!(44, "world");
    /// let tup3 = tup.join(tup2);
    /// assert_eq!(tup3, tuple!(1, "hello", 3.14, 44, "world"));
    /// ```
    fn join<T>(self, value: T) -> Self::JoinOutput<T>
    where
        T: TupleLike;

    /// Convert from `tuple!(a, b, c ...)` to `tuple!(Some(a), Some(b), Some(c) ...)`.
    ///
    /// See [`unwrap()`](TupleLike::unwrap()),
    /// [`unwrap_or_default()`](TupleLike::unwrap_or_default())
    /// or [`try_unwrap()`](TupleLike::try_unwrap()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// assert_eq!(tup.to_some(), tuple!(Some(1), Some("hello"), Some(3.14)));
    /// ```
    fn to_some(self) -> Self::ToSomeOutput;

    /// Convert from `tuple!(a, b, c ...)` to `tuple!(Ok(a), Ok(b), Ok(c) ...)`.
    ///
    /// Note: You need to provide the error type.
    ///
    /// See [`unwrap()`](TupleLike::unwrap()),
    /// [`unwrap_or_default()`](TupleLike::unwrap_or_default())
    /// or [`try_unwrap()`](TupleLike::try_unwrap()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// assert_eq!(tup.to_ok::<()>(), tuple!(Ok(1), Ok("hello"), Ok(3.14)));
    /// ```
    fn to_ok<E>(self) -> Self::ToOkOutput<E>;

    /// Convert from `tuple!(a, b, c ...)` to `tuple!(tuple!(a), tuple!(b), tuple!(c) ...)`.
    ///
    /// See [`untuple()`](TupleLike::untuple()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// assert_eq!(tup.to_tuple(), tuple!(tuple!(1), tuple!("hello"), tuple!(3.14)));
    /// ```
    fn to_tuple(self) -> Self::ToTupleOutput;

    /// Create a new tuple that all elements are wrapped by [`MaybeUninit`](std::mem::MaybeUninit)
    /// and in uninitialized states.
    ///
    /// Similar to [`MaybeUninit::uninit()`](std::mem::MaybeUninit::uninit()), dropping a tuple with uninitialized elements
    /// will never call elements' drop codes. It is your responsibility to make sure elements get dropped if they got initialized.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{TupleLike, tuple_t};
    ///
    /// let uninit = <tuple_t!(i32, &str, Vec<String>)>::uninit();
    /// let _: tuple_t!(MaybeUninit<i32>, MaybeUninit<&str>, MaybeUninit<Vec<String>>) = uninit;
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit() -> Self::Uninit;

    /// Create a new tuple that all elements are wrapped by [`MaybeUninit`](std::mem::MaybeUninit)
    /// and in uninitialized states, with the memory being filled with `0` bytes.
    ///
    /// Similar to [`MaybeUninit::zeroed()`](std::mem::MaybeUninit::zeroed()), dropping a tuple with uninitialized elements
    /// will never call elements' drop codes. It is your responsibility to make sure elements get dropped if they got initialized.
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let uninit = <tuple_t!(i32, bool, *const u8)>::zeroed();
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(0, false, std::ptr::null()));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn zeroed() -> Self::Uninit;

    /// Convert from `tuple!(a, b, c ...)` to `tuple!(MaybeUninit::new(a), MaybeUninit::new(b), MaybeUninit::new(c) ...)`.
    ///
    /// See [`uninit_assume_init()`](TupleLike::uninit_assume_init()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let uninit = tuple!(1, "hello", 3.14).to_uninit();
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(1, "hello", 3.14));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn to_uninit(self) -> Self::Uninit;

    /// Extract the values of a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init()`](std::mem::MaybeUninit::assume_init()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(true);
    /// uninit.uninit_write_one("hello");
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init(self) -> Self::Initialized
    where
        Self: Uninit + Sized,
    {
        Uninit::assume_init(self)
    }

    /// Extract value from a specific [`MaybeUninit`](std::mem::MaybeUninit) element.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init()`](std::mem::MaybeUninit::assume_init()).
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write_one(12);
    /// let first_init = unsafe { uninit.uninit_assume_init_one::<i32, _>() };
    /// assert_eq!(get!(first_init; 0), 12);
    /// let _: tuple_t!(i32, MaybeUninit<bool>, MaybeUninit<&str>) = first_init;
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_one<T, I>(self) -> Self::MapReplaceOutput<T>
    where
        Self: Search<MaybeUninit<T>, I> + Sized,
    {
        Search::map_replace(self, |x| x.assume_init())
    }

    /// Read the values of a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_read()`](std::mem::MaybeUninit::assume_init_read()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Option<Vec<u32>>)>::uninit();
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(None);
    /// let tup1 = unsafe { uninit.uninit_assume_init_read() };
    /// // SAFETY: `i32` implements `Copy`, duplicating a `None` value is safe.
    /// let tup2 = unsafe { uninit.uninit_assume_init_read() };
    /// assert_eq!(tup1, tup2);
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_read(&self) -> Self::Initialized
    where
        Self: Uninit,
    {
        Uninit::assume_init_read(self)
    }

    /// Read one value from a specific [`MaybeUninit`] element.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_read()`](std::mem::MaybeUninit::assume_init_read()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(
    ///     0,
    ///     MaybeUninit::<i32>::new(12),
    ///     "hello",
    ///     MaybeUninit::<f64>::uninit(),
    ///     24
    /// );
    /// let x: i32 = unsafe { tup.uninit_assume_init_read_one() };
    /// assert_eq!(x, 12);
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_read_one<T, I>(&self) -> T
    where
        Self: Search<MaybeUninit<T>, I>,
    {
        Search::get_ref(self).assume_init_read()
    }

    /// Get immutable references to values of a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_ref()`](std::mem::MaybeUninit::assume_init_ref()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
    /// let tup_ref = unsafe { uninit.uninit_assume_init_ref() };
    /// assert_eq!(get!(tup_ref; 0), &12);
    /// assert_eq!(get!(tup_ref; 1), &vec![1, 2, 3]);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_ref(&self) -> <Self::Initialized as TupleLike>::AsRefOutput<'_>
    where
        Self: Uninit,
    {
        Uninit::assume_init_ref(self)
    }

    /// Get immutable reference to value of a specific [`MaybeUninit`](std::mem::MaybeUninit) element.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_ref()`](std::mem::MaybeUninit::assume_init_ref()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(MaybeUninit::<Vec<i32>>::uninit(), "hello", 12);
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let v = unsafe { tup.uninit_assume_init_ref_one::<Vec<i32>, _>() };
    /// assert_eq!(v, &vec![1, 2, 3]);
    /// unsafe { tup.uninit_assume_init_drop_one::<Vec<i32>, _>(); }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_ref_one<T, I>(&self) -> &T
    where
        Self: Search<MaybeUninit<T>, I>,
    {
        Search::get_ref(self).assume_init_ref()
    }

    /// Get mutable references to values of a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_mut()`](std::mem::MaybeUninit::assume_init_mut()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
    /// let tup_mut = unsafe { uninit.uninit_assume_init_mut() };
    /// *get!(tup_mut; 0) += 1;
    /// get!(tup_mut; 1).push(4);
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(13, vec![1, 2, 3, 4]));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_mut(&mut self) -> <Self::Initialized as TupleLike>::AsMutOutput<'_>
    where
        Self: Uninit,
    {
        Uninit::assume_init_mut(self)
    }

    /// Get mutable reference to value of a specific [`MaybeUninit`](std::mem::MaybeUninit) element.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_mut()`](std::mem::MaybeUninit::assume_init_mut()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(MaybeUninit::<Vec<i32>>::uninit(), "hello", 12);
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let v = unsafe { tup.uninit_assume_init_mut_one::<Vec<i32>, _>() };
    /// v.push(4);
    /// assert_eq!(v, &vec![1, 2, 3, 4]);
    /// unsafe { tup.uninit_assume_init_drop_one::<Vec<i32>, _>(); }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_mut_one<T, I>(&mut self) -> &mut T
    where
        Self: Search<MaybeUninit<T>, I>,
    {
        Search::get_mut(self).assume_init_mut()
    }

    /// Drop values in place for a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_drop()`](std::mem::MaybeUninit::assume_init_drop()).
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_drop(&mut self)
    where
        Self: Uninit,
    {
        Uninit::assume_init_drop(self)
    }

    /// Drop value in place for a specific [`MaybeUninit`](std::mem::MaybeUninit) element.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_drop()`](std::mem::MaybeUninit::assume_init_drop()).
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_drop_one<T, I>(&mut self)
    where
        Self: Search<MaybeUninit<T>, I>,
    {
        Search::get_mut(self).assume_init_drop()
    }

    /// Get points to values of a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
    /// let v = unsafe { &*get!(uninit.uninit_as_ptr(); 1) };
    /// assert_eq!(v.len(), 3);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_as_ptr(&self) -> <Self::Initialized as TupleLike>::AsPtrOutput
    where
        Self: Uninit,
    {
        Uninit::as_ptr(self)
    }

    /// Get mutable points to values of a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
    /// let v = unsafe { &mut *get!(uninit.uninit_as_mut_ptr(); 1) };
    /// v.push(4);
    /// assert_eq!(v.len(), 4);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_as_mut_ptr(&mut self) -> <Self::Initialized as TupleLike>::AsMutPtrOutput
    where
        Self: Uninit,
    {
        Uninit::as_mut_ptr(self)
    }

    /// Set value to a specific [`MaybeUninit`](std::mem::MaybeUninit) element in a tuple.
    ///
    /// **NOTE**: The type of this element must exist only once in the tuple.
    ///
    /// Similar to [`MaybeUninit::write()`](std::mem::MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(true);
    /// uninit.uninit_write_one("hello");
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    ///
    /// let mut tup = tuple!(
    ///     0,
    ///     MaybeUninit::<i32>::uninit(),
    ///     "hello",
    ///     MaybeUninit::<f64>::uninit(),
    ///     24
    /// );
    /// let x = unsafe { tup.uninit_write_one(12) };
    /// assert_eq!(x, &12);
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_write_one<T, I>(&mut self, value: T) -> &mut T
    where
        Self: Search<MaybeUninit<T>, I>,
    {
        Search::get_mut(self).write(value)
    }

    /// Set values to a tuple consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// Similar to [`MaybeUninit::write()`](std::mem::MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write(tuple!(12, true, "hello"));
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_write(
        &mut self,
        init: Self::Initialized,
    ) -> <Self::Initialized as TupleLike>::AsMutOutput<'_>
    where
        Self: Uninit,
    {
        Uninit::write(self, init)
    }

    /// Extract values of a specific subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init()`](MaybeUninit::assume_init()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let part_init = unsafe {
    ///     tup.uninit_assume_init_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(get!(part_init; 1), 0);
    /// assert_eq!(get!(part_init; 3), vec![1, 2, 3]);
    /// let _: tuple_t!(i32, i32, MaybeUninit<&str>, Vec<i32>, bool) = part_init;
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_subseq<Seq, I>(self) -> Self::PartiallyInitialized
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I> + Sized,
    {
        UninitSubseq::assume_init_subseq(self)
    }

    /// Read the values of a specific subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_read()`](MaybeUninit::assume_init_read()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited = unsafe {
    ///     tup.uninit_assume_init_read_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited, tuple!(0, vec![1, 2, 3]));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_read_subseq<Seq, I>(&self) -> Seq
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I>,
    {
        UninitSubseq::assume_init_read_subseq(self)
    }

    /// Get immutable references to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_ref()`](MaybeUninit::assume_init_ref()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ref = unsafe {
    ///     tup.uninit_assume_init_ref_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited_ref, tuple!(&0, &vec![1, 2, 3]));
    /// unsafe { tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_ref_subseq<Seq, I>(&self) -> <Seq as TupleLike>::AsRefOutput<'_>
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I>,
    {
        UninitSubseq::assume_init_ref_subseq(self)
    }

    /// Get mutable references to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_mut()`](MaybeUninit::assume_init_mut()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_mut = unsafe {
    ///     tup.uninit_assume_init_mut_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// *get!(inited_mut; 0) += 1;
    /// get!(inited_mut; 1).push(4);
    /// assert_eq!(inited_mut, tuple!(&mut 1, &mut vec![1, 2, 3, 4]));
    /// unsafe { tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_mut_subseq<Seq, I>(
        &mut self,
    ) -> <Seq as TupleLike>::AsMutOutput<'_>
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I>,
    {
        UninitSubseq::assume_init_mut_subseq(self)
    }

    /// Get pointers to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_subseq_as_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     assert_eq!(*get!(inited_ptr; 0), 0);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3]);
    ///     tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_subseq_as_ptr<Seq, I>(&self) -> <Seq as TupleLike>::AsPtrOutput
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I>,
    {
        UninitSubseq::subseq_as_ptr(self)
    }

    /// Get mutable pointers to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_subseq_as_mut_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     *get!(inited_ptr; 0) += 1;
    ///     (*get!(inited_ptr; 1)).push(4);
    ///     assert_eq!(*get!(inited_ptr; 0), 1);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3, 4]);
    ///     tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_subseq_as_mut_ptr<Seq, I>(&mut self) -> <Seq as TupleLike>::AsMutPtrOutput
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I>,
    {
        UninitSubseq::subseq_as_mut_ptr(self)
    }

    /// Set values to a subsequence consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Similar to [`MaybeUninit::write()`](std::mem::MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write_one(true);
    /// uninit.uninit_write_subseq(tuple!(12, "hello"));
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_write_subseq<Seq, I>(&mut self, subseq: Seq) -> Seq::AsMutOutput<'_>
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I>,
    {
        UninitSubseq::write_subseq(self, subseq)
    }

    /// Drop values in place for a subsequence consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_drop()`](std::mem::MaybeUninit::assume_init_drop()).
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_drop_subseq<Seq, I>(&mut self)
    where
        Seq: TupleLike,
        Self: UninitSubseq<Seq, I>,
    {
        UninitSubseq::assume_init_drop_subseq(self)
    }

    /// Extract values of a specific contiguous subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init()`](MaybeUninit::assume_init()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let part_init = unsafe {
    ///     tup.uninit_assume_init_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(get!(part_init; 2), 13);
    /// assert_eq!(get!(part_init; 3), vec![1, 2, 3]);
    /// let _: tuple_t!(i32, MaybeUninit<i32>, i32, Vec<i32>, bool) = part_init;
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_con_subseq<Seq, I>(self) -> Self::PartiallyInitialized
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I> + Sized,
    {
        UninitConSubseq::assume_init_con_subseq(self)
    }

    /// Read the values of a specific contiguous subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_read()`](MaybeUninit::assume_init_read()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited = unsafe {
    ///     tup.uninit_assume_init_read_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited, tuple!(13, vec![1, 2, 3]));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_read_con_subseq<Seq, I>(&self) -> Seq
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I>,
    {
        UninitConSubseq::assume_init_read_con_subseq(self)
    }

    /// Get immutable references to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_ref()`](MaybeUninit::assume_init_ref()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ref = unsafe {
    ///     tup.uninit_assume_init_ref_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited_ref, tuple!(&13, &vec![1, 2, 3]));
    /// unsafe { tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_ref_con_subseq<Seq, I>(
        &self,
    ) -> <Seq as TupleLike>::AsRefOutput<'_>
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I>,
    {
        UninitConSubseq::assume_init_ref_con_subseq(self)
    }

    /// Get mutable references to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_mut()`](MaybeUninit::assume_init_mut()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_mut = unsafe {
    ///     tup.uninit_assume_init_mut_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// *get!(inited_mut; 0) += 1;
    /// get!(inited_mut; 1).push(4);
    /// assert_eq!(inited_mut, tuple!(&mut 14, &mut vec![1, 2, 3, 4]));
    /// unsafe { tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_mut_con_subseq<Seq, I>(
        &mut self,
    ) -> <Seq as TupleLike>::AsMutOutput<'_>
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I>,
    {
        UninitConSubseq::assume_init_mut_con_subseq(self)
    }
    /// Get pointers to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_con_subseq_as_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     assert_eq!(*get!(inited_ptr; 0), 13);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3]);
    ///     tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_con_subseq_as_ptr<Seq, I>(&self) -> <Seq as TupleLike>::AsPtrOutput
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I>,
    {
        UninitConSubseq::con_subseq_as_ptr(self)
    }

    /// Get mutable pointers to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_con_subseq_as_mut_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     *get!(inited_ptr; 0) += 1;
    ///     (*get!(inited_ptr; 1)).push(4);
    ///     assert_eq!(*get!(inited_ptr; 0), 14);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3, 4]);
    ///     tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_con_subseq_as_mut_ptr<Seq, I>(&mut self) -> <Seq as TupleLike>::AsMutPtrOutput
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I>,
    {
        UninitConSubseq::con_subseq_as_mut_ptr(self)
    }

    /// Set values to a contiguous subsequence consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// Similar to [`MaybeUninit::write()`](std::mem::MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write_one(true);
    /// uninit.uninit_write_subseq(tuple!(12, "hello"));
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    fn uninit_write_con_subseq<Seq, I>(&mut self, subseq: Seq) -> Seq::AsMutOutput<'_>
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I>,
    {
        UninitConSubseq::write_con_subseq(self, subseq)
    }

    /// Drop values in place for a contiguous subsequence consisting of [`MaybeUninit`](std::mem::MaybeUninit) elements.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_drop()`](std::mem::MaybeUninit::assume_init_drop()).
    #[cfg(feature = "uninit")]
    #[cfg_attr(docsrs, doc(cfg(feature = "uninit")))]
    unsafe fn uninit_assume_init_drop_con_subseq<Seq, I>(&mut self)
    where
        Seq: TupleLike,
        Self: UninitConSubseq<Seq, I>,
    {
        UninitConSubseq::assume_init_drop_con_subseq(self)
    }

    /// Untuple a tuple, whose elements are all tuples.
    ///
    /// See [`to_tuple()`](TupleLike::to_tuple()) for the opposite operation.
    ///
    /// Also called [`flatten()`](TupleLike::flatten()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup_tup = tuple!(tuple!(1, "hello"), tuple!(), tuple!(3.14));
    /// assert_eq!(tup_tup.untuple(), tuple!(1, "hello", 3.14));
    /// ```
    fn untuple(self) -> Self::UntupleOutput
    where
        Self: Untupleable + Sized,
    {
        Untupleable::untuple(self)
    }

    /// Flatten one level of nesting in the tuple.
    ///
    /// Also called [`untuple()`](TupleLike::untuple()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup_tup = tuple!(tuple!(1, "hello"), tuple!(), tuple!(3.14));
    /// assert_eq!(tup_tup.flatten(), tuple!(1, "hello", 3.14));
    /// ```
    fn flatten(self) -> Self::UntupleOutput
    where
        Self: Untupleable + Sized,
    {
        Untupleable::untuple(self)
    }

    /// Traverse the tuple, and collect the output of traversal into a new tuple.
    ///
    /// Check out [`Mapper`](crate::foreach::Mapper)'s documentation page to learn how to build
    /// a mapper that can be passed to [`foreach()`](TupleLike::foreach()).
    ///
    /// NOTE: Traverse a tuple will consume it. If this is not what you want, call [`as_ref()`](TupleLike::as_ref())
    /// or [`as_mut()`](TupleLike::as_mut()) to create a new tuple that references its all members before traversing.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{mapper, tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14).foreach(mapper! {
    ///     |x: i32| -> i64 { x as i64 }
    ///     |x: f32| -> String { x.to_string() }
    ///     <'a> |x: &'a str| -> &'a [u8] { x.as_bytes() }
    /// });
    /// assert_eq!(tup, tuple!(1i64, b"hello" as &[u8], "3.14".to_string()));
    /// ```
    fn foreach<F>(self, mapper: F) -> <Self as Foreach<F>>::Output
    where
        Self: Foreach<F> + Sized,
    {
        Foreach::foreach(self, mapper)
    }

    /// Fold the tuple.
    ///
    /// Check out [`Folder`](crate::fold::Folder)'s documentation page to learn how to build
    /// a folder that can be passed to [`foreach()`](TupleLike::foreach()).
    ///
    /// NOTE: Fold a tuple will consume it. If this is not what you want, call [`as_ref()`](TupleLike::as_ref())
    /// or [`as_mut()`](TupleLike::as_mut()) to create a new tuple that references its all members before folding.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{folder, tuple, TupleLike};
    ///
    /// let tup = tuple!(Some(1), "2", Some(3.0));
    /// let result = tup.fold(
    ///     folder! { String; // Type of `acc` of all closures must be the same and annotated at the front
    ///         |acc, x: &str| { acc + &x.to_string() }
    ///         <T: ToString> |acc, x: Option<T>| { acc + &x.unwrap().to_string() }
    ///     },
    ///     String::new(),
    /// );
    /// assert_eq!(result, "123".to_string());
    /// ```
    fn fold<F, Acc>(self, folder: F, acc: Acc) -> <Self as Foldable<F, Acc>>::Output
    where
        Self: Foldable<F, Acc> + Sized,
    {
        Foldable::fold(self, folder, acc)
    }

    /// Tests if any element of the tuple matches a predicate.
    ///
    /// Check out [`UnaryPredicate`]'s documentation page to learn how to build
    /// a unary predicate that can be passed to [`any()`](TupleLike::any()).
    ///
    /// [`any()`](TupleLike::any()) is short-circuiting; in other words, it will stop processing as soon as it finds a `true`,
    /// given that no matter what else happens, the result will also be `true`.
    ///
    /// An empty tuple returns `false`.
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
    fn any<Pred>(&self, predicate: Pred) -> bool
    where
        Self: TestAny<Pred>,
    {
        TestAny::any(self, predicate)
    }

    /// Tests if every element of the tuple matches a predicate.
    ///
    /// Check out [`UnaryPredicate`]'s documentation page to learn how to build
    /// a unary predicate that can be passed to [`all()`](TupleLike::all()).
    ///
    /// [`all()`](TupleLike::all()) is short-circuiting; in other words, it will stop processing as soon as it finds a `false`,
    /// given that no matter what else happens, the result will also be `false`.
    ///
    /// An empty tuple returns `true`.
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
    fn all<Pred>(&self, predicate: Pred) -> bool
    where
        Self: TestAll<Pred>,
    {
        TestAll::all(self, predicate)
    }

    /// Performs dot product operation.
    ///
    /// Note: it evaluates starting from the last element.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    /// assert_eq!(tuple!(1, 3, -5).dot(tuple!(4, -2, -1)), 3);
    /// ```
    fn dot<T>(self, rhs: T) -> <Self as Dot<T>>::Output
    where
        Self: Dot<T> + Sized,
    {
        Dot::dot(self, rhs)
    }

    /// Zip two tuples.
    ///
    /// See [`unzip()`](TupleLike::unzip()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, 2.0, "3").zip(tuple!("4", 5, 6.0));
    /// assert_eq!(tup, tuple!(tuple!(1, "4"), tuple!(2.0, 5), tuple!("3", 6.0)));
    /// ```
    fn zip<T>(self, rhs: T) -> Self::ZipOutput
    where
        Self: Zippable<T> + Sized,
    {
        Zippable::zip(self, rhs)
    }

    /// Zip two tuples, but output elements are primitive tuples.
    ///
    /// See [`unzip()`](TupleLike::unzip()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, 2.0, "3").zip2(tuple!("4", 5, 6.0));
    /// assert_eq!(tup, tuple!((1, "4"), (2.0, 5), ("3", 6.0)));
    /// ```
    fn zip2<T>(self, rhs: T) -> Self::ZipOutput2
    where
        Self: Zippable<T> + Sized,
    {
        Zippable::zip2(self, rhs)
    }

    /// Unzip a tuple to two tuples, if all elements of the tuple are tuples with two elements.
    /// Elements can be of [`Tuple`] type or primitive tuple type.
    ///
    /// See [`zip()`](TupleLike::zip()) and [`zip2()`](TupleLike::zip2()) for the opposite operation.
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(
    ///     tuple!(1, "hello"), // A `Tuple`
    ///     ("world", 2.0),     // A primitive tuple
    /// );
    /// let (l, r) = tup.unzip();
    /// assert_eq!(l, tuple!(1, "world"));
    /// assert_eq!(r, tuple!("hello", 2.0));
    /// ```
    fn unzip(self) -> (Self::UnzipOutputLeft, Self::UnzipOutputRight)
    where
        Self: Unzippable + Sized,
    {
        Unzippable::unzip(self)
    }

    /// If the elements of a tuple are all tuples, push an element to the back of each tuple element.
    ///
    /// See [`shrink()`](TupleLike::shrink()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(tuple!(1, "hello"), tuple!(), tuple!(3.14));
    /// let ext = tuple!(9.0, "8", 7);
    /// assert_eq!(
    ///     tup.extend(ext),
    ///     tuple!(tuple!(1, "hello", 9.0), tuple!("8"), tuple!(3.14, 7))
    /// );
    /// ```
    fn extend<T>(self, rhs: T) -> Self::ExtendBackOutput
    where
        Self: Extendable<T> + Sized,
    {
        Extendable::extend(self, rhs)
    }

    /// If the elements of a tuple are all tuples, push an element to the front of each tuple element.
    ///
    /// See [`shrink_front()`](TupleLike::shrink_front()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(tuple!(1, "hello"), tuple!(), tuple!(3.14));
    /// let ext = tuple!(9.0, "8", 7);
    /// assert_eq!(
    ///     tup.extend_front(ext),
    ///     tuple!(tuple!(9.0, 1, "hello"), tuple!("8"), tuple!(7, 3.14))
    /// );
    /// ```
    fn extend_front<T>(self, rhs: T) -> Self::ExtendFrontOutput
    where
        Self: Extendable<T> + Sized,
    {
        Extendable::extend_front(self, rhs)
    }

    /// If the elements of a tuple are all tuples, push an element to the front of each tuple element.
    /// Same as [`extend()`](TupleLike::extend()).
    fn extend_back<T>(self, rhs: T) -> Self::ExtendBackOutput
    where
        Self: Extendable<T> + Sized,
    {
        Extendable::extend_back(self, rhs)
    }

    /// If the elements of a tuple are all tuples, pop an element from the back of each tuple element.
    ///
    /// See [`extend()`](TupleLike::extend()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(tuple!(9.0, 1, "hello"), tuple!("8"), tuple!(7, 3.14));
    /// let (result, popped) = tup.shrink();
    /// assert_eq!(result, tuple!(tuple!(9.0, 1), tuple!(), tuple!(7)));
    /// assert_eq!(popped, tuple!("hello", "8", 3.14));
    /// ```
    fn shrink(self) -> (Self::ShrinkBackOutput, Self::ShrinkBackElements)
    where
        Self: Shrinkable + Sized,
    {
        Shrinkable::shrink(self)
    }

    /// If the elements of a tuple are all tuples, pop an element from the front of each tuple element.
    ///
    /// See [`extend_front()`](TupleLike::extend_front()) for the opposite operation.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(tuple!(9.0, 1, "hello"), tuple!("8"), tuple!(7, 3.14));
    /// let (result, popped) = tup.shrink_front();
    /// assert_eq!(result, tuple!(tuple!(1, "hello"), tuple!(), tuple!(3.14)));
    /// assert_eq!(popped, tuple!(9.0, "8", 7));
    /// ```
    fn shrink_front(self) -> (Self::ShrinkFrontOutput, Self::ShrinkFrontElements)
    where
        Self: Shrinkable + Sized,
    {
        Shrinkable::shrink_front(self)
    }

    /// If the elements of a tuple are all tuples, pop an element from the back of each tuple element.
    /// Same as [`shrink()`](TupleLike::shrink()).
    fn shrink_back(self) -> (Self::ShrinkBackOutput, Self::ShrinkBackElements)
    where
        Self: Shrinkable + Sized,
    {
        Shrinkable::shrink_back(self)
    }

    /// If two tuples have the same number of elements, and their elements are both tuples,
    /// join their tuple elements one-to-one.
    ///
    /// NOTE: This method is not [`join()`](TupleLike::join()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(tuple!(1), tuple!(), tuple!("hello", 3.14));
    /// let tup2 = tuple!(tuple!(), tuple!(9, "8"), tuple!(7.0));
    /// let tup3 = tup.combine(tup2);
    /// assert_eq!(tup3, tuple!(tuple!(1), tuple!(9, "8"), tuple!("hello", 3.14, 7.0)));
    /// ```
    fn combine<T>(self, rhs: T) -> Self::CombineOutput
    where
        Self: Combinable<T> + Sized,
    {
        Combinable::combine(self, rhs)
    }

    /// Replace the first N elements of the tuple with all elements of another tuple of N elements.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "2", 3.0, Some(4));
    /// let tup2 = tuple!("z", 8);
    /// let (output, replaced) = tup.replace_head(tup2);
    /// assert_eq!(output, tuple!("z", 8, 3.0, Some(4)));
    /// assert_eq!(replaced, tuple!(1, "2"));
    /// ```
    fn replace_head<T>(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced)
    where
        T: TupleLike,
        Self: HeadReplaceable<T> + Sized,
    {
        HeadReplaceable::replace_head(self, rhs)
    }

    /// Replace the last N elements of the tuple with all elements of another tuple of N elements.
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
    fn replace_tail<T, I>(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced)
    where
        T: TupleLike,
        Self: TailReplaceable<T, I> + Sized,
    {
        TailReplaceable::replace_tail(self, rhs)
    }

    /// When all elements of the tuple implement [`Fn(T)`](std::ops::Fn) for a specific `T`,
    /// call them once in sequence.
    ///
    /// # Example
    ///
    /// It is required that `T` implements [`Clone`].
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// fn add1(x: i32) -> i32 {
    ///     x + 1
    /// }
    /// fn add2(x: i32) -> i32 {
    ///     x + 2
    /// }
    /// fn to_string(x: i32) -> String {
    ///     x.to_string()
    /// }
    ///
    /// let tup = tuple!(add1, add2, to_string).call(1);
    /// assert_eq!(tup, tuple!(2, 3, "1".to_string()));
    /// ```
    ///
    /// ...however, due to the existence of reborrowing, we can use some tricks to allow
    /// the mutable references to be used as parameters multiple times.
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// fn add1(x: &mut i32) {
    ///     *x += 1
    /// }
    /// fn add2(x: &mut i32) {
    ///     *x += 2
    /// }
    /// fn to_string(x: &mut i32) -> String {
    ///     x.to_string()
    /// }
    ///
    /// let mut x = 1;
    /// let tup = tuple!(add1, add2, to_string).call(&mut x);
    /// assert_eq!(x, 4);
    /// assert_eq!(tup, tuple!((), (), "4".to_string()));
    /// ```
    fn call<T, P>(&self, rhs: T) -> <Self as Callable<T, P>>::Output
    where
        Self: Callable<T, P>,
    {
        Callable::call(self, rhs)
    }

    /// When all elements of the tuple implement [`FnMut(T)`](std::ops::FnMut) for a specific `T`,
    /// call them once in sequence.
    ///
    /// Basically the same as [`call()`](TupleLike::call()), but elements are required to implement
    /// [`FnMut(T)`](std::ops::FnMut) instead of [`Fn(T)`](std::ops::Fn).
    fn call_mut<T, P>(&mut self, rhs: T) -> <Self as MutCallable<T, P>>::Output
    where
        Self: MutCallable<T, P>,
    {
        MutCallable::call_mut(self, rhs)
    }

    /// When all elements of the tuple implement [`FnOnce(T)`](std::ops::FnOnce) for a specific `T`,
    /// call them once in sequence.
    ///
    /// Basically the same as [`call()`](TupleLike::call()), but elements are required to implement
    /// [`FnOnce(T)`](std::ops::FnOnce) instead of [`Fn(T)`](std::ops::Fn).
    fn call_once<T, P>(self, rhs: T) -> <Self as OnceCallable<T, P>>::Output
    where
        Self: OnceCallable<T, P> + Sized,
    {
        OnceCallable::call_once(self, rhs)
    }

    /// Convert from `Tuple<Wrapper0<T0>, Wrapper1<T1>, ... Wrappern<Tn>>` to `Tuple<T0, T1, ..., Tn>`,
    /// when all element types `Wrapper0`, `Wrapper1` ... `Wrappern` implement [`Unwrap`].
    ///
    /// Because this function may panic, its use is generally discouraged. Instead,
    /// use [`unwrap_or_default()`](TupleLike::unwrap_or_default()) or
    /// [`try_unwrap()`](TupleLike::try_unwrap()).
    ///
    /// # Panic
    ///
    /// Panic if any element does not contain a value.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(Some(1), Ok::<f32, ()>(3.14), Some("hello"));
    /// assert_eq!(tup.unwrap(), tuple!(1, 3.14, "hello"));
    /// ```
    #[cfg(feature = "unwrap")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unwrap")))]
    fn unwrap(self) -> Self::UnwrapOutput
    where
        Self: Unwrap + Sized,
    {
        Unwrap::unwrap(self)
    }

    /// Check if self can be safely [`unwrap()`](TupleLike::unwrap()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// assert_eq!(tuple!(Some(1), Some(3.14), Ok::<&str, ()>("hello")).has_value(), true);
    /// assert_eq!(tuple!(None::<i32>, Some(3.14), Err::<&str, ()>(())).has_value(), false);
    /// ```
    #[cfg(feature = "unwrap")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unwrap")))]
    fn has_value(&self) -> bool
    where
        Self: Unwrap,
    {
        Unwrap::has_value(self)
    }

    /// Convert from `Tuple<Wrapper0<T0>, Wrapper1<T1>, ... Wrappern<Tn>>` to `Tuple<T0, T1, ..., Tn>`,
    /// when all element types `Wrapper0`, `Wrapper1` ... `Wrappern` implement [`UnwrapOrDefault`].
    ///
    /// Unlike [`unwrap()`](TupleLike::unwrap()), if an element does not contain a value, use the
    /// default value instead of panic.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(Some(1), Err::<f32, &str>("failed"), Some("hello"));
    /// assert_eq!(tup.unwrap_or_default(), tuple!(1, 0.0, "hello"));
    /// ```
    #[cfg(feature = "unwrap")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unwrap")))]
    fn unwrap_or_default(self) -> Self::UnwrapOutput
    where
        Self: UnwrapOrDefault + Sized,
    {
        UnwrapOrDefault::unwrap_or_default(self)
    }

    /// Convert from `Tuple<Wrapper0<T0>, Wrapper1<T1>, ... Wrappern<Tn>>` to `Option<Tuple<T0, T1, ..., Tn>>`,
    /// when all element types `Wrapper0`, `Wrapper1` ... `Wrappern` implement [`Unwrap`].
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(Some(1), Ok::<f32, ()>(3.14));
    /// assert_eq!(tup.try_unwrap(), Some(tuple!(1, 3.14)));
    /// let tup2 = tuple!(Some("hello"), Err::<i32, &str>("failed"));
    /// assert_eq!(tup2.try_unwrap(), None);
    /// ```
    #[cfg(feature = "unwrap")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unwrap")))]
    fn try_unwrap(self) -> Option<Self::UnwrapOutput>
    where
        Self: Unwrap + Sized,
    {
        if Unwrap::has_value(&self) {
            Some(Unwrap::unwrap(self))
        } else {
            None
        }
    }
}

impl TupleLike for Unit {
    type AsRefOutput<'a> = Unit;
    type AsMutOutput<'a> = Unit;
    type AsPtrOutput = Unit;
    type AsMutPtrOutput = Unit;
    type AsPinRefOutput<'a> = Unit;
    type AsPinMutOutput<'a> = Unit;
    type PushFrontOutput<T> = Tuple<T, Unit>;
    type PushBackOutput<T> = Tuple<T, Unit>;
    type RevOutput = Unit;
    type JoinOutput<T>
        = T
    where
        T: TupleLike;
    type ToSomeOutput = Unit;
    type ToOkOutput<E> = Unit;
    type ToTupleOutput = Unit;
    #[cfg(feature = "uninit")]
    type Uninit = Unit;

    const LEN: usize = 0;

    fn as_ref(&self) -> Self::AsRefOutput<'_> {
        Self
    }

    fn as_mut(&mut self) -> Self::AsMutOutput<'_> {
        Self
    }

    fn as_ptr(&self) -> Self::AsPtrOutput {
        Unit
    }

    fn as_mut_ptr(&mut self) -> Self::AsMutPtrOutput {
        Unit
    }

    fn as_pin_ref(self: Pin<&Self>) -> Self::AsPinRefOutput<'_> {
        Unit
    }

    fn as_pin_mut(self: Pin<&mut Self>) -> Self::AsPinMutOutput<'_> {
        Unit
    }

    fn push<T>(self, value: T) -> Self::PushBackOutput<T> {
        Tuple(value, self)
    }

    fn push_front<T>(self, value: T) -> Self::PushFrontOutput<T> {
        Tuple(value, self)
    }

    fn push_back<T>(self, value: T) -> Self::PushBackOutput<T> {
        Tuple(value, self)
    }

    fn rev(self) -> Self::RevOutput {
        self
    }

    fn join<T>(self, value: T) -> Self::JoinOutput<T>
    where
        T: TupleLike,
    {
        value
    }

    fn to_some(self) -> Self::ToSomeOutput {
        self
    }

    fn to_ok<E>(self) -> Self::ToOkOutput<E> {
        self
    }

    fn to_tuple(self) -> Self::ToTupleOutput {
        self
    }

    #[cfg(feature = "uninit")]
    fn uninit() -> Self::Uninit {
        Unit
    }

    #[cfg(feature = "uninit")]
    fn zeroed() -> Self::Uninit {
        Unit
    }

    #[cfg(feature = "uninit")]
    fn to_uninit(self) -> Self::Uninit {
        Unit
    }
}

impl<First, Other> TupleLike for Tuple<First, Other>
where
    Other: TupleLike,
{
    type AsRefOutput<'a>
        = Tuple<&'a First, Other::AsRefOutput<'a>>
    where
        Self: 'a;
    type AsMutOutput<'a>
        = Tuple<&'a mut First, Other::AsMutOutput<'a>>
    where
        Self: 'a;
    type AsPtrOutput = Tuple<*const First, Other::AsPtrOutput>;
    type AsMutPtrOutput = Tuple<*mut First, Other::AsMutPtrOutput>;
    type AsPinRefOutput<'a>
        = Tuple<Pin<&'a First>, Other::AsPinRefOutput<'a>>
    where
        Self: 'a;
    type AsPinMutOutput<'a>
        = Tuple<Pin<&'a mut First>, Other::AsPinMutOutput<'a>>
    where
        Self: 'a;
    type PushFrontOutput<T> = Tuple<T, Self>;
    type PushBackOutput<T> = Tuple<First, Other::PushBackOutput<T>>;
    type RevOutput = <Other::RevOutput as TupleLike>::PushBackOutput<First>;
    type JoinOutput<T>
        = Tuple<First, Other::JoinOutput<T>>
    where
        T: TupleLike;
    type ToSomeOutput = Tuple<Option<First>, Other::ToSomeOutput>;
    type ToOkOutput<E> = Tuple<Result<First, E>, Other::ToOkOutput<E>>;
    type ToTupleOutput = Tuple<Tuple<First, Unit>, Other::ToTupleOutput>;
    #[cfg(feature = "uninit")]
    type Uninit = Tuple<MaybeUninit<First>, Other::Uninit>;

    const LEN: usize = Other::LEN + 1;

    fn as_ref(&self) -> Self::AsRefOutput<'_> {
        Tuple(&self.0, self.1.as_ref())
    }

    fn as_mut(&mut self) -> Self::AsMutOutput<'_> {
        Tuple(&mut self.0, self.1.as_mut())
    }

    fn as_ptr(&self) -> Self::AsPtrOutput {
        Tuple(&self.0, self.1.as_ptr())
    }

    fn as_mut_ptr(&mut self) -> Self::AsMutPtrOutput {
        Tuple(&mut self.0, self.1.as_mut_ptr())
    }

    fn as_pin_ref(self: Pin<&Self>) -> Self::AsPinRefOutput<'_> {
        let this = Pin::get_ref(self);
        unsafe {
            Tuple(
                Pin::new_unchecked(&this.0),
                Pin::new_unchecked(&this.1).as_pin_ref(),
            )
        }
    }

    fn as_pin_mut(self: Pin<&mut Self>) -> Self::AsPinMutOutput<'_> {
        unsafe {
            let this = Pin::get_unchecked_mut(self);
            Tuple(
                Pin::new_unchecked(&mut this.0),
                Pin::new_unchecked(&mut this.1).as_pin_mut(),
            )
        }
    }

    fn push<T>(self, value: T) -> Self::PushBackOutput<T> {
        Tuple(self.0, self.1.push(value))
    }

    fn push_front<T>(self, value: T) -> Self::PushFrontOutput<T> {
        Tuple(value, self)
    }

    fn push_back<T>(self, value: T) -> Self::PushBackOutput<T> {
        self.push::<T>(value)
    }

    fn rev(self) -> Self::RevOutput {
        self.1.rev().push(self.0)
    }

    fn join<T>(self, value: T) -> Self::JoinOutput<T>
    where
        T: TupleLike,
    {
        Tuple(self.0, self.1.join(value))
    }

    fn to_some(self) -> Self::ToSomeOutput {
        Tuple(Some(self.0), self.1.to_some())
    }

    fn to_ok<E>(self) -> Self::ToOkOutput<E> {
        Tuple(Ok(self.0), self.1.to_ok())
    }

    fn to_tuple(self) -> Self::ToTupleOutput {
        Tuple(Tuple(self.0, Unit), self.1.to_tuple())
    }

    #[cfg(feature = "uninit")]
    fn uninit() -> Self::Uninit {
        Tuple(MaybeUninit::uninit(), Other::uninit())
    }

    #[cfg(feature = "uninit")]
    fn zeroed() -> Self::Uninit {
        Tuple(MaybeUninit::zeroed(), Other::zeroed())
    }

    #[cfg(feature = "uninit")]
    fn to_uninit(self) -> Self::Uninit {
        Tuple(MaybeUninit::new(self.0), TupleLike::to_uninit(self.1))
    }
}

/// A Marker trait to indicate that two tuple types have the same number of elements.
///
/// **FIXME**: Once the [`generic_const_exprs` feature](https://github.com/rust-lang/rust/issues/76560)
/// and the [`associated_const_equality` feature](https://github.com/rust-lang/rust/issues/92827) are
/// stabilized, this trait is no longer needed. Instead, we can write:
///
/// ```ignore
/// use tuplez::TupleLike;
///
/// fn use_tuple<T, U>(t: T, u: U)
/// where
///     T: TupleLike,
///     U: TupleLike<LEN = { T::LEN }>,
/// {
///     // ...
/// }
/// ```
///
/// # Example
///
/// Use with [`tuple_t!`](crate::tuple_t!) macro to constrain the number of elements of the tuple.
///
/// ```
/// use tuplez::{tuple, tuple_t, TupleLenEqTo, TupleLike};
///
/// fn only_accept_5_elements<T>(_: T)
/// where
///     T: TupleLenEqTo<tuple_t!((); 5)>
/// {
/// }
///
/// let tup4 = tuple!(1, 2.0, "3", 4);
/// // only_accept_5_elements(tup4);    // Error: the trait bound is not satisfied
/// let tup5 = tup4.push_back('5');
/// only_accept_5_elements(tup5);       // Ok
/// let tup6 = tup5.push_back(6.0);
/// // only_accept_5_elements(tup6);    // Error: the trait bound is not satisfied
/// ```
pub trait TupleLenEqTo<T: TupleLike>: TupleLike {}

impl TupleLenEqTo<Unit> for Unit {}

impl<First1, Other1, First2, Other2> TupleLenEqTo<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    Other1: TupleLenEqTo<Other2>,
    Other2: TupleLike,
{
}

/// Convert from tuples to [primitive tuples](https://doc.rust-lang.org/std/primitive.tuple.html).
///
/// Note that due to the limitation that Rust cannot represent primitive tuple types containing any number of elements,
/// the trait [`ToPrimitive`] is only implemented for tuples with no more than 32 elements.
pub trait ToPrimitive {
    /// The primitive tuple type containing the same number and order of elements.
    type Primitive;

    /// Convert from the tuple to the primitive tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::{ToPrimitive, tuple};
    ///
    /// let tup = tuple!(1, "2", 3.0, 4);
    /// let prim = tup.primitive();
    /// assert_eq!(prim, (1, "2", 3.0, 4));
    /// ```
    fn primitive(self) -> Self::Primitive;
}

/// Convert from tuples to [primitive arrays](std::array), if all elements of the tuple are of the same type.
///
/// Because the [generic constant expressions](https://github.com/rust-lang/rust/issues/76560) feature is still unstable yet,
/// we can only limit the maximum number of elements of the tuple that implement [`ToArray`] to 32,
/// just like what we did with the primitive tuples.
///
/// However, if you are OK with using rustc released to nightly channel to compile codes with unstable features,
/// you can enable the `any_array` feature to implement [`ToArray`] on tuples with no limit on the number of elements.
///
/// ```toml
/// tuplez = { features = [ "any_array" ] }
/// ```
///
/// Always remember: unstable features are not guaranteed by Rust and may not be available someday in the future.
///
/// Why `<T>` instead of `type Item`? Well, this is because the [`Unit`]s can be converted to any `[T; 0]`.
pub trait ToArray<T>: TupleLike {
    /// The primitive array type to generate.
    type Array: IntoIterator<Item = T>;

    /// Immutable element iterator type.
    type Iter<'a>: Iterator<Item = &'a T>
    where
        Self::AsRefOutput<'a>: ToArray<&'a T>,
        Self: 'a,
        T: 'a;

    /// Mutable element iterator type.
    type IterMut<'a>: Iterator<Item = &'a mut T>
    where
        Self::AsMutOutput<'a>: ToArray<&'a mut T>,
        Self: 'a,
        T: 'a;

    /// Convert from the tuple to the primitive array.
    ///
    /// # Example
    ///
    /// ```
    /// # #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
    /// #
    /// use tuplez::{tuple, ToArray};
    ///
    /// let tup = tuple!(1, 2, 3, 4, 5, 6);
    /// assert_eq!(tup.to_array(), [1, 2, 3, 4, 5, 6]);
    /// ```
    fn to_array(self) -> Self::Array;

    /// Get immutable element iterator.
    ///
    /// # Example
    ///
    /// ```
    /// # #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
    /// #
    /// use tuplez::{tuple, ToArray};
    ///
    /// let tup = tuple!(1, 2, 3, 4, 5, 6);
    /// assert_eq!(tup.iter().sum::<i32>(), 21);
    /// ```
    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::AsRefOutput<'a>: ToArray<&'a T>,
        Self: 'a,
        T: 'a;

    /// Get mutable element iterator.
    ///
    /// # Example
    ///
    /// ```
    /// # #![cfg_attr(feature = "any_array", feature(generic_const_exprs))]
    /// #
    /// use tuplez::{tuple, ToArray};
    ///
    /// let mut tup = tuple!(1, 2, 3, 4, 5, 6);
    /// tup.iter_mut().for_each(|v| *v += 1);
    /// assert_eq!(tup.iter().sum::<i32>(), 27);
    /// ```
    fn iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self::AsMutOutput<'a>: ToArray<&'a mut T>,
        Self: 'a,
        T: 'a;
}

tuple_traits_impl!(32);

__tuple_unary_ops_impl! {
    Neg::neg(),
    Not::not(),
}

__tuple_binary_ops_impl! {
    Add::add(),
    Sub::sub(),
    Mul::mul(),
    Div::div(),
    Rem::rem(),
    BitAnd::bitand(),
    BitOr::bitor(),
    BitXor::bitxor(),
    Shl::shl(),
    Shr::shr(),
}

__tuple_assignment_ops_impl! {
    AddAssign::add_assign(),
    SubAssign::sub_assign(),
    MulAssign::mul_assign(),
    DivAssign::div_assign(),
    RemAssign::rem_assign(),
    BitAndAssign::bitand_assign(),
    BitOrAssign::bitor_assign(),
    BitXorAssign::bitxor_assign(),
    ShlAssign::shl_assign(),
    ShrAssign::shr_assign(),
}

impl<T, Other> IntoIterator for Tuple<T, Other>
where
    Tuple<T, Other>: ToArray<T>,
{
    type Item = T;
    type IntoIter = <<Self as ToArray<T>>::Array as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.to_array().into_iter()
    }
}

impl<'a, T, Other> IntoIterator for &'a Tuple<T, Other>
where
    Tuple<T, Other>: TupleLike,
    <Tuple<T, Other> as TupleLike>::AsRefOutput<'a>: ToArray<&'a T>,
{
    type Item = &'a T;
    type IntoIter = <<<Tuple<T, Other> as TupleLike>::AsRefOutput<'a> as ToArray<&'a T>>::Array as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.as_ref().to_array().into_iter()
    }
}

impl<'a, T, Other> IntoIterator for &'a mut Tuple<T, Other>
where
    Tuple<T, Other>: TupleLike,
    <Tuple<T, Other> as TupleLike>::AsMutOutput<'a>: ToArray<&'a mut T>,
{
    type Item = &'a mut T;
    type IntoIter = <<<Tuple<T, Other> as TupleLike>::AsMutOutput<'a> as ToArray<&'a mut T>>::Array as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut().to_array().into_iter()
    }
}
