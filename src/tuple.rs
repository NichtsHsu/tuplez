#[cfg(feature = "unwrap")]
use crate::unwrap::*;
use crate::{
    fold::Foldable, foreach::Foreach, macros::__tuple_traits_impl, ops::*, predicate::*, search::*,
};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

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
/// When you try to implement your own traits on [`Tuple`]s, remember the key idea - recursion.
/// You bound `Other` with the same trait, and implement that trait for [`Unit`] as the termination of recursion.
///
/// This is an example of generating Fibonacci numbers based on [`Tuple`]s:
///
/// ```
/// use tuplez::{tuple, Tuple, TupleLike, Unit};
///
/// trait Fibonacci {
///     const CURRENT: usize;
///     const NEXT: usize;
///
///     fn fib(&self) -> Vec<usize>;
/// }
///
/// impl Fibonacci for Unit {
///     const CURRENT: usize = 0;
///     const NEXT: usize = 1;
///
///     fn fib(&self) -> Vec<usize> {
///         vec![]
///     }
/// }
///
/// impl<First, Other> Fibonacci for Tuple<First, Other>
/// where
///     Other: TupleLike + Fibonacci,
/// {
///     const CURRENT: usize = Other::NEXT;
///     const NEXT: usize = Other::CURRENT + Other::NEXT;
///
///     fn fib(&self) -> Vec<usize> {
///         let mut v = self.1.fib();
///         v.push(Self::CURRENT);
///         v
///     }
/// }
///
/// assert_eq!(tuple!((); 10).fib(), vec![1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
/// ```
///
/// If you're looking for more complex examples, then the [source code of tuplez](https://github.com/NichtsHsu/tuplez)
/// is a good place to start.
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
/// Currently we can't convert tuple from/to primitive arrays with no limit on the number of elements,
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

    /// Take out the searched element, and get the remainder of tuple.
    ///
    /// Add a type annotation to the searched element to let [`take()`](TupleLike::take()) know which one you want.
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
    fn take<T, R>(self) -> (T, Self::TakeRemainder)
    where
        Self: Search<T, R> + Sized,
    {
        Search::take(self)
    }

    /// Get an immutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`get_ref()`](TupleLike::get_ref()) know which one you want.
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
    fn get_ref<T, R>(&self) -> &T
    where
        Self: Search<T, R> + Sized,
    {
        Search::get_ref(self)
    }

    /// Get a mutable reference of the searched element.
    ///
    /// Add a type annotation to the searched element to let [`get_mut()`](TupleLike::get_mut()) know which one you want.
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
    fn get_mut<T, R>(&mut self) -> &mut T
    where
        Self: Search<T, R> + Sized,
    {
        Search::get_mut(self)
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

    /// Convert a `tuple!(a, b, c ...)` to `tuple!(Some(a), Some(b), Some(c) ...)`.
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

    /// Convert a `tuple!(a, b, c ...)` to `tuple!(Ok(a), Ok(b), Ok(c) ...)`.
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

    /// Convert a `tuple!(a, b, c ...)` to `tuple!(tuple!(a), tuple!(b), tuple!(c) ...)`.
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
    fn replace_tail<T, R>(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced)
    where
        T: TupleLike,
        Self: TailReplaceable<T, R> + Sized,
    {
        TailReplaceable::replace_tail(self, rhs)
    }

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
    /// then what you are looking for might be [`swap_with()`](TupleLike::swap_with()).
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
    fn replace_with<T, R>(&mut self, rhs: T) -> T
    where
        T: TupleLike,
        Self: ReplaceWith<T, R>,
    {
        ReplaceWith::replace_with(self, rhs)
    }

    /// Swap a sequence of elements in the tuple with all elements of another tuple.
    ///
    /// The tuple will search for a sequence of elements whose types are exactly the same as
    /// the sequence of all the elements of the provided tuple, and then swaps the elements
    /// of this sequence with the elements of the provided tuple.
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
    fn swap_with<T, R>(&mut self, rhs: &mut T)
    where
        T: TupleLike,
        Self: ReplaceWith<T, R>,
    {
        ReplaceWith::swap_with(self, rhs)
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

    /// Convert `Tuple<Wrapper0<T0>, Wrapper1<T1>, ... Wrappern<Tn>>` to `Tuple<T0, T1, ..., Tn>`,
    /// when all element types `Wrapper0`, `Wrapper1` ... `Wrappern` implement [`Unwrap`].
    ///
    /// Only available if the `unwrap` feature is enabled (enabled by default).
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
    fn unwrap(self) -> Self::UnwrapOutput
    where
        Self: Unwrap + Sized,
    {
        Unwrap::unwrap(self)
    }

    /// Check if self can be safely [`unwrap()`](TupleLike::unwrap()).
    ///
    /// Only available if the `unwrap` feature is enabled (enabled by default).
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
    fn has_value(&self) -> bool
    where
        Self: Unwrap,
    {
        Unwrap::has_value(self)
    }

    /// Convert `Tuple<Wrapper0<T0>, Wrapper1<T1>, ... Wrappern<Tn>>` to `Tuple<T0, T1, ..., Tn>`,
    /// when all element types `Wrapper0`, `Wrapper1` ... `Wrappern` implement [`UnwrapOrDefault`].
    ///
    /// Unlike [`unwrap()`](TupleLike::unwrap()), if an element does not contain a value, use the
    /// default value instead of panic.
    ///
    /// Only available if the `unwrap` feature is enabled (enabled by default).
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
    fn unwrap_or_default(self) -> Self::UnwrapOutput
    where
        Self: UnwrapOrDefault + Sized,
    {
        UnwrapOrDefault::unwrap_or_default(self)
    }

    /// Convert `Tuple<Wrapper0<T0>, Wrapper1<T1>, ... Wrappern<Tn>>` to `Option<Tuple<T0, T1, ..., Tn>>`,
    /// when all element types `Wrapper0`, `Wrapper1` ... `Wrappern` implement [`Unwrap`].
    ///
    /// Only available if the `unwrap` feature is enabled (enabled by default).
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
    type PushFrontOutput<T> = Tuple<T, Unit>;
    type PushBackOutput<T> = Tuple<T, Unit>;
    type RevOutput = Unit;
    type JoinOutput<T> = T where T: TupleLike;
    type ToSomeOutput = Unit;
    type ToOkOutput<E> = Unit;
    type ToTupleOutput = Unit;

    const LEN: usize = 0;

    fn as_ref(&self) -> Self::AsRefOutput<'_> {
        Self
    }

    fn as_mut(&mut self) -> Self::AsMutOutput<'_> {
        Self
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
}

impl<First, Other> TupleLike for Tuple<First, Other>
where
    Other: TupleLike,
{
    type AsRefOutput<'a> = Tuple<&'a First, Other::AsRefOutput<'a>> where Self: 'a;
    type AsMutOutput<'a> = Tuple<&'a mut First, Other::AsMutOutput<'a>> where Self: 'a;
    type PushFrontOutput<T> = Tuple<T, Self>;
    type PushBackOutput<T> = Tuple<First, Other::PushBackOutput<T>>;
    type RevOutput = <Other::RevOutput as TupleLike>::PushBackOutput<First>;
    type JoinOutput<T> = Tuple<First, Other::JoinOutput<T>> where T: TupleLike;
    type ToSomeOutput = Tuple<Option<First>, Other::ToSomeOutput>;
    type ToOkOutput<E> = Tuple<Result<First, E>, Other::ToOkOutput<E>>;
    type ToTupleOutput = Tuple<Tuple<First, Unit>, Other::ToTupleOutput>;

    const LEN: usize = Other::LEN + 1;

    fn as_ref(&self) -> Self::AsRefOutput<'_> {
        Tuple(&self.0, self.1.as_ref())
    }

    fn as_mut(&mut self) -> Self::AsMutOutput<'_> {
        Tuple(&mut self.0, self.1.as_mut())
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

/// Convert tuples to [primitive tuples](https://doc.rust-lang.org/std/primitive.tuple.html).
///
/// Note that due to the limitation that Rust cannot represent primitive tuple types containing any number of elements,
/// the trait [`ToPrimitive`] is only implemented for tuples with no more than 32 elements.
pub trait ToPrimitive {
    /// The primitive tuple type containing the same number and order of elements.
    type Primitive;

    /// Converts the tuple to the primitive tuple.
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

/// Convert tuples to [primitive arrays](std::array), if all elements of the tuple are of the same type.
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
#[cfg(not(feature = "any_array"))]
pub trait ToArray<T>: super::TupleLike {
    /// The primitive array type to generate.
    type Array;

    /// Converts the tuple to the primitive array.
    fn to_array(self) -> Self::Array;
}

__tuple_traits_impl! { 0; }
__tuple_traits_impl! { 1; T0 }
__tuple_traits_impl! { 2; T0 T1 }
__tuple_traits_impl! { 3; T0 T1 T2 }
__tuple_traits_impl! { 4; T0 T1 T2 T3 }
__tuple_traits_impl! { 5; T0 T1 T2 T3 T4 }
__tuple_traits_impl! { 6; T0 T1 T2 T3 T4 T5 }
__tuple_traits_impl! { 7; T0 T1 T2 T3 T4 T5 T6 }
__tuple_traits_impl! { 8; T0 T1 T2 T3 T4 T5 T6 T7 }
__tuple_traits_impl! { 9; T0 T1 T2 T3 T4 T5 T6 T7 T8 }
__tuple_traits_impl! { 10; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 }
__tuple_traits_impl! { 11; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 }
__tuple_traits_impl! { 12; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 }
__tuple_traits_impl! { 13; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 }
__tuple_traits_impl! { 14; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 }
__tuple_traits_impl! { 15; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 }
__tuple_traits_impl! { 16; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 }
__tuple_traits_impl! { 17; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 }
__tuple_traits_impl! { 18; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 }
__tuple_traits_impl! { 19; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 }
__tuple_traits_impl! { 20; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 }
__tuple_traits_impl! { 21; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 }
__tuple_traits_impl! { 22; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 }
__tuple_traits_impl! { 23; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 }
__tuple_traits_impl! { 24; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 }
__tuple_traits_impl! { 25; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 }
__tuple_traits_impl! { 26; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 }
__tuple_traits_impl! { 27; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 }
__tuple_traits_impl! { 28; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 }
__tuple_traits_impl! { 29; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 }
__tuple_traits_impl! { 30; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 }
__tuple_traits_impl! { 31; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 }
__tuple_traits_impl! { 32; T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 }

impl<T> Add<T> for Unit {
    type Output = T;
    fn add(self, rhs: T) -> Self::Output {
        rhs
    }
}

impl<First1, Other1, First2, Other2> Add<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Add<First2>,
    Other1: Add<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn add(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 + rhs.0, self.1 + rhs.1)
    }
}

impl AddAssign for Unit {
    fn add_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> AddAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: AddAssign<First2>,
    Other1: AddAssign<Other2>,
{
    fn add_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 += rhs.0;
        self.1 += rhs.1;
    }
}

impl Sub for Unit {
    type Output = Unit;
    fn sub(self, _: Unit) -> Self::Output {
        Unit
    }
}

impl<First1, Other1, First2, Other2> Sub<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Sub<First2>,
    Other1: Sub<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn sub(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 - rhs.0, self.1 - rhs.1)
    }
}

impl SubAssign for Unit {
    fn sub_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> SubAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: SubAssign<First2>,
    Other1: SubAssign<Other2>,
{
    fn sub_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 -= rhs.0;
        self.1 -= rhs.1;
    }
}

impl<T> Mul<T> for Unit {
    type Output = T;
    fn mul(self, rhs: T) -> T {
        rhs
    }
}

impl<First1, Other1, First2, Other2> Mul<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Mul<First2>,
    Other1: Mul<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn mul(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 * rhs.0, self.1 * rhs.1)
    }
}

impl MulAssign for Unit {
    fn mul_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> MulAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: MulAssign<First2>,
    Other1: MulAssign<Other2>,
{
    fn mul_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 *= rhs.0;
        self.1 *= rhs.1;
    }
}

impl Div for Unit {
    type Output = Unit;
    fn div(self, _: Unit) -> Self::Output {
        Unit
    }
}

impl<First1, Other1, First2, Other2> Div<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Div<First2>,
    Other1: Div<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn div(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 / rhs.0, self.1 / rhs.1)
    }
}

impl DivAssign for Unit {
    fn div_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> DivAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: DivAssign<First2>,
    Other1: DivAssign<Other2>,
{
    fn div_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 /= rhs.0;
        self.1 /= rhs.1;
    }
}

impl Rem for Unit {
    type Output = Unit;
    fn rem(self, _: Unit) -> Self::Output {
        Unit
    }
}

impl<First1, Other1, First2, Other2> Rem<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Rem<First2>,
    Other1: Rem<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn rem(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 % rhs.0, self.1 % rhs.1)
    }
}

impl RemAssign for Unit {
    fn rem_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> RemAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: RemAssign<First2>,
    Other1: RemAssign<Other2>,
{
    fn rem_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 %= rhs.0;
        self.1 %= rhs.1;
    }
}

impl<T> BitAnd<T> for Unit {
    type Output = T;
    fn bitand(self, rhs: T) -> Self::Output {
        rhs
    }
}

impl<First1, Other1, First2, Other2> BitAnd<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: BitAnd<First2>,
    Other1: BitAnd<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn bitand(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 & rhs.0, self.1 & rhs.1)
    }
}

impl BitAndAssign for Unit {
    fn bitand_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> BitAndAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: BitAndAssign<First2>,
    Other1: BitAndAssign<Other2>,
{
    fn bitand_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 &= rhs.0;
        self.1 &= rhs.1;
    }
}

impl<T> BitOr<T> for Unit {
    type Output = T;
    fn bitor(self, rhs: T) -> Self::Output {
        rhs
    }
}

impl<First1, Other1, First2, Other2> BitOr<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: BitOr<First2>,
    Other1: BitOr<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn bitor(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 | rhs.0, self.1 | rhs.1)
    }
}

impl BitOrAssign for Unit {
    fn bitor_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> BitOrAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: BitOrAssign<First2>,
    Other1: BitOrAssign<Other2>,
{
    fn bitor_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 |= rhs.0;
        self.1 |= rhs.1;
    }
}

impl<T> BitXor<T> for Unit {
    type Output = T;
    fn bitxor(self, rhs: T) -> Self::Output {
        rhs
    }
}

impl<First1, Other1, First2, Other2> BitXor<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: BitXor<First2>,
    Other1: BitXor<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn bitxor(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 ^ rhs.0, self.1 ^ rhs.1)
    }
}

impl BitXorAssign for Unit {
    fn bitxor_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> BitXorAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: BitXorAssign<First2>,
    Other1: BitXorAssign<Other2>,
{
    fn bitxor_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 ^= rhs.0;
        self.1 ^= rhs.1;
    }
}

impl Shl for Unit {
    type Output = Unit;
    fn shl(self, _: Unit) -> Self::Output {
        Unit
    }
}

impl<First1, Other1, First2, Other2> Shl<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Shl<First2>,
    Other1: Shl<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn shl(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 << rhs.0, self.1 << rhs.1)
    }
}

impl ShlAssign for Unit {
    fn shl_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> ShlAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: ShlAssign<First2>,
    Other1: ShlAssign<Other2>,
{
    fn shl_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 <<= rhs.0;
        self.1 <<= rhs.1;
    }
}

impl Shr for Unit {
    type Output = Unit;
    fn shr(self, _: Unit) -> Self::Output {
        Unit
    }
}

impl<First1, Other1, First2, Other2> Shr<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Shr<First2>,
    Other1: Shr<Other2>,
{
    type Output = Tuple<First1::Output, Other1::Output>;
    fn shr(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Tuple(self.0 >> rhs.0, self.1 >> rhs.1)
    }
}

impl ShrAssign for Unit {
    fn shr_assign(&mut self, _: Unit) {}
}

impl<First1, Other1, First2, Other2> ShrAssign<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: ShrAssign<First2>,
    Other1: ShrAssign<Other2>,
{
    fn shr_assign(&mut self, rhs: Tuple<First2, Other2>) {
        self.0 >>= rhs.0;
        self.1 >>= rhs.1;
    }
}

impl Neg for Unit {
    type Output = Unit;

    fn neg(self) -> Self::Output {
        self
    }
}

impl<First: Neg, Other: Neg> Neg for Tuple<First, Other> {
    type Output = Tuple<First::Output, Other::Output>;

    fn neg(self) -> Self::Output {
        Tuple(-self.0, -self.1)
    }
}

impl Not for Unit {
    type Output = Unit;

    fn not(self) -> Self::Output {
        self
    }
}

impl<First: Not, Other: Not> Not for Tuple<First, Other> {
    type Output = Tuple<First::Output, Other::Output>;

    fn not(self) -> Self::Output {
        Tuple(!self.0, !self.1)
    }
}
