use crate::*;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

pub use to_array::*;

/// The unit type that represents tuples of zero elements.
///
/// Compared with [`Tuple`] type, the unit type does not implement the [`Popable`] trait.
///
/// Suggestion: Use the parameterless [`tuple!`] macro to create a unit:
///
/// ```
/// use tuplez::*;
/// let unit = tuple!();
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Unit;

/// The type used to represent tuples containing at least one element.
///
/// See [`Unit`] type which represents tuples containing no elements.
///
/// The [`TupleLike`] trait defines the basic mothods of all [`Tuple`] types and [`Unit`] type.
///
/// You can create a tuple quickly and easily using the [`tuple!`] macro:
///
/// ```
/// use tuplez::*;
/// let tup = tuple!(1, "hello", 3.14);
/// ```
///
/// Use `;` to indicate repeated elements:
///
/// ```
/// use tuplez::*;
/// assert_eq!(tuple!(1.0, 2;3, "3"), tuple!(1.0, 2, 2, 2, "3"));
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
/// use tuplez::*;
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
/// use tuplez::*;
///
/// let tup = Tuple::from((1, "hello", 3.14)); // or
/// let tup: Tuple<_, _> = From::from((1, "hello", 3.14));
/// ```
///
/// But sometimes, you may still need to specify the complete tuple type explicitly.
/// At this point, you can use the [`tuple_t!`](crate::tuple_t) macro to generate it:
///
/// ```
/// use tuplez::*;
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
/// use tuplez::*;
///
/// let tup: tuple_t!(i32, f64;3, i32) = tuple!(1, 2.0, 3.0, 4.0, 5);
/// ```
///
/// # Element access
///
/// There is a [`get!`](crate::get) macro that can be used to get elements,
/// the only restriction is that the index must be an integer literal:
///
/// ```
/// use tuplez::*;
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
/// use tuplez::*;
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
/// use tuplez::*;
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
/// [`Unit`]s are not [`Popable`], and all [`Tuple`]s are [`Popable`]:
///
/// ```
/// use tuplez::*;
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
/// // _ = unit.pop()                   // Error: cannot pop an `Unit`
/// ```
///
/// You can use the [`split_at!`](crate::split_at) macro to split a tuple into two parts.
/// Like the [`get!`](crate::get) macro, the index must be an integer literal:
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
/// use tuplez::*;
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
/// use tuplez::*;
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
/// use tuplez::*;
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
/// # Traverse tuples
///
/// You can traverse tuples by [`foreach()`](Foreach::foreach()), [`foreach_mut()`](ForeachMut::foreach_mut())
/// and [`foreach_once()`](ForeachOnce::foreach_once()).
///
/// Silimar to [`Fn`] / [`FnMut`] / [`FnOnce`],
/// [`foreach()`](Foreach::foreach()) will traverse all elements in the form of `&T`,
/// [`foreach_mut()`](ForeachMut::foreach_mut()) will traverse all elements in the form of `&mut T`,
/// and [`foreach_once()`](ForeachOnce::foreach_once()) will traverse all elements in the form of `T`,
/// so [`foreach_once()`](ForeachOnce::foreach_once()) will take the ownership of the tuple.
///
/// Call [`foreach()`](Foreach::foreach()) / [`foreach_mut()`](ForeachMut::foreach_mut()) /
/// [`foreach_once()`](ForeachOnce::foreach_once()) on a tuple requires a functor implementing
/// [`Mapper`] / [`MapperMut`] / [`MapperOnce`] as the paramter.
/// Check their documentation pages for examples.
///
/// However, here are [`mapper!`] / [`mapper_mut!`] / [`mapper_once!`] macros that can help you
/// quickly generate a simple functor:
///
/// ```
/// use tuplez::*;
///
/// fn to_string<T: ToString>(v: T) -> String {
///     v.to_string()
/// }
///
/// let tup = tuple!(1, "hello", 3.14);
/// let tup2 = tup.foreach_once(mapper_once!{
///     _ => String: to_string where ToString
/// });     // Currently, the bounds of the function must be written explicitly within the macro
/// assert_eq!(tup2, tuple!("1".to_string(), "hello".to_string(), "3.14".to_string()));
///
/// let tup3 = tup.foreach(mapper!{
///    x: i32 => i64: *x as i64;
///    x: f32 => String: x.to_string();
///    x, 'a: &'a str => &'a [u8]: x.as_bytes()
/// });     // Reference types need to explicitly introduce its lifetime parameters
/// assert_eq!(tup3, tuple!(1i64, b"hello" as &[u8], "3.14".to_string()));
/// ```
///
/// Check the documentation pages of these macros for detailed syntax.
///
/// # Convert from/to primitive tuples
///
/// Okay, we're finally talking about the only interfaces of [`Tuple`] that limits the maximum number of elements.
///
/// Since Rust does not have a way to represent [primitive tuple types](https://doc.rust-lang.org/std/primitive.tuple.html) with an arbitrary number of elements,
/// the interfaces for converting from/to primitive tuple types is only implemented for [`Tuple`]s with no more than 32 elements.
///
/// ```
/// use tuplez::*;
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
/// use tuplez::*;
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
pub struct Tuple<First, Other>(
    /// First element.
    pub First,
    /// Other elements. See [representation](Tuple#representation).
    pub Other,
);

/// The [`TupleLike`] trait defines the basic methods of tuples.
///
/// Notice that an [`Unit`] contains no elements and cannot be popped, so the pop methods is not required methods of a tuple.
/// See the [`Popable`] trait about pop methods.
///
/// In fact, all tuples implement the rotation methods.
/// However, since right rotation requires additional detection of whether the tuple can be popped,
/// and cannot be introduced into [`TupleLike`] in a elegant way, so an extra trait [`Rotatable`] is used for them.
///
/// Another thing is, due to the limitation that Rust cannot represent
/// [primitive tuple types]((https://doc.rust-lang.org/std/primitive.tuple.html)) containing any number of elements,
/// we cannot make [`TupleLike`] trait contain a method that converts tuple to the primitive tuple type.
/// Therefore, this method is provided by the trait [`ToPrimitive`] and is only implemented for tuples with no more than 32 elements.
pub trait TupleLike {
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

    /// The number of elements in the tuple.
    const LEN: usize;

    /// Returns the number of elements in the tuple.
    /// MUST always return [`LEN`](TupleLike::LEN).
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::*;
    /// assert_eq!(tuple!(1, "hello", 3.14).len(), 3);
    /// ```
    fn len(&self) -> usize {
        Self::LEN
    }

    /// Push an element to the back of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::*;
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
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let tup2 = tup.push_front(44);
    /// assert_eq!(tup2, tuple!(44, 1, "hello", 3.14));
    /// ```
    fn push_front<T>(self, value: T) -> Self::PushFrontOutput<T>;

    /// Push an element to the back of the tuple. Same as [`push()`](TupleLike::push()).
    fn push_back<T>(self, value: T) -> Self::PushBackOutput<T>;

    /// Reverse elements of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::*;
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
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let tup2 = tuple!(44, "world");
    /// let tup3 = tup.join(tup2);
    /// assert_eq!(tup3, tuple!(1, "hello", 3.14, 44, "world"));
    /// ```
    fn join<T>(self, value: T) -> Self::JoinOutput<T>
    where
        T: TupleLike;
}

impl TupleLike for Unit {
    type PushFrontOutput<T> = Tuple<T, Unit>;
    type PushBackOutput<T> = Tuple<T, Unit>;
    type RevOutput = Unit;
    type JoinOutput<T> = T where T: TupleLike;

    const LEN: usize = 0;

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
}

impl<First, Other> TupleLike for Tuple<First, Other>
where
    Other: TupleLike,
{
    type PushFrontOutput<T> = Tuple<T, Self>;
    type PushBackOutput<T> = Tuple<First, Other::PushBackOutput<T>>;
    type RevOutput = <Other::RevOutput as TupleLike>::PushBackOutput<First>;
    type JoinOutput<T> = Tuple<First, Other::JoinOutput<T>> where T: TupleLike;

    const LEN: usize = Other::LEN + 1;

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
}

/// The [`Popable`] trait allows popping elements from the front and back of the tuple.
///
/// The [`Unit`] type is not [`Popable`]. All [`Tuple`]s are [`Popable`].
pub trait Popable {
    /// The type of tuple generated by popping an element from the front of the tuple.
    type PopFrontOutput: TupleLike;

    /// The type of the element popped from the front of the tuple.
    type PopFrontElemet;

    /// The type of tuple generated by popping an element from the back of the tuple.
    type PopBackOutput: TupleLike;

    /// The type of the element popped from the back of the tuple.
    type PopBackElement;

    /// Pop an element from the back of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let (tup2, popped) = tup.pop();
    /// assert_eq!(tup2, tuple!(1, "hello"));
    /// assert_eq!(popped, 3.14);
    /// ```
    fn pop(self) -> (Self::PopBackOutput, Self::PopBackElement);

    /// Pop an element from the front of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "hello", 3.14);
    /// let (tup2, popped) = tup.pop_front();
    /// assert_eq!(tup2, tuple!("hello", 3.14));
    /// assert_eq!(popped, 1);
    /// ```
    fn pop_front(self) -> (Self::PopFrontOutput, Self::PopFrontElemet);

    /// Pop an element from the back of the tuple. Same as [`pop()`](Popable::pop()).
    fn pop_back(self) -> (Self::PopBackOutput, Self::PopBackElement);
}

impl<First, Other> Popable for Tuple<First, Other>
where
    Other: Popable + TupleLike,
{
    type PopFrontOutput = Other;
    type PopFrontElemet = First;
    type PopBackOutput = Tuple<First, Other::PopBackOutput>;
    type PopBackElement = Other::PopBackElement;

    fn pop(self) -> (Self::PopBackOutput, Self::PopBackElement) {
        let (tup, elem) = self.1.pop();
        (Tuple(self.0, tup), elem)
    }

    fn pop_front(self) -> (Self::PopFrontOutput, Self::PopFrontElemet) {
        (self.1, self.0)
    }

    fn pop_back(self) -> (Self::PopBackOutput, Self::PopBackElement) {
        self.pop()
    }
}

impl<First> Popable for Tuple<First, Unit> {
    type PopFrontOutput = Unit;
    type PopFrontElemet = First;
    type PopBackOutput = Unit;
    type PopBackElement = First;
    fn pop(self) -> (Self::PopBackOutput, Self::PopBackElement) {
        (Unit, self.0)
    }

    fn pop_front(self) -> (Self::PopFrontOutput, Self::PopFrontElemet) {
        (Unit, self.0)
    }

    fn pop_back(self) -> (Self::PopBackOutput, Self::PopBackElement) {
        self.pop()
    }
}

/// The [`Rotatable`] trait allows you to rotate the elements of the tuple.
///
/// In fact, all tuples implement [`Rotatable`], including [`Unit`].
/// However, implementing right rotation for [`Tuple`]s relies on [`pop()`](Popable::pop()),
/// so this trait cannot be incorporated into [`TupleLike`] elegantly.
pub trait Rotatable {
    /// The type of tuple generated by left rorating the elements of the tuple.
    type RotLeftOutput: TupleLike;

    /// The type of tuple generated by right rotating the elements of the tuple.
    type RotRightOutput: TupleLike;

    /// Left rotates the elements of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "2", 3.0, 4);
    /// let tup2 = tup.rot_l();
    /// assert_eq!(tup2, tuple!("2", 3.0, 4, 1));
    /// ```
    fn rot_l(self) -> Self::RotLeftOutput;

    /// Right rotates the elements of the tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "2", 3.0, 4);
    /// let tup2 = tup.rot_r();
    /// assert_eq!(tup2, tuple!(4, 1, "2", 3.0));
    /// ```
    fn rot_r(self) -> Self::RotRightOutput;
}

impl Rotatable for Unit {
    type RotLeftOutput = Unit;
    type RotRightOutput = Unit;

    fn rot_l(self) -> Unit {
        self
    }

    fn rot_r(self) -> Unit {
        self
    }
}

impl<First, Other> Rotatable for Tuple<First, Other>
where
    Other: TupleLike,
    Self: Popable,
{
    type RotLeftOutput = Other::PushBackOutput<First>;
    type RotRightOutput =
        Tuple<<Self as Popable>::PopBackElement, <Self as Popable>::PopBackOutput>;

    fn rot_l(self) -> Self::RotLeftOutput {
        let Tuple(first, other) = self;
        other.push(first)
    }

    fn rot_r(self) -> Self::RotRightOutput {
        let (out, elem) = self.pop();
        Tuple(elem, out)
    }
}

/// The [`ToPrimitive`] trait allows you to convert tuplez's tuples to [primitive tuples](https://doc.rust-lang.org/std/primitive.tuple.html).
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
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "2", 3.0, 4);
    /// let prim = tup.primitive();
    /// assert_eq!(prim, (1, "2", 3.0, 4));
    /// ```
    fn primitive(self) -> Self::Primitive;
}

#[cfg(not(feature = "any_array"))]
mod to_array {
    /// The [`ToArray`] trait allows you to convert tuples to [primitive arrays](std::array),
    /// if and only if all elements of the tuple are of the same type.
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
    pub trait ToArray<T>: super::TupleLike {
        /// The primitive array type to generate.
        type Array;

        /// Converts the tuple to the primitive array.
        fn to_array(self) -> Self::Array;
    }
}

#[cfg(feature = "any_array")]
pub mod to_array {
    use std::mem::MaybeUninit;

    use crate::{Tuple, TupleLike, Unit};

    trait FillSlice<T>: TupleLike {
        fn fill_slice(self, arr: &mut [MaybeUninit<T>], index: usize);
    }

    impl<T> FillSlice<T> for Unit {
        fn fill_slice(self, _: &mut [MaybeUninit<T>], _: usize) {}
    }

    impl<First, Other> FillSlice<First> for Tuple<First, Other>
    where
        Other: FillSlice<First>,
    {
        fn fill_slice(self, arr: &mut [MaybeUninit<First>], index: usize) {
            let Tuple(first, other) = self;
            arr[index].write(first);
            other.fill_slice(arr, index + 1);
        }
    }

    /// The [`ToArray`] trait allows you to convert tuples to [primitive arrays](std::array),
    /// if and only if all elements of the tuple are of the same type.
    ///
    /// *Warning*: You have enabled the `any_array` feature, which will allow to use the unstable features to implement
    /// [`ToArray`] for tuples with any number of elements.
    ///
    /// Always remember: unstable features are not guaranteed by Rust and may not be available someday in the future.
    pub trait ToArray<T>: TupleLike {
        /// The primitive array type to generate.
        type Array;

        /// Converts the tuple to the primitive array.
        fn to_array(self) -> Self::Array;
    }

    impl<T> ToArray<T> for Unit {
        type Array = [T; 0];

        fn to_array(self) -> Self::Array {
            Default::default()
        }
    }

    impl<First, Other> ToArray<First> for Tuple<First, Other>
    where
        Self: FillSlice<First>,
        [First; Self::LEN]:,
    {
        type Array = [First; Self::LEN];

        fn to_array(self) -> Self::Array {
            let mut arr: [MaybeUninit<First>; Self::LEN] = MaybeUninit::uninit_array();
            self.fill_slice(&mut arr, 0);
            unsafe { MaybeUninit::array_assume_init(arr) }
        }
    }

    trait FromSlice<T>: TupleLike {
        fn from_slice(arr: &mut [MaybeUninit<T>], index: usize) -> Self;
    }

    impl<T> FromSlice<T> for Unit {
        fn from_slice(_: &mut [MaybeUninit<T>], _: usize) -> Self {
            Unit
        }
    }

    impl<First, Other> FromSlice<First> for Tuple<First, Other>
    where
        Other: FromSlice<First>,
    {
        fn from_slice(arr: &mut [MaybeUninit<First>], index: usize) -> Self {
            let v = std::mem::replace(&mut arr[index], MaybeUninit::uninit());
            Tuple(
                unsafe { v.assume_init() },
                Other::from_slice(arr, index + 1),
            )
        }
    }

    impl<T> From<[T; 0]> for Unit {
        fn from(_: [T; 0]) -> Self {
            Unit
        }
    }

    impl<First, Other> From<[First; Self::LEN]> for Tuple<First, Other>
    where
        Self: FromSlice<First>,
    {
        fn from(value: [First; Self::LEN]) -> Self {
            let mut arr = MaybeUninit::new(value).transpose();
            Self::from_slice(&mut arr, 0)
        }
    }
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

impl Add for Unit {
    type Output = Unit;
    fn add(self, _: Unit) -> Self::Output {
        Unit
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

impl Mul for Unit {
    type Output = Unit;
    fn mul(self, _: Unit) -> Self::Output {
        Unit
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

impl BitAnd for Unit {
    type Output = Unit;
    fn bitand(self, _: Unit) -> Self::Output {
        Unit
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

impl BitOr for Unit {
    type Output = Unit;
    fn bitor(self, _: Unit) -> Self::Output {
        Unit
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

impl BitXor for Unit {
    type Output = Unit;
    fn bitxor(self, _: Unit) -> Self::Output {
        Unit
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

impl<F> Foreach<F> for Unit {
    type Output = Unit;
    fn foreach(&self, _: &mut F) -> Self::Output {
        Unit
    }
}

impl<F, First, Other> Foreach<F> for Tuple<First, Other>
where
    F: Mapper<First>,
    Other: Foreach<F>,
{
    type Output = Tuple<<F as Mapper<First>>::Output, <Other as Foreach<F>>::Output>;
    fn foreach(&self, f: &mut F) -> Self::Output {
        Tuple(f.map(&self.0), self.1.foreach(f))
    }
}

impl<F> ForeachMut<F> for Unit {
    type Output = Unit;
    fn foreach_mut(&mut self, _: &mut F) -> Self::Output {
        Unit
    }
}

impl<F, First, Other> ForeachMut<F> for Tuple<First, Other>
where
    F: MapperMut<First>,
    Other: ForeachMut<F>,
{
    type Output = Tuple<<F as MapperMut<First>>::Output, <Other as ForeachMut<F>>::Output>;
    fn foreach_mut(&mut self, f: &mut F) -> Self::Output {
        Tuple(f.map_mut(&mut self.0), self.1.foreach_mut(f))
    }
}

impl<F> ForeachOnce<F> for Unit {
    type Output = Unit;
    fn foreach_once(self, _: &mut F) -> Self::Output {
        Unit
    }
}

impl<F, First, Other> ForeachOnce<F> for Tuple<First, Other>
where
    F: MapperOnce<First>,
    Other: ForeachOnce<F>,
{
    type Output = Tuple<<F as MapperOnce<First>>::Output, <Other as ForeachOnce<F>>::Output>;
    fn foreach_once(self, f: &mut F) -> Self::Output {
        Tuple(f.map_once(self.0), self.1.foreach_once(f))
    }
}
