macro_rules! __tuple_unary_ops_impl {
    ($($tr:ident :: $f:ident ()),* $(,)?) => {
        $(__tuple_unary_ops_impl!{ @impl $tr $f })*
    };
    (@impl $tr:ident $f:ident) => {
        impl $tr for Unit {
            type Output = Unit;

            fn $f(self) -> Self::Output {
                self
            }
        }

        impl $tr for &Unit {
            type Output = Unit;

            fn $f(self) -> Self::Output {
                Unit
            }
        }

        impl<First, Other> $tr for Tuple<First, Other>
        where
            First: $tr,
            Other: $tr + TupleLike,
        {
            type Output = Tuple<First::Output, Other::Output>;

            fn $f(self) -> Self::Output {
                Tuple($tr::$f(self.0), $tr::$f(self.1))
            }
        }

        impl<'a, First, Other> $tr for &'a Tuple<First, Other>
        where
            &'a First: $tr,
            &'a Other: $tr,
            Other: TupleLike,
        {
            type Output = Tuple<<&'a First as $tr>::Output, <&'a Other as $tr>::Output>;

            fn $f(self) -> Self::Output {
                Tuple($tr::$f(&self.0), $tr::$f(&self.1))
            }
        }
    }
}

macro_rules! __tuple_binary_ops_impl {
    ($($tr:ident :: $f:ident ()),* $(,)?) => {
        $(__tuple_binary_ops_impl!{ @impl $tr $f })*
    };
    (@impl $tr:ident $f:ident) => {
        impl<T> $tr<T> for Unit {
            type Output = T;
            fn $f(self, rhs: T) -> Self::Output {
                rhs
            }
        }

        impl<T> $tr<T> for &Unit {
            type Output = T;
            fn $f(self, rhs: T) -> Self::Output {
                rhs
            }
        }

        impl<First, Other> $tr<Unit> for Tuple<First, Other>
        where
            Other: TupleLike
        {
            type Output = Self;
            fn $f(self, _: Unit) -> Self::Output {
                self
            }
        }

        impl<First, Other> $tr<&Unit> for Tuple<First, Other>
        where
            Other: TupleLike
        {
            type Output = Self;
            fn $f(self, _: &Unit) -> Self::Output {
                self
            }
        }

        impl<First, Other> $tr<Unit> for &Tuple<First, Other>
        where
            Tuple<First, Other>: Clone,
            Other: TupleLike
        {
            type Output = Tuple<First, Other>;
            fn $f(self, _: Unit) -> Self::Output {
                Clone::clone(self)
            }
        }

        impl<First, Other> $tr<&Unit> for &Tuple<First, Other>
        where
            Tuple<First, Other>: Clone,
            Other: TupleLike
        {
            type Output = Tuple<First, Other>;
            fn $f(self, _: &Unit) -> Self::Output {
                Clone::clone(self)
            }
        }

        impl<First1, Other1, First2, Other2> $tr<Tuple<First2, Other2>> for Tuple<First1, Other1>
        where
            First1: $tr<First2>,
            Other1: $tr<Other2> + TupleLike,
            Other2: TupleLike,
        {
            type Output = Tuple<First1::Output, Other1::Output>;
            fn $f(self, rhs: Tuple<First2, Other2>) -> Self::Output {
                Tuple($tr::$f(self.0, rhs.0), $tr::$f(self.1, rhs.1))
            }
        }

        impl<'a, First1, Other1, First2, Other2> $tr<&'a Tuple<First2, Other2>> for Tuple<First1, Other1>
        where
            First1: $tr<&'a First2>,
            Other1: $tr<&'a Other2> + TupleLike,
            Other2: TupleLike,
        {
            type Output = Tuple<First1::Output, Other1::Output>;
            fn $f(self, rhs: &'a Tuple<First2, Other2>) -> Self::Output {
                Tuple($tr::$f(self.0, &rhs.0), $tr::$f(self.1, &rhs.1))
            }
        }

        impl<'a, First1, Other1, First2, Other2> $tr<Tuple<First2, Other2>> for &'a Tuple<First1, Other1>
        where
            &'a First1: $tr<First2>,
            &'a Other1: $tr<Other2>,
            Other1: TupleLike,
            Other2: TupleLike,
        {
            type Output = Tuple<<&'a First1 as $tr<First2>>::Output, <&'a Other1 as $tr<Other2>>::Output>;
            fn $f(self, rhs: Tuple<First2, Other2>) -> Self::Output {
                Tuple($tr::$f(&self.0, rhs.0), $tr::$f(&self.1, rhs.1))
            }
        }

        impl<'a, 'b, First1, Other1, First2, Other2> $tr<&'a Tuple<First2, Other2>>
            for &'b Tuple<First1, Other1>
        where
            &'b First1: $tr<&'a First2>,
            &'b Other1: $tr<&'a Other2>,
            Other1: TupleLike,
            Other2: TupleLike,
        {
            type Output =
                Tuple<<&'b First1 as $tr<&'a First2>>::Output, <&'b Other1 as $tr<&'a Other2>>::Output>;
            fn $f(self, rhs: &'a Tuple<First2, Other2>) -> Self::Output {
                Tuple($tr::$f(&self.0, &rhs.0), $tr::$f(&self.1, &rhs.1))
            }
        }
    }
}

macro_rules! __tuple_assignment_ops_impl {
    ($($tr:ident :: $f:ident ()),* $(,)?) => {
        $(__tuple_assignment_ops_impl!{ @impl $tr $f })*
    };
    (@impl $tr:ident $f:ident) => {
        impl $tr<Unit> for Unit {
            fn $f(&mut self, _: Unit) {}
        }

        impl $tr<&Unit> for Unit {
            fn $f(&mut self, _: &Unit) {}
        }

        impl<First1, Other1, First2, Other2> $tr<Tuple<First2, Other2>> for Tuple<First1, Other1>
        where
            First1: $tr<First2> + TupleLike,
            Other1: $tr<Other2> + TupleLike,
        {
            fn $f(&mut self, rhs: Tuple<First2, Other2>) {
                self.0.$f(rhs.0);
                self.1.$f(rhs.1);
            }
        }

        impl<'a, First1, Other1, First2, Other2> $tr<&'a Tuple<First2, Other2>>
            for Tuple<First1, Other1>
        where
            First1: $tr<&'a First2> + TupleLike,
            Other1: $tr<&'a Other2> + TupleLike,
        {
            fn $f(&mut self, rhs: &'a Tuple<First2, Other2>) {
                self.0.$f(&rhs.0);
                self.1.$f(&rhs.1);
            }
        }
    }
}

pub(crate) use __tuple_assignment_ops_impl;
pub(crate) use __tuple_binary_ops_impl;
pub(crate) use __tuple_unary_ops_impl;

/// Generate a tuple from a list of expressions.
///
/// # Syntax
///
/// `tuple!( [ Expr1 [; Count], Expr2 [; Count], ... ] )`
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputting `...`.*
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
/// Remember that the [`tuple!`](crate::tuple!) macro does not directly evaluate expressions, so:
///
/// ```
/// use tuplez::tuple;
///
/// let mut x = 0;
/// assert_eq!(tuple!({x += 1; x}; 3), tuple!(1, 2, 3));
/// ```
#[macro_export]
macro_rules! tuple {
    ($($t:tt)*) => {
        $crate::tuple_inner!(::tuplez; $($t)*)
    };
}

/// Generate the complete type signature for tuples.
///
/// # Syntax
///
/// `tuple_t!([T0 [; Count], T1 [; Count], ... ])`
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputting `...`.*
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
#[macro_export]
macro_rules! tuple_t {
    ($($t:tt)*) => {
        $crate::tuple_t_inner!(::tuplez; $($t)*)
    };
}

/// Generate patterns for tuples.
///
/// # Syntax
///
/// `tuple_pat!([#] [Pat0 [; Count], Pat1 [; Count], ... ])`
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputting `...`.*
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
#[macro_export]
macro_rules! tuple_pat {
    ($($t:tt)*) => {
        $crate::tuple_pat_inner!(::tuplez; $($t)*)
    };
}

/// Take the element at a specific index of the tuple and get the remainder.
///
/// When the type of element is provided instead of its index, this macro expands to
/// [`take()`](crate::TupleLike::take()).
///
/// The [`pop()`](crate::TupleLike::pop()) and [`pop_front()`](crate::TupleLike::pop_front()) methods
/// also provide ways to pop elements from the front or back of the tuple.
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
/// Use indices:
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
#[macro_export]
macro_rules! take {
    ($($t:tt)*) => {
        $crate::take_inner!(::tuplez; $($t)*)
    };
}

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
#[macro_export]
macro_rules! split_at {
    ($($t:tt)*) => {
        $crate::split_at_inner!(::tuplez; $($t)*)
    };
}

/// Provides a simple way to build a mapper that implements [`Mapper`](crate::foreach::Mapper).
///
/// # Syntax
///
/// ```text
/// Generic = [Lifetime1, Lifetime2, ...] [Type1 [: Bound1], Type2 [: Bound2], ...]
/// Rule    = [ < Generic > ] | Variable : InputType | [-> OutputType] { Body } [,] [;]
///
/// mapper!( [Rule1 Rule2 ... ] )
/// ```
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputting `...`.*
///
/// # Explanation
///
/// A mapping rule is much like a closure, except that it must annotate the argument type and the return type:
///
/// ```text
/// |x: i32| -> i64 { x as i64 }
/// ```
///
/// Note that it's just like but not really a closure, so you can't capture context variables.
///
/// Also supports adding `mut`:
///
/// ```text
/// |mut x: i32| -> i64 { x += 1; x as i64 }
/// ```
///
/// If the return value requires a lifetime, you need to explicitly introduce the lifetime annotation, since Rust binds the lifetime
/// of return value to the mapper instead of the element by default:
///
/// ```text
/// <'a> |x: &'a str| -> &'a [u8] { x.as_bytes() }
/// ```
///
/// You can omit the return type when the return type is the same as the element type.
/// Note: Do not misunderstand that the return type is automatically inferred or is a `()`.
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
/// It is allowed to add commas or semicolons as separators between rules. Sometimes this may look better.
///
/// Tip: If you don't want to consume the tuple, call its [`as_ref()`](crate::TupleLike::as_ref()) before traversing.
/// Likewise, if you want to modify elements of tuple, call its [`as_mut()`](crate::TupleLike::as_mut()) before traversing.
///
/// ```
/// use tuplez::{mapper, tuple, TupleLike};
///
/// let mut tup = tuple!(1, "hello", Some(3.14));
/// let tup2 = tup.as_ref().foreach(mapper! {
///     |x: &i32| -> i32 { *x + 1 }
///     <T: ToString> |x: &Option<T>| -> String { x.as_ref().unwrap().to_string() }
///     <'a> |x: &&'a str| -> &'a [u8] { x.as_bytes() }
/// });
/// assert_eq!(tup2, tuple!(2, b"hello" as &[u8], "3.14".to_string()));
/// assert_eq!(tup, tuple!(1, "hello", Some(3.14)));  // And the original tuple is not consumed
///
/// _ = tup.as_mut().foreach(mapper! {
///     |x: &mut i32| -> () { *x += 1; }
///     <T: ToString> |x: &mut Option<T>| -> () { x.take(); }
///     |x: &mut &str| -> () { *x = "world" }
/// });
/// assert_eq!(tup, tuple!(2, "world", None));
/// ```
#[macro_export]
macro_rules! mapper {
    ($($t:tt)*) => {
        $crate::mapper_inner!(::tuplez; $($t)*)
    };
}

/// Provides a simple way to build a folder that implements [`Folder`](crate::fold::Folder).
///
/// # Syntax
///
/// ```text
/// Generic = [Lifetime1, Lifetime2, ...] [Type1 [: Bound1], Type2 [: Bound2], ...]
/// Rule    = [ < Generic > ] | Variable1, Variable2 : InputType | { Body } [,] [;]
///
/// folder!( OutputType; [Rule1 Rule2 ... ] )
/// ```
///
/// *`[` and `]` only indicate the optional content but not that they need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputting `...`.*
///
/// # Explanation
///
/// A folding rule is much like a closure, except that it must annotate the element type:
///
/// ```text
/// |acc, x: i32| { acc + x }
/// ```
///
/// Note that it's just like but not really a closure, so you can't capture context variables.
///
/// You'd better not annotate types for the accumulation value and return value,
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
/// and then combine them in the [`folder!`](crate::folder!) macro to fold the tuple:
///
/// ```
/// use std::convert::AsRef;
/// use tuplez::{folder, tuple, TupleLike};
///
/// let tup = tuple!(1, "2", 3.0);
/// let result = tup.fold(
///     folder! {i32;        // Annotate the accumulation value type
///         |acc, x: i32| { acc + x }
///         |acc, x: f32| { acc + (x as i32) }
///         // `str` is a DST, so `?Sized` bound is required.
///         <T: AsRef<str> + ?Sized> |acc, x: &T| { acc + x.as_ref().parse::<i32>().unwrap() }
///     },
///     0
/// );
/// assert_eq!(result, 6);
/// ```
///
/// It is allowed to add commas or semicolons as separators between rules. Sometimes this may look better.
#[macro_export]
macro_rules! folder {
    ($($t:tt)*) => {
        $crate::folder_inner!(::tuplez; $($t)*)
    };
}

/// Provides a simple way to build a unary predicate that implements [`UnaryPredicate`](crate::predicate::UnaryPredicate).
///
/// # Syntax
///
/// ```text
/// Generic = [Lifetime1, Lifetime2, ...] [Type1 [: Bound1], Type2 [: Bound2], ...]
/// Rule    = [ < Generic > ] | Variable : InputType | { Body } [,] [;]
///
/// unary_pred!( [Rule1 Rule2 ... ] )
/// ```
///
/// # Explanation
///
/// A unary predicate rule is much like a closure, except that it must annotate the element type,
/// and what you actually get is the immutable reference to the element rather than itself.
///
/// ```text
/// |x: i32| { *x > 10 }    // The actual type of `x` is `&i32` not `i32`
/// ```
///
/// Note that it's just like but not really a closure, so you can't capture context variables.
///
/// You'd better not annotate types for the return value of rules,
/// because they must return a `bool` value. Of course you can do that,
/// but there would be no advantage other than potential compilation errors.
///
/// You can also introduce generic types like this:
///
/// ```text
/// <T: Fn(i32) -> bool> |f: T| { f(1) }
/// ```
///
/// Construct unary predicate rules for all element types in the tuple,
/// and then combine them in the [`unary_pred!`](crate::unary_pred!) macro to test the tuple:
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
/// It is allowed to add commas or semicolons as separators between rules. Sometimes this may look better.
///
/// # As a [`Mapper`](crate::foreach::Mapper)
///
/// In fact, this macro does not directly implement [`UnaryPredicate<T>`](crate::predicate::UnaryPredicate) for the
/// underlying type. Instead, it implements [`Mapper<&T, Output=bool>`](crate::foreach::Mapper).
///
/// Therefore, you can definitely use it as a [`Mapper`](crate::foreach::Mapper) like this:
///
/// ```
/// use tuplez::{tuple, TupleLike, unary_pred};
///
/// let tup = tuple!(Some(1), "", |x: i32| x == 0);
/// let result = tup.as_ref().foreach(
///     unary_pred! {
///         |x: Option<i32>| { x.is_some() }
///         |x: &str| { !x.is_empty() }
///         <T: Fn(i32) -> bool> |f: T| { f(1) }
///     }
/// );
///
/// assert_eq!(result, tuple!(true, false, false));
/// ```
#[macro_export]
macro_rules! unary_pred {
    ($($t:tt)*) => {
        $crate::unary_pred_inner!(::tuplez; $($t)*)
    };
}

