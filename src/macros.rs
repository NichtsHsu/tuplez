macro_rules! __from_primitive {
    ($tup:ident; $($v:ident)*) => {{
        use paste::paste;
        paste!{
            let ($([< $v:lower >],)*) = $tup;
            tuple!($([< $v:lower  >]),*)
        }
    }};
}

macro_rules! __to_primitive {
    ($tup:ident $(;)?) => { () };
    ($tup:ident; $($v:ident)+) => {{
        use paste::paste;
        paste!{
            let __to_primitive!(@expand $([< $v:lower >])+) = $tup;
            ($([< $v:lower >],)+)
        }
    }};
    (@expand $v:ident) => {
        Tuple($v, _)
    };
    (@expand $v:ident $($vs:ident)+) => {
        Tuple($v, __to_primitive!(@expand $($vs)+))
    };
}

macro_rules! __from_array {
    ($arr:ident; $($v:ident)*) => {{
        use paste::paste;
        paste!{
            let [$([< $v:lower >],)*] = $arr;
            tuple!($([< $v:lower  >]),*)
        }
    }};
}

macro_rules! __to_array {
    ($tup:ident; $($v:ident)+) => {{
        use paste::paste;
        paste!{
            let __to_primitive!(@expand $([< $v:lower >])+) = $tup;
            [ $([< $v:lower >],)+ ]
        }
    }};
    (@expand $v:ident) => {
        Tuple($v, _)
    };
    (@expand $v:ident $($vs:ident)+) => {
        Tuple($v, __to_primitive!(@expand $($vs)+))
    };
}

#[cfg(not(feature = "any_array"))]
macro_rules! __tuple_array_impl {
    ($cnt:literal;) => {
        impl<T> ToArray<T> for Unit {
            type Array = [T; 0];
            fn to_array(self) -> Self::Array {
                Default::default()
            }
        }

        impl<T> From<[T; 0]> for Unit {
            fn from(_: [T; 0]) -> Self {
                Unit
            }
        }
    };
    ($cnt:literal; $($ts:ident)+) => {
        impl<T> ToArray<T> for tuple_t!(T; $cnt) {
            type Array = [T; $cnt];
            fn to_array(self) -> Self::Array {
                __to_array!(self; $($ts)*)
            }
        }

        impl<T> From<[T; $cnt]> for tuple_t!(T; $cnt) {
            fn from(arr: [T; $cnt]) -> Self {
                __from_array!(arr; $($ts)*)
            }
        }
    };
}

macro_rules! __tuple_traits_impl {
    ($cnt:literal; $($ts:ident)*) => {
        impl<$($ts),*> ToPrimitive for tuple_t!($($ts),*)
        {
            type Primitive = ($($ts,)*);
            fn primitive(self)  -> Self::Primitive {
                __to_primitive!(self; $($ts)*)
            }
        }

        impl<$($ts),*> From<($($ts,)*)> for tuple_t!($($ts),*) {
            fn from(prim: ($($ts,)*)) -> Self {
                __from_primitive!(prim; $($ts)*)
            }
        }

        #[cfg(not(feature = "any_array"))]
        __tuple_array_impl!{ $cnt; $($ts)* }
    };
}

/// Provides a simple way to create a functor that implements [`Mapper`](crate::Mapper).
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
/// A mapping rule is much like a closure, except that it must specify the argument type and the return type:
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
/// Construct specialized mapping rules for all element types in the tuple,
/// and then combine them in the [`mapper!`](crate::mapper!) macro to traverse the tuple:
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(1, "hello", Some(3.14)).map(mapper! {
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
/// use tuplez::*;
///
/// let mut tup = tuple!(1, "hello", Some(3.14));
/// let tup2 = tup.as_ref().map(mapper!{
///     |x: &i32| -> i32 { *x + 1 }
///     <T: ToString> |x: &Option<T>| -> String { x.as_ref().unwrap().to_string() }
///     <'a> |x: &&'a str| -> &'a [u8] { x.as_bytes() }
/// });
/// assert_eq!(tup2, tuple!(2, b"hello" as &[u8], "3.14".to_string()));
/// assert_eq!(tup, tuple!(1, "hello", Some(3.14)));  // And the original tuple is not consumed
///
/// _ = tup.as_mut().map(mapper!{
///     |x: &mut i32| -> () { *x += 1; }
///     <T: ToString> |x: &mut Option<T>| -> () { x.take(); }
///     |x: &mut &str| -> () { *x = "world" }
/// });
/// assert_eq!(tup, tuple!(2, "world", None));
/// ```
///
///

#[macro_export]
macro_rules! mapper {
    ($(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? | $($x:ident)* $(: $it:ty)? | $(-> $ot:ty)? $body:block $($tail:tt)*) => {{
        struct __Mapper;
        mapper!{@impl $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)? | $($x)* $(: $it)? | $(-> $ot)? $body $($tail)* }
        &mut __Mapper
    }};
    (@impl) => {};
    (@impl $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? | $($x:ident)* : $it:ty | $body:block $($tail:tt)*) => {
        impl $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)? Mapper<$it> for __Mapper
        {
            type Output = $it;
            fn map(&mut self, value: $it) -> Self::Output {
                let f = | $($x)* : $it| -> $it { $body };
                f(value)
            }
        }
        mapper!{@impl $($tail)* }
    };
    (@impl $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? | $($x:ident)* : $it:ty | -> $ot:ty $body:block $($tail:tt)*) => {
        impl $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)? Mapper<$it> for __Mapper {
            type Output = $ot;
            fn map(&mut self, value: $it) -> Self::Output {
                let f = | $($x)* : $it| -> $ot { $body };
                f(value)
            }
        }
        mapper!{@impl $($tail)* }
    }
}
