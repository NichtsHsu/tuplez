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

macro_rules! __tuple_array_impl {
    ($cnt:literal;) => {
        #[cfg(not(feature = "any_array"))]
        impl<T> ToArray<T> for Unit {
            type Array = [T; 0];
            fn to_array(self) -> Self::Array {
                Default::default()
            }
        }

        #[cfg(not(feature = "any_array"))]
        impl<T> From<[T; 0]> for Unit {
            fn from(_: [T; 0]) -> Self {
                Unit
            }
        }
    };
    ($cnt:literal; $($ts:ident)+) => {
        #[cfg(not(feature = "any_array"))]
        impl<T> ToArray<T> for tuple_t!(T; $cnt) {
            type Array = [T; $cnt];
            fn to_array(self) -> Self::Array {
                __to_array!(self; $($ts)*)
            }
        }

        #[cfg(not(feature = "any_array"))]
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

        __tuple_array_impl!{ $cnt; $($ts)* }
    };
}

/// Provides a simple way to create a functor that implements [`Mapper`](crate::mapper::Mapper).
///
/// # Syntax
///
/// ```text
/// Introduce   = Variable [, Lifetime1, Lifetime2, ... ]
/// TypeMap     = TypeIn [=> TypeOut]
/// Specialized = Introduce : TypeMap : Expr
/// Universal   = _ : TypeMap : Function [where Bounds]
///
/// mapper!([ Specialized1; Specialized2; ... ] [; Univsersal])
/// ```
///
/// *The `[` and `]` markers only indicate optional content but not that the `[` and `]` need to be input.*
///
/// *Similarly, `...` indicates several repeated segments, rather than inputing `...`.*
///
/// # Explanation
///
/// ## Specialized mapping rules
///
/// Firstly introduce a variable name used to represent the element (Recommand using `x`) and all possible lifetime paramters.
/// If the element type contains a reference or generic lifetime parameter, please explicitly annotate all lifetimes:
///
/// ```text
/// x, 'a
/// ```
///
/// Then specify the mapping of the type, that is, element type => output type.
/// If the element type and output type are the same type, the output type can be omitted:
///
/// ```text
/// &'a str => &'a [u8]
/// ```
///
/// Next, write down the conversion expression, remember that `x` is an immutable reference to the element:
///
/// ```text
/// x.as_bytes()
/// ```
///
/// Finally, use `:` to link them, and a specialized mapping rule is complete:
///
/// ```text
/// x, 'a : &'a str => &'a [u8] : x.as_bytes()
/// ```
///
/// Construct specialized mapping rules for all element types in the tuple,
/// and then combine them in a [`mapper!`](crate::mapper!) macro to traverse the tuple:
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(1, "hello", 3.14).foreach(mapper!{
///    x: i32 : *x + 1;                                 // Omit the output type
///    x: f32 => String: x.to_string();
///    x, 'a: &'a str => &'a [u8]: x.as_bytes()
/// });
/// assert_eq!(tup, tuple!(2, b"hello" as &[u8], "3.14".to_string()));
/// ```
///
/// ## Universal mapping rule
///
/// Universal mapping rule currently only supports conversion through generic functions, not expressions.
/// So first define the mapping function:
///
/// ```
/// fn to_string<T: ToString>(v: &T) -> String {
///     v.to_string()
/// }
/// ```
///
/// Write down the mapping of types as before, only this time we use an `_` for element types.
///
/// ```text
/// _ => String
/// ```
///
/// Finally, use `:` to link them. But there is a little noise here. We need to write down the bounds of the mapping
/// function as well:
///
/// ```text
/// _ => String : to_string where ToString
/// ```
///
/// Put it in the [`mapper!`](crate::mapper!) macro to traverse the tuple:
///
/// ```
/// use tuplez::*;
///
/// fn to_string<T: ToString>(v: &T) -> String {
///     v.to_string()
/// }
///
/// let tup = tuple!(1, "hello", 3.14);
/// let tup2 = tup.foreach(mapper! {
///     _ => String: to_string where ToString
/// });
/// assert_eq!(
///     tup2,
///     tuple!("1".to_string(), "hello".to_string(), "3.14".to_string())
/// );
/// ```
///
/// If the mapping function output the same type, the output type can be omitted:
///
/// ```
/// use tuplez::*;
///
/// fn just<T: Copy>(v: &T) -> T { *v }
///
/// let tup = tuple!(1, "hello", 3.14);
/// let tup2 = tup.foreach(mapper! {
///     _ : just where Copy
/// });
/// assert_eq!(tup, tup2);
/// ```
///
/// ## Use both
///
/// You can use both multiple specialized mapping rules and one universal mapping rule in a [`mapper!`](crate::mapper!) macro,
/// but there are some restrictions.
///
/// 1. The universal mapping rule must be placed after all specialized mapping rules.
/// 2. Types that use specialized mapping rules must be exclusive from the bounds of the universal mapping rule.
/// 3. Either all types that use specialized mapping rules is your custom types, or the bounds of the universal mapping rule contain
/// your custom traits.
///
/// Example of custom type:
///
/// ```
/// use tuplez::*;
///
/// struct MyElement(i32);
///
/// fn to_string<T: ToString>(v: &T) -> String {
///     v.to_string()
/// }
///
/// let tup = tuple!(MyElement(12), "hello", 3.14);
/// let tup2 = tup.foreach(mapper! {
///     x : MyElement => i32 : x.0;
///     _ => String: to_string where ToString
/// });
/// assert_eq!(tup2, tuple!(12, "hello".to_string(), "3.14".to_string()));
/// ```
///
/// Example of custom trait:
///
/// ```
/// use tuplez::*;
///
/// trait MyToString: ToString {}
/// impl MyToString for &str {}
/// impl MyToString for f32 {}
///
/// fn to_string<T: MyToString>(v: &T) -> String {
///     v.to_string()
/// }
///
/// let tup = tuple!(vec![12, 14], "hello", 3.14);
/// /* Using `ToString` here is not allowed because
///  * neither `Vec` nor `ToString` is defined in current crate,
///  * even though `Vec` does not implement `ToString`.
///  */
/// let tup2 = tup.foreach(mapper! {
///     x : Vec<i32> => i32 : x[0];
///     _ => String: to_string where MyToString
/// });
/// assert_eq!(tup2, tuple!(12, "hello".to_string(), "3.14".to_string()));
/// ```
#[macro_export]
macro_rules! mapper {
    ($($x:ident $(, $lt:lifetime)*: $it:ty $(=> $ot:ty)? : $e:expr);* $(;)?) => {{
        struct __Mapper;
        $(
            mapper!(@impl $x $(, $lt)* : $it $(=> $ot)? : $e);
        )*
        &mut __Mapper
    }};
    ($($x:ident $(, $lt:lifetime)*: $it:ty $(=> $ot:ty)? : $e:expr ;)*
        $(_ $(=> $ot2:ty)? : $f:ident $(where $($t:tt)*)?)?) => {{
        struct __Mapper;
        $(
            mapper!(@impl $x $(, $lt)* : $it $(=> $ot)? : $e);
        )*
        $(
            mapper!(@impl _ $(=> $ot2)? : $f $(where $($t)*)?);
        )?
        &mut __Mapper
    }};
    (@impl _ : $f:ident $(where $($t:tt)*)?) => {{
        impl<T $(: $($t)*)?> Mapper<T> for __Mapper
        {
            type Output = T;
            fn map(&mut self, value: &T) -> Self::Output {
                $f(value)
            }
        }
    }};
    (@impl _ => $ot:ty : $f:ident $(where $($t:tt)*)?) => {{
        impl<T$(: $($t)*)?> Mapper<T> for __Mapper
        {
            type Output = $ot;
            fn map(&mut self, value: &T) -> Self::Output {
                $f(value)
            }
        }
    }};
    (@impl $x:ident : $it:ty : $e:expr) => {
        impl Mapper<$it> for __Mapper {
            type Output = $it;
            fn map(&mut self, value: &$it) -> Self::Output {
                let f = |$x : &$it| -> $it { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident $(, $lt:lifetime)* : $it:ty : $e:expr) => {
        impl<$($lt),*> Mapper<$it> for __Mapper {
            type Output = $it;
            fn map(&mut self, value: &$it) -> Self::Output {
                let f = |$x : &$it| -> $it { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident : $it:ty => $ot:ty : $e:expr) => {
        impl Mapper<$it> for __Mapper {
            type Output = $ot;
            fn map(&mut self, value: &$it) -> Self::Output {
                let f = |$x : &$it| -> $ot { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident $(, $lt:lifetime)* : $it:ty => $ot:ty : $e:expr) => {
        impl<$($lt),*> Mapper<$it> for __Mapper {
            type Output = $ot;
            fn map(&mut self, value: &$it) -> Self::Output {
                let f = |$x : &$it| -> $ot { $e };
                f(value)
            }
        }
    };
}

/// Provides a simple way to create a functor that implements [`MapperMut`](crate::mapper::MapperMut).
///
/// # Syntax
///
/// The syntax is exactly the same as [`mapper!`](crate::mapper!). The difference is that [`mapper_mut!`](crate::mapper_mut!) passes in mutable references
/// to the elements of the tuple instead of immutable references.
///
/// # Example
///
/// ```
/// use tuplez::*;
///
/// let mut tup = tuple!(2, "hello", 3.14);
/// let tup2 = tup.foreach_mut(mapper_mut!{
///     x: i32: { (*x) *= (*x); *x - 1 };
///     x: f32 => (): *x += 1.0;
///     x, 'a: &'a str: *x
/// });
/// assert_eq!(tup, tuple!(4, "hello", 3.14 + 1.0));
/// assert_eq!(tup2, tuple!(3, "hello", ()));
/// ```
#[macro_export]
macro_rules! mapper_mut {
    ($($x:ident $(, $lt:lifetime)*: $it:ty $(=> $ot:ty)? : $e:expr);* $(;)?) => {{
        struct __MapperMut;
        $(
            mapper_mut!(@impl $x $(, $lt)* : $it $(=> $ot)? : $e);
        )*
        &mut __MapperMut
    }};
    ($($x:ident $(, $lt:lifetime)*: $it:ty $(=> $ot:ty)? : $e:expr ;)*
        $(_ $(=> $ot2:ty)? : $f:ident $(where $($t:tt)*)?)?) => {{
        struct __MapperMut;
        $(
            mapper_mut!(@impl $x $(, $lt)* : $it $(=> $ot)? : $e);
        )*
        $(
            mapper_mut!(@impl _ $(=> $ot2)? : $f $(where $($t)*)?);
        )?
        &mut __MapperMut
    }};
    (@impl _ : $f:ident $(where $($t:tt)*)?) => {{
        impl<T $(: $($t)*)?> MapperMut<T> for __MapperMut
        {
            type Output = T;
            fn map_mut(&mut self, value: &mut T) -> Self::Output {
                $f(value)
            }
        }
    }};
    (@impl _ => $ot:ty : $f:ident $(where $($t:tt)*)?) => {{
        impl<T$(: $($t)*)?> MapperMut<T> for __MapperMut
        {
            type Output = $ot;
            fn map_mut(&mut self, value: &mut T) -> Self::Output {
                $f(value)
            }
        }
    }};
    (@impl $x:ident : $it:ty : $e:expr) => {
        impl MapperMut<$it> for __MapperMut {
            type Output = $it;
            fn map_mut(&mut self, value: &mut $it) -> Self::Output {
                let f = |$x : &mut $it| -> $it { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident $(, $lt:lifetime)* : $it:ty : $e:expr) => {
        impl<$($lt),*> MapperMut<$it> for __MapperMut {
            type Output = $it;
            fn map_mut(&mut self, value: &mut $it) -> Self::Output {
                let f = |$x : &mut $it| -> $it { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident : $it:ty => $ot:ty : $e:expr) => {
        impl MapperMut<$it> for __MapperMut {
            type Output = $ot;
            fn map_mut(&mut self, value: &mut $it) -> Self::Output {
                let f = |$x : &mut $it| -> $ot { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident $(, $lt:lifetime)* : $it:ty => $ot:ty : $e:expr) => {
        impl<$($lt),*> MapperMut<$it> for __MapperMut {
            type Output = $ot;
            fn map_mut(&mut self, value: &mut $it) -> Self::Output {
                let f = |$x : &mut $it| -> $ot { $e };
                f(value)
            }
        }
    };
}

/// Provides a simple way to create a functor that implements [`MapperOnce`](crate::mapper::MapperOnce).
///
/// # Syntax
///
/// The syntax is exactly the same as [`mapper!`](crate::mapper!). The difference is that [`mapper_once!`](crate::mapper_once!) take elements of the tuple
/// instead of pass in their immutable references.
///
/// # Example
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(vec![1, 2, 3], "hello".to_string());
/// let tup2 = tup.foreach_once(mapper_once!{
///     x: Vec<i32> => Box<[i32]> : x.into();
///     x: String : x
/// });
/// // assert_eq!(tup, ... ); // No, `tup` has been moved
/// assert_eq!(
///     tup2,
///     tuple!(
///         Box::<[i32; 3]>::new([1, 2, 3]) as Box<[i32]>,
///         "hello".to_string()
///     )
/// );
/// ```
#[macro_export]
macro_rules! mapper_once {
    ($($x:ident $(, $lt:lifetime)*: $it:ty $(=> $ot:ty)? : $e:expr);* $(;)?) => {{
        struct __MapperOnce;
        $(
            mapper_once!(@impl $x $(, $lt)* : $it $(=> $ot)? : $e);
        )*
        &mut __MapperOnce
    }};
    ($($x:ident $(, $lt:lifetime)*: $it:ty $(=> $ot:ty)? : $e:expr ;)*
        $(_ $(=> $ot2:ty)? : $f:ident $(where $($t:tt)*)?)?) => {{
        struct __MapperOnce;
        $(
            mapper_once!(@impl $x $(, $lt)* : $it $(=> $ot)? : $e);
        )*
        $(
            mapper_once!(@impl _ $(=> $ot2)? : $f $(where $($t)*)?);
        )?
        &mut __MapperOnce
    }};
    (@impl _ : $f:ident $(where $($t:tt)*)?) => {{
        impl<T $(: $($t)*)?> MapperOnce<T> for __MapperOnce
        {
            type Output = T;
            fn map_once(&mut self, value: T) -> Self::Output {
                $f(value)
            }
        }
    }};
    (@impl _ => $ot:ty : $f:ident $(where $($t:tt)*)?) => {{
        impl<T$(: $($t)*)?> MapperOnce<T> for __MapperOnce
        {
            type Output = $ot;
            fn map_once(&mut self, value: T) -> Self::Output {
                $f(value)
            }
        }
    }};
    (@impl $x:ident : $it:ty : $e:expr) => {
        impl MapperOnce<$it> for __MapperOnce {
            type Output = $it;
            fn map_once(&mut self, value: $it) -> Self::Output {
                #[allow(unused_mut)]
                let f = |mut $x : $it| -> $it { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident $(, $lt:lifetime)* : $it:ty : $e:expr) => {
        impl<$($lt),*> MapperOnce<$it> for __MapperOnce {
            type Output = $it;
            fn map_once(&mut self, value: $it) -> Self::Output {
                #[allow(unused_mut)]
                let f = |mut $x : $it| -> $it { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident : $it:ty => $ot:ty : $e:expr) => {
        impl MapperOnce<$it> for __MapperOnce {
            type Output = $ot;
            fn map_once(&mut self, value: $it) -> Self::Output {
                #[allow(unused_mut)]
                let f = |mut $x : $it| -> $ot { $e };
                f(value)
            }
        }
    };
    (@impl $x:ident $(, $lt:lifetime)* : $it:ty => $ot:ty : $e:expr) => {
        impl<$($lt),*> MapperOnce<$it> for __MapperOnce {
            type Output = $ot;
            fn map_once(&mut self, value: $it) -> Self::Output {
                #[allow(unused_mut)]
                let f = |mut $x : $it| -> $ot { $e };
                f(value)
            }
        }
    };
}
