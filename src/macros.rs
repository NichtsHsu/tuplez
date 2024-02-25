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
