macro_rules! __from_primitive {
    ($tup:ident; $($v:ident)*) => {{
        paste::paste! {
            let ($([< $v:lower >],)*) = $tup;
            $crate::tuple!($([< $v:lower  >]),*)
        }
    }};
}

macro_rules! __to_primitive {
    ($tup:ident $(;)?) => { () };
    ($tup:ident; $($v:ident)+) => {{
        paste::paste! {
            let $crate::macros::__to_primitive!(@expand $([< $v:lower >])+) = $tup;
            ($([< $v:lower >],)+)
        }
    }};
    (@expand $v:ident) => {
        $crate::Tuple($v, _)
    };
    (@expand $v:ident $($vs:ident)+) => {
        $crate::Tuple($v, $crate::macros::__to_primitive!(@expand $($vs)+))
    };
}

macro_rules! __from_array {
    ($arr:ident; $($v:ident)*) => {{
        paste::paste! {
            let [$([< $v:lower >],)*] = $arr;
            $crate::tuple!($([< $v:lower  >]),*)
        }
    }};
}

macro_rules! __to_array {
    ($tup:ident; $($v:ident)+) => {{
        paste::paste! {
            let $crate::macros::__to_primitive!(@expand $([< $v:lower >])+) = $tup;
            [ $([< $v:lower >],)+ ]
        }
    }};
    (@expand $v:ident) => {
        $crate::Tuple($v, _)
    };
    (@expand $v:ident $($vs:ident)+) => {
        $crate::Tuple($v, $crate::macros::__to_primitive!(@expand $($vs)+))
    };
}

#[cfg(not(feature = "any_array"))]
macro_rules! __tuple_array_impl {
    ($cnt:literal;) => {
        impl<T> ToArray<T> for $crate::Unit {
            type Array = [T; 0];
            type Iter<'a> = std::array::IntoIter<&'a T, 0> where Self: 'a, T: 'a;
            type IterMut<'a> = std::array::IntoIter<&'a mut T, 0> where Self: 'a, T: 'a;
            fn to_array(self) -> Self::Array {
                Default::default()
            }
            fn iter<'a>(&'a self) -> Self::Iter<'a>
            where
                Self: 'a,
                T: 'a
            {
                self.as_ref().to_array().into_iter()
            }
            fn iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
            where
                Self: 'a,
                T: 'a
            {
                self.as_mut().to_array().into_iter()
            }
        }

        impl<T> From<[T; 0]> for $crate::Unit {
            fn from(_: [T; 0]) -> Self {
                $crate::Unit
            }
        }
    };
    ($cnt:literal; $($ts:ident)+) => {
        impl<T> ToArray<T> for $crate::tuple_t!(T; $cnt) {
            type Array = [T; $cnt];
            type Iter<'a> = std::array::IntoIter<&'a T, $cnt> where Self: 'a, T: 'a;
            type IterMut<'a> = std::array::IntoIter<&'a mut T, $cnt> where Self: 'a, T: 'a;
            fn to_array(self) -> Self::Array {
                $crate::macros::__to_array!(self; $($ts)*)
            }
            fn iter<'a>(&'a self) -> Self::Iter<'a>
            where
                Self: 'a,
                T: 'a
            {
                self.as_ref().to_array().into_iter()
            }
            fn iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
            where
                Self: 'a,
                T: 'a
            {
                self.as_mut().to_array().into_iter()
            }
        }

        impl<T> From<[T; $cnt]> for $crate::tuple_t!(T; $cnt) {
            fn from(arr: [T; $cnt]) -> Self {
                $crate::macros::__from_array!(arr; $($ts)*)
            }
        }
    };
}

macro_rules! __tuple_traits_impl {
    ($cnt:literal; $($ts:ident)*) => {
        impl<$($ts),*> ToPrimitive for $crate::tuple_t!($($ts),*)
        {
            type Primitive = ($($ts,)*);
            fn primitive(self)  -> Self::Primitive {
                $crate::macros::__to_primitive!(self; $($ts)*)
            }
        }

        impl<$($ts),*> From<($($ts,)*)> for $crate::tuple_t!($($ts),*) {
            fn from(prim: ($($ts,)*)) -> Self {
                $crate::macros::__from_primitive!(prim; $($ts)*)
            }
        }

        #[cfg(not(feature = "any_array"))]
        $crate::macros::__tuple_array_impl! { $cnt; $($ts)* }
    };
}

#[cfg(not(feature = "any_array"))]
pub(crate) use __from_array;
pub(crate) use __from_primitive;
#[cfg(not(feature = "any_array"))]
pub(crate) use __to_array;
pub(crate) use __to_primitive;
#[cfg(not(feature = "any_array"))]
pub(crate) use __tuple_array_impl;
pub(crate) use __tuple_traits_impl;
