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
            Tuple<First, Other>: Cloned,
            Other: TupleLike
        {
            type Output = <Tuple<First, Other> as Cloned>::ClonedOutput;
            fn $f(self, _: Unit) -> Self::Output {
                Cloned::cloned(self)
            }
        }

        impl<First, Other> $tr<&Unit> for &Tuple<First, Other>
        where
            Tuple<First, Other>: Cloned,
            Other: TupleLike
        {
            type Output = <Tuple<First, Other> as Cloned>::ClonedOutput;
            fn $f(self, _: &Unit) -> Self::Output {
                Cloned::cloned(self)
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

#[cfg(not(feature = "any_array"))]
pub(crate) use __from_array;
pub(crate) use __from_primitive;
#[cfg(not(feature = "any_array"))]
pub(crate) use __to_array;
pub(crate) use __to_primitive;
#[cfg(not(feature = "any_array"))]
pub(crate) use __tuple_array_impl;
pub(crate) use __tuple_assignment_ops_impl;
pub(crate) use __tuple_binary_ops_impl;
pub(crate) use __tuple_traits_impl;
pub(crate) use __tuple_unary_ops_impl;
