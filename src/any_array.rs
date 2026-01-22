use crate::{ToArray, Tuple, TupleLike, Unit};
use std::mem::MaybeUninit;

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

impl<T> ToArray<T> for Unit {
    type Array = [T; 0];
    type Iter<'a>
        = std::array::IntoIter<&'a T, 0>
    where
        Self: 'a,
        T: 'a;
    type IterMut<'a>
        = std::array::IntoIter<&'a mut T, 0>
    where
        Self: 'a,
        T: 'a;

    fn to_array(self) -> Self::Array {
        Default::default()
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self: 'a,
        T: 'a,
    {
        self.as_ref().to_array().into_iter()
    }

    fn iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self: 'a,
        T: 'a,
    {
        self.as_mut().to_array().into_iter()
    }
}

impl<First, Other> ToArray<First> for Tuple<First, Other>
where
    Self: FillSlice<First>,
    [First; Self::LEN]:,
{
    type Array = [First; Self::LEN];

    type Iter<'a> = <<<Tuple<First, Other> as TupleLike>::AsRefOutput<'a> as
        ToArray<&'a First>>::Array as IntoIterator>::IntoIter
    where
        Self::AsRefOutput<'a>: ToArray<&'a First>,
        Self: 'a,
        First: 'a;

    type IterMut<'a> = <<<Tuple<First, Other> as TupleLike>::AsMutOutput<'a> as
        ToArray<&'a mut First>>::Array as IntoIterator>::IntoIter
    where
        Self::AsMutOutput<'a>: ToArray<&'a mut First>,
        Self: 'a,
        First: 'a;

    fn to_array(self) -> Self::Array {
        let mut arr: [MaybeUninit<First>; Self::LEN] = [const { MaybeUninit::uninit() }; Self::LEN];
        self.fill_slice(&mut arr, 0);
        unsafe { MaybeUninit::array_assume_init(arr) }
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::AsRefOutput<'a>: ToArray<&'a First>,
        Self: 'a,
        First: 'a,
    {
        self.as_ref().to_array().into_iter()
    }

    fn iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self::AsMutOutput<'a>: ToArray<&'a mut First>,
        Self: 'a,
        First: 'a,
    {
        self.as_mut().to_array().into_iter()
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
