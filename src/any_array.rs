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
