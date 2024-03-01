//! Provides some operations between two tuples.
//!
//! The module aims to hide the implementation details, all methods are wrapped by [`TupleLike`].

use crate::{tuple, tuple_t, Tuple, TupleLike, Unit};
use std::ops::{Add, Mul};

/// Pop elements from the front and back of the tuple.
///
/// The [`Unit`] type is not [`Poppable`]. All [`Tuple`]s are [`Poppable`].
///
/// The [`take!`](crate::take!) macro provides another way to take out elements by their indices or types.
pub trait Poppable: TupleLike {
    /// The type of tuple generated by popping an element from the front of the tuple.
    type PopFrontOutput: TupleLike;

    /// The type of the element popped from the front of the tuple.
    type PopFrontElement;

    /// The type of tuple generated by popping an element from the back of the tuple.
    type PopBackOutput: TupleLike;

    /// The type of the element popped from the back of the tuple.
    type PopBackElement;

    /// Pop an element from the back of the tuple.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`pop()`](TupleLike::pop()) method as the wrapper
    /// for this [`pop()`](Poppable::pop()) method.
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
    fn pop(self) -> (Self::PopBackOutput, Self::PopBackElement);

    /// Pop an element from the front of the tuple.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`pop_front()`](TupleLike::pop_front()) method as the wrapper
    /// for this [`pop_front()`](Poppable::pop_front()) method.
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
    fn pop_front(self) -> (Self::PopFrontOutput, Self::PopFrontElement);

    /// Pop an element from the back of the tuple. Same as [`pop()`](Poppable::pop()).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`pop_back()`](TupleLike::pop_back()) method as the wrapper
    /// for this [`pop_back()`](Poppable::pop_back()) method.
    fn pop_back(self) -> (Self::PopBackOutput, Self::PopBackElement)
    where
        Self: Sized,
    {
        Poppable::pop(self)
    }
}

impl<First, Other> Poppable for Tuple<First, Other>
where
    Other: Poppable,
{
    type PopFrontOutput = Other;
    type PopFrontElement = First;
    type PopBackOutput = Tuple<First, Other::PopBackOutput>;
    type PopBackElement = Other::PopBackElement;

    fn pop(self) -> (Self::PopBackOutput, Self::PopBackElement) {
        let (tup, elem) = Poppable::pop(self.1);
        (Tuple(self.0, tup), elem)
    }

    fn pop_front(self) -> (Self::PopFrontOutput, Self::PopFrontElement) {
        (self.1, self.0)
    }
}

impl<First> Poppable for Tuple<First, Unit> {
    type PopFrontOutput = Unit;
    type PopFrontElement = First;
    type PopBackOutput = Unit;
    type PopBackElement = First;

    fn pop(self) -> (Self::PopBackOutput, Self::PopBackElement) {
        (Unit, self.0)
    }

    fn pop_front(self) -> (Self::PopFrontOutput, Self::PopFrontElement) {
        (Unit, self.0)
    }
}

/// Rotate the elements of the tuple.
pub trait Rotatable: TupleLike {
    /// The type of tuple generated by left rotating the elements of the tuple.
    type RotLeftOutput: TupleLike;

    /// The type of tuple generated by right rotating the elements of the tuple.
    type RotRightOutput: TupleLike;

    /// Left rotates the elements of the tuple.
    ///
    /// # Examples
    ///
    /// Hint: The [`TupleLike`] trait provides the [`rot_l()`](TupleLike::rot_l()) method as the wrapper
    /// for this [`rot_l()`](Rotatable::rot_l()) method.
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
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
    /// Hint: The [`TupleLike`] trait provides the [`rot_r()`](TupleLike::rot_r()) method as the wrapper
    /// for this [`rot_r()`](Rotatable::rot_r()) method.
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
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
    Self: Poppable,
{
    type RotLeftOutput = Other::PushBackOutput<First>;
    type RotRightOutput =
        Tuple<<Self as Poppable>::PopBackElement, <Self as Poppable>::PopBackOutput>;

    fn rot_l(self) -> Self::RotLeftOutput {
        let Tuple(first, other) = self;
        other.push(first)
    }

    fn rot_r(self) -> Self::RotRightOutput {
        let (out, elem) = Poppable::pop(self);
        Tuple(elem, out)
    }
}

/// Make [`tuple!(&[mut] a, &[mut] b, &[mut] c, ...)`](crate::tuple!)
/// to [`tuple!(a, b, c, ...)`](crate::tuple!) by cloning its elements.
pub trait Cloned: TupleLike {
    /// The type of the output tuple.
    type ClonedOutput: TupleLike;

    /// If the elements of the tuple are all references, clone these elements to a new tuple.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`cloned()`](TupleLike::cloned()) method as the wrapper
    /// for this [`cloned()`](Cloned::cloned()) method.
    ///
    /// # Example:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut string = String::from("hello");
    /// let tup = tuple!(&1, &mut string, &3.14);
    /// let tup2 = tup.cloned();
    /// assert_eq!(tup2, tuple!(1, String::from("hello"), 3.14));
    /// ```
    fn cloned(&self) -> Self::ClonedOutput;
}

impl Cloned for Unit {
    type ClonedOutput = Unit;
    fn cloned(&self) -> Self::ClonedOutput {
        Self
    }
}

impl<First, Other> Cloned for Tuple<&First, Other>
where
    First: Clone,
    Other: Cloned,
{
    type ClonedOutput = Tuple<First, Other::ClonedOutput>;
    fn cloned(&self) -> Self::ClonedOutput {
        Tuple(Clone::clone(self.0), Cloned::cloned(&self.1))
    }
}

impl<First, Other> Cloned for Tuple<&mut First, Other>
where
    First: Clone,
    Other: Cloned,
{
    type ClonedOutput = Tuple<First, Other::ClonedOutput>;
    fn cloned(&self) -> Self::ClonedOutput {
        Tuple(Clone::clone(self.0), Cloned::cloned(&self.1))
    }
}

/// Make [`tuple!(&[mut] a, &[mut] b, &[mut] c, ...)`](crate::tuple!) to
/// [`tuple!(a, b, c, ...)`](crate::tuple!) by cloning its elements.
///
/// Much like [`Cloned`], but allows dynamic sized types.
pub trait Owned: TupleLike {
    /// The type of the output tuple.
    type OwnedOutput: TupleLike;

    /// If the elements of the tuple are all references, clone its elements to a new tuple.
    ///
    /// Much like [`cloned()`](Cloned::cloned()), but can work on types like `&str` or slices.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`owned()`](TupleLike::owned()) method as the wrapper
    /// for this [`owned()`](Owned::owned()) method.
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
    fn owned(&self) -> Self::OwnedOutput;
}

impl Owned for Unit {
    type OwnedOutput = Unit;

    fn owned(&self) -> Self::OwnedOutput {
        Self
    }
}

impl<First, Other> Owned for Tuple<&First, Other>
where
    First: ToOwned + ?Sized,
    Other: Owned,
{
    type OwnedOutput = Tuple<First::Owned, Other::OwnedOutput>;
    fn owned(&self) -> Self::OwnedOutput {
        Tuple(ToOwned::to_owned(self.0), Owned::owned(&self.1))
    }
}

impl<First, Other> Owned for Tuple<&mut First, Other>
where
    First: ToOwned + ?Sized,
    Other: Owned,
{
    type OwnedOutput = Tuple<First::Owned, Other::OwnedOutput>;
    fn owned(&self) -> Self::OwnedOutput {
        Tuple(ToOwned::to_owned(self.0), Owned::owned(&self.1))
    }
}

/// Make [`tuple!(&[mut] a, &[mut] b, &[mut] c, ...)`](crate::tuple!) to
/// [`tuple!(a, b, c, ...)`](crate::tuple!) by copying its elements.
pub trait Copied: TupleLike {
    /// The type of the output tuple.
    type CopiedOutput: TupleLike;

    /// If the elements of the tuple are all references, copy its elements to a new tuple.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`copied()`](TupleLike::copied()) method as the wrapper
    /// for this [`copied()`](Copied::copied()) method.
    ///
    /// # Example:
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let mut ch = 'c';
    /// let tup = tuple!(&1, &mut ch, &3.14);
    /// let tup2 = tup.copied();
    /// assert_eq!(tup2, tuple!(1, 'c', 3.14));
    /// ```
    fn copied(&self) -> Self::CopiedOutput;
}

impl Copied for Unit {
    type CopiedOutput = Unit;
    fn copied(&self) -> Self::CopiedOutput {
        Self
    }
}

impl<First, Other> Copied for Tuple<&First, Other>
where
    First: Copy,
    Other: Copied,
{
    type CopiedOutput = Tuple<First, Other::CopiedOutput>;
    fn copied(&self) -> Self::CopiedOutput {
        Tuple(*self.0, Copied::copied(&self.1))
    }
}

impl<First, Other> Copied for Tuple<&mut First, Other>
where
    First: Copy,
    Other: Copied,
{
    type CopiedOutput = Tuple<First, Other::CopiedOutput>;
    fn copied(&self) -> Self::CopiedOutput {
        Tuple(*self.0, Copied::copied(&self.1))
    }
}

/// Opposite operation of [`to_tuple()`](TupleLike::to_tuple()).
pub trait Untupleable: TupleLike {
    /// The type of tuple generated by untupling the elements of the tuple.
    type UntupleOutput: TupleLike;

    /// Untuple a tuple, whose elements are all tuples with only one element.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`untuple()`](TupleLike::untuple()) method as the wrapper
    /// for this [`untuple()`](Untupleable::untuple()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup_tup = tuple!(tuple!(1), tuple!("hello"), tuple!(3.14));
    /// assert_eq!(tup_tup.untuple(), tuple!(1, "hello", 3.14));
    /// ```
    fn untuple(self) -> Self::UntupleOutput;
}

impl Untupleable for Unit {
    type UntupleOutput = Unit;

    fn untuple(self) -> Self::UntupleOutput {
        self
    }
}

impl<First, Other> Untupleable for Tuple<First, Other>
where
    First: TupleLike,
    Other: Untupleable,
{
    type UntupleOutput = First::JoinOutput<Other::UntupleOutput>;

    fn untuple(self) -> Self::UntupleOutput {
        self.0.join(Untupleable::untuple(self.1))
    }
}

/// Dot product operation.
pub trait Dot<T = Self> {
    /// Output type of the dot product operation.
    type Output;

    /// Performs the dot product operation.
    fn dot(self, rhs: T) -> Self::Output;
}

impl Dot for Unit {
    type Output = Unit;
    fn dot(self, _: Self) -> Self::Output {
        Self
    }
}

impl<First1, Other1, First2, Other2> Dot<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: Mul<First2>,
    Other1: Dot<Other2> + TupleLike,
    Other2: TupleLike,
    <Other1 as Dot<Other2>>::Output: Add<<First1 as Mul<First2>>::Output>,
{
    type Output = <<Other1 as Dot<Other2>>::Output as Add<<First1 as Mul<First2>>::Output>>::Output;
    fn dot(self, rhs: Tuple<First2, Other2>) -> Self::Output {
        Dot::dot(self.1, rhs.1) + self.0 * rhs.0
    }
}

/// Zip two tuples.
pub trait Zippable<T>: TupleLike {
    /// The type of the output generated by zipping two tuples.
    type ZipOutput: TupleLike;

    /// The type of the output generated by zipping two tuples, but elements are primitive tuples.
    type ZipOutput2: TupleLike;

    /// Zip two tuples.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`zip()`](TupleLike::zip()) method as the wrapper
    /// for this [`zip()`](Zippable::zip()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, 2.0, "3").zip(tuple!("4", 5, 6.0));
    /// assert_eq!(tup, tuple!(tuple!(1, "4"), tuple!(2.0, 5), tuple!("3", 6.0)));
    /// ```
    fn zip(self, rhs: T) -> Self::ZipOutput;

    /// Zip two tuples, but output elements are primitive tuples.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`zip2()`](TupleLike::zip2()) method as the wrapper
    /// for this [`zip2()`](Zippable::zip2()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike};
    ///
    /// let tup = tuple!(1, 2.0, "3").zip2(tuple!("4", 5, 6.0));
    /// assert_eq!(tup, tuple!((1, "4"), (2.0, 5), ("3", 6.0)));
    /// ```
    fn zip2(self, rhs: T) -> Self::ZipOutput2;
}

impl Zippable<Unit> for Unit {
    type ZipOutput = Unit;
    type ZipOutput2 = Unit;

    fn zip(self, _: Unit) -> Self::ZipOutput {
        self
    }

    fn zip2(self, _: Unit) -> Self::ZipOutput2 {
        self
    }
}

impl<First1, Other1, First2, Other2> Zippable<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    Other1: Zippable<Other2>,
    Other2: TupleLike,
{
    type ZipOutput = Tuple<tuple_t!(First1, First2), Other1::ZipOutput>;
    type ZipOutput2 = Tuple<(First1, First2), Other1::ZipOutput2>;
    fn zip(self, rhs: Tuple<First2, Other2>) -> Self::ZipOutput {
        Tuple(tuple!(self.0, rhs.0), Zippable::zip(self.1, rhs.1))
    }

    fn zip2(self, rhs: Tuple<First2, Other2>) -> Self::ZipOutput2 {
        Tuple((self.0, rhs.0), Zippable::zip2(self.1, rhs.1))
    }
}

/// Unzip a tuple to two tuples, if all elements of the tuple are tuples with two elements.
pub trait Unzippable: TupleLike {
    /// The type of the new tuple which collects all first elements of the tuple elements.
    type UnzipOutputLeft: TupleLike;

    /// The type of the new tuple which collects all second elements of the tuple elements.
    type UnzipOutputRight: TupleLike;

    /// Unzip a tuple to two tuples, if all elements of the tuple are tuples with two elements.
    /// Elements can be of [`Tuple`] type or primitive tuple type.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`unzip()`](TupleLike::unzip()) method as the wrapper
    /// for this [`unzip()`](Unzippable::unzip()) method.
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
    fn unzip(self) -> (Self::UnzipOutputLeft, Self::UnzipOutputRight);
}

impl Unzippable for Unit {
    type UnzipOutputLeft = Unit;
    type UnzipOutputRight = Unit;

    fn unzip(self) -> (Self::UnzipOutputLeft, Self::UnzipOutputRight) {
        (self, self)
    }
}

impl<FirstLeft, FirstRight, Other> Unzippable
    for Tuple<Tuple<FirstLeft, Tuple<FirstRight, Unit>>, Other>
where
    Other: Unzippable,
{
    type UnzipOutputLeft = Tuple<FirstLeft, Other::UnzipOutputLeft>;
    type UnzipOutputRight = Tuple<FirstRight, Other::UnzipOutputRight>;

    fn unzip(self) -> (Self::UnzipOutputLeft, Self::UnzipOutputRight) {
        let Tuple(left, Tuple(right, ..)) = self.0;
        let (lefts, rights) = Unzippable::unzip(self.1);
        (Tuple(left, lefts), Tuple(right, rights))
    }
}

impl<FirstLeft, FirstRight, Other> Unzippable for Tuple<(FirstLeft, FirstRight), Other>
where
    Other: Unzippable,
{
    type UnzipOutputLeft = Tuple<FirstLeft, Other::UnzipOutputLeft>;
    type UnzipOutputRight = Tuple<FirstRight, Other::UnzipOutputRight>;

    fn unzip(self) -> (Self::UnzipOutputLeft, Self::UnzipOutputRight) {
        let (left, right) = self.0;
        let (lefts, rights) = Unzippable::unzip(self.1);
        (Tuple(left, lefts), Tuple(right, rights))
    }
}

/// If the elements of a tuple are all tuples, push an element to each tuple element.
pub trait Extendable<T>: TupleLike {
    /// The type of the output generated by pushing new elements to the front of tuple elements.
    type ExtendFrontOutput: TupleLike;

    /// The type of the output generated by pushing new elements to the back of tuple elements.
    type ExtendBackOutput: TupleLike;

    /// If the elements of a tuple are all tuples, push an element to the back of each tuple element.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`extend()`](TupleLike::extend()) method as the wrapper
    /// for this [`extend()`](Extendable::extend()) method.
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
    fn extend(self, rhs: T) -> Self::ExtendBackOutput;

    /// If the elements of a tuple are all tuples, push an element to the front of each tuple element.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`extend_front()`](TupleLike::extend_front()) method as the wrapper
    /// for this [`extend_front()`](Extendable::extend_front()) method.
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
    fn extend_front(self, rhs: T) -> Self::ExtendFrontOutput;

    /// If the elements of a tuple are all tuples, push an element to the front of each tuple element.
    /// Same as [`extend()`](Extendable::extend()).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`extend_back()`](TupleLike::extend_back()) method as the wrapper
    /// for this [`extend_back()`](Extendable::extend_back()) method.
    fn extend_back(self, rhs: T) -> Self::ExtendBackOutput
    where
        Self: Sized,
    {
        Extendable::extend(self, rhs)
    }
}

impl Extendable<Unit> for Unit {
    type ExtendFrontOutput = Unit;
    type ExtendBackOutput = Unit;

    fn extend(self, _: Unit) -> Self::ExtendBackOutput {
        self
    }

    fn extend_front(self, _: Unit) -> Self::ExtendFrontOutput {
        self
    }
}

impl<First1, Other1, First2, Other2> Extendable<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: TupleLike,
    Other1: Extendable<Other2>,
{
    type ExtendFrontOutput = Tuple<First1::PushFrontOutput<First2>, Other1::ExtendFrontOutput>;
    type ExtendBackOutput = Tuple<First1::PushBackOutput<First2>, Other1::ExtendBackOutput>;

    fn extend(self, rhs: Tuple<First2, Other2>) -> Self::ExtendBackOutput {
        Tuple(self.0.push(rhs.0), Extendable::extend(self.1, rhs.1))
    }

    fn extend_front(self, rhs: Tuple<First2, Other2>) -> Self::ExtendFrontOutput {
        Tuple(
            self.0.push_front(rhs.0),
            Extendable::extend_front(self.1, rhs.1),
        )
    }
}

/// If the elements of a tuple are all tuples, pop an element from each tuple element.
pub trait Shrinkable: TupleLike {
    /// The type of the output generated by pop elements from the front of tuple elements.
    type ShrinkFrontOutput: TupleLike;

    /// The type of the tuple that collect popped elements from the front of tuple elements.
    type ShrinkFrontElements: TupleLike;

    /// The type of the output generated by pop elements from the back of tuple elements.
    type ShrinkBackOutput: TupleLike;

    /// The type of the tuple that collect popped elements from the back of tuple elements.
    type ShrinkBackElements: TupleLike;

    /// If the elements of a tuple are all tuples, pop an element from the back of each tuple element.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`shrink()`](TupleLike::shrink()) method as the wrapper
    /// for this [`shrink()`](Shrinkable::shrink()) method.
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
    fn shrink(self) -> (Self::ShrinkBackOutput, Self::ShrinkBackElements);

    /// If the elements of a tuple are all tuples, pop an element from the front of each tuple element.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`shrink_front()`](TupleLike::shrink_front()) method as the wrapper
    /// for this [`shrink_front()`](Shrinkable::shrink_front()) method.
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
    fn shrink_front(self) -> (Self::ShrinkFrontOutput, Self::ShrinkFrontElements);

    /// If the elements of a tuple are all tuples, pop an element from the back of each tuple element.
    /// Same as [`shrink()`](Shrinkable::shrink()).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`shrink_back()`](TupleLike::shrink_back()) method as the wrapper
    /// for this [`shrink_back()`](Shrinkable::shrink_back()) method.
    fn shrink_back(self) -> (Self::ShrinkBackOutput, Self::ShrinkBackElements)
    where
        Self: Sized,
    {
        Shrinkable::shrink(self)
    }
}

impl Shrinkable for Unit {
    type ShrinkFrontOutput = Unit;
    type ShrinkFrontElements = Unit;
    type ShrinkBackOutput = Unit;
    type ShrinkBackElements = Unit;

    fn shrink(self) -> (Unit, Unit) {
        (self, self)
    }
    fn shrink_front(self) -> (Self::ShrinkFrontOutput, Self::ShrinkFrontElements) {
        (self, self)
    }
}

impl<First, Other> Shrinkable for Tuple<First, Other>
where
    First: Poppable,
    Other: Shrinkable,
{
    type ShrinkFrontOutput = Tuple<First::PopFrontOutput, Other::ShrinkFrontOutput>;
    type ShrinkFrontElements = Tuple<First::PopFrontElement, Other::ShrinkFrontElements>;
    type ShrinkBackOutput = Tuple<First::PopBackOutput, Other::ShrinkBackOutput>;
    type ShrinkBackElements = Tuple<First::PopBackElement, Other::ShrinkBackElements>;

    fn shrink(self) -> (Self::ShrinkBackOutput, Self::ShrinkBackElements) {
        let (first, elem) = Poppable::pop(self.0);
        let (other, elems) = Shrinkable::shrink(self.1);
        (Tuple(first, other), Tuple(elem, elems))
    }

    fn shrink_front(self) -> (Self::ShrinkFrontOutput, Self::ShrinkFrontElements) {
        let (first, elem) = Poppable::pop_front(self.0);
        let (other, elems) = Shrinkable::shrink_front(self.1);
        (Tuple(first, other), Tuple(elem, elems))
    }
}

/// If two tuples have the same number of elements, and their elements are both tuples,
/// join their tuple elements one-to-one.
pub trait Combinable<T>: TupleLike {
    /// The type of the output generated by combine two tuples.
    type CombineOutput: TupleLike;

    /// If two tuples have the same number of elements, and their elements are both tuples,
    /// join their tuple elements one-to-one.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`combine()`](TupleLike::combine()) method as the wrapper
    /// for this [`combine()`](Combinable::combine()) method.
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
    fn combine(self, rhs: T) -> Self::CombineOutput;
}

impl Combinable<Unit> for Unit {
    type CombineOutput = Unit;

    fn combine(self, _: Unit) -> Unit {
        self
    }
}

impl<First1, Other1, First2, Other2> Combinable<Tuple<First2, Other2>> for Tuple<First1, Other1>
where
    First1: TupleLike,
    First2: TupleLike,
    Other1: Combinable<Other2>,
{
    type CombineOutput = Tuple<First1::JoinOutput<First2>, Other1::CombineOutput>;

    fn combine(self, rhs: Tuple<First2, Other2>) -> Self::CombineOutput {
        Tuple(self.0.join(rhs.0), Combinable::combine(self.1, rhs.1))
    }
}

/// replace head elements of the tuple.
pub trait HeadReplaceable<T>: TupleLike {
    /// The type of the tuple after replacing its elements.
    type ReplaceOutput: TupleLike;

    /// The type of the tuple that collect all replaced elements.
    type Replaced: TupleLike;

    /// Replace the first N elements of the tuple with all elements of another tuple of N elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`replace_head()`](TupleLike::replace_head()) method as the wrapper
    /// for this [`replace_head()`](HeadReplaceable::replace_head()) method.
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
    fn replace_head(self, rhs: T) -> (Self::ReplaceOutput, Self::Replaced);
}

impl<T> HeadReplaceable<Unit> for T
where
    Self: TupleLike,
{
    type ReplaceOutput = Self;
    type Replaced = Unit;
    fn replace_head(self, rhs: Unit) -> (Self::ReplaceOutput, Self::Replaced) {
        (self, rhs)
    }
}

impl<First1, Other1, First2, Other2> HeadReplaceable<Tuple<First2, Other2>>
    for Tuple<First1, Other1>
where
    Other1: HeadReplaceable<Other2>,
{
    type ReplaceOutput = Tuple<First2, Other1::ReplaceOutput>;
    type Replaced = Tuple<First1, Other1::Replaced>;
    fn replace_head(self, rhs: Tuple<First2, Other2>) -> (Self::ReplaceOutput, Self::Replaced) {
        let (output, replaced) = HeadReplaceable::replace_head(self.1, rhs.1);
        (Tuple(rhs.0, output), Tuple(self.0, replaced))
    }
}

/// Helper class that indicates types implemented [`Clone`].
pub struct PhantomClone;

/// Helper class that indicates mutable references.
pub struct PhantomMut;

/// When all elements implement [`Fn(T)`](std::ops::Fn) for a specific `T`, call them once in sequence.
pub trait Callable<T, P>: TupleLike {
    /// Type of the tuple collecting results of each call.
    type Output: TupleLike;

    /// When all elements of the tuple implement [`Fn(T)`](std::ops::Fn) for a specific `T`,
    /// call them once in sequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`call()`](TupleLike::call()) method as the wrapper
    /// for this [`call()`](Callable::call()) method.
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
    fn call(&self, rhs: T) -> Self::Output;
}

impl<T, P> Callable<T, P> for Unit {
    type Output = Unit;
    fn call(&self, _: T) -> Self::Output {
        Unit
    }
}

impl<T, R, First, Other> Callable<T, PhantomClone> for Tuple<First, Other>
where
    T: Clone,
    First: Fn(T) -> R,
    Other: Callable<T, PhantomClone>,
{
    type Output = Tuple<R, Other::Output>;
    fn call(&self, rhs: T) -> Self::Output {
        Tuple((self.0)(rhs.clone()), Callable::call(&self.1, rhs))
    }
}

impl<'a, T, R, First, Other> Callable<&'a mut T, PhantomMut> for Tuple<First, Other>
where
    First: Fn(&mut T) -> R,
    R: 'a,
    Other: Callable<&'a mut T, PhantomMut>,
{
    type Output = Tuple<R, <Other as Callable<&'a mut T, PhantomMut>>::Output>;
    fn call(&self, rhs: &'a mut T) -> Self::Output {
        Tuple((self.0)(&mut *rhs), Callable::call(&self.1, &mut *rhs))
    }
}

/// When all elements implement [`FnMut(T)`](std::ops::FnMut) for a specific `T`, call them once in sequence.
pub trait MutCallable<T, P>: TupleLike {
    /// Type of the tuple collecting results of each call.
    type Output: TupleLike;

    /// When all elements of the tuple implement [`FnMut(T)`](std::ops::FnMut) for a specific `T`,
    /// call them once in sequence.
    ///
    /// Basically the same as [`call()`](Callable::call()), but elements are required to implement
    /// [`FnMut(T)`](std::ops::FnMut) instead of [`Fn(T)`](std::ops::Fn).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`call_mut()`](TupleLike::call_mut()) method as the wrapper
    /// for this [`call_mut()`](MutCallable::call_mut()) method.
    fn call_mut(&mut self, rhs: T) -> Self::Output;
}

impl<T, P> MutCallable<T, P> for Unit {
    type Output = Unit;
    fn call_mut(&mut self, _: T) -> Self::Output {
        Unit
    }
}

impl<T, R, First, Other> MutCallable<T, PhantomClone> for Tuple<First, Other>
where
    T: Clone,
    First: FnMut(T) -> R,
    Other: MutCallable<T, PhantomClone>,
{
    type Output = Tuple<R, Other::Output>;
    fn call_mut(&mut self, rhs: T) -> Self::Output {
        Tuple(
            (self.0)(rhs.clone()),
            MutCallable::call_mut(&mut self.1, rhs),
        )
    }
}

impl<'a, T, R, First, Other> MutCallable<&'a mut T, PhantomMut> for Tuple<First, Other>
where
    First: FnMut(&mut T) -> R,
    R: 'a,
    Other: MutCallable<&'a mut T, PhantomMut>,
{
    type Output = Tuple<R, <Other as MutCallable<&'a mut T, PhantomMut>>::Output>;
    fn call_mut(&mut self, rhs: &'a mut T) -> Self::Output {
        Tuple(
            (self.0)(&mut *rhs),
            MutCallable::call_mut(&mut self.1, &mut *rhs),
        )
    }
}

/// When all elements implement [`FnOnce(T)`](std::ops::FnOnce) for a specific `T`, call them once in sequence.
pub trait OnceCallable<T, P>: TupleLike {
    /// Type of the tuple collecting results of each call.
    type Output: TupleLike;

    /// When all elements of the tuple implement [`FnOnce(T)`](std::ops::FnOnce) for a specific `T`,
    /// call them once in sequence.
    ///
    /// Basically the same as [`call()`](Callable::call()), but elements are required to implement
    /// [`FnOnce(T)`](std::ops::FnOnce) instead of [`Fn(T)`](std::ops::Fn).
    ///
    /// Hint: The [`TupleLike`] trait provides the [`call_once()`](TupleLike::call_once()) method as the wrapper
    /// for this [`call_once()`](OnceCallable::call_once()) method.
    fn call_once(self, rhs: T) -> Self::Output;
}

impl<T, P> OnceCallable<T, P> for Unit {
    type Output = Unit;
    fn call_once(self, _: T) -> Self::Output {
        Unit
    }
}

impl<T, R, First, Other> OnceCallable<T, PhantomClone> for Tuple<First, Other>
where
    T: Clone,
    First: FnOnce(T) -> R,
    Other: OnceCallable<T, PhantomClone>,
{
    type Output = Tuple<R, Other::Output>;
    fn call_once(self, rhs: T) -> Self::Output {
        Tuple((self.0)(rhs.clone()), OnceCallable::call_once(self.1, rhs))
    }
}

impl<'a, T, R, First, Other> OnceCallable<&'a mut T, PhantomMut> for Tuple<First, Other>
where
    First: FnOnce(&mut T) -> R,
    R: 'a,
    Other: OnceCallable<&'a mut T, PhantomMut>,
{
    type Output = Tuple<R, <Other as OnceCallable<&'a mut T, PhantomMut>>::Output>;
    fn call_once(self, rhs: &'a mut T) -> Self::Output {
        Tuple(
            (self.0)(&mut *rhs),
            OnceCallable::call_once(self.1, &mut *rhs),
        )
    }
}
