//! Provide operations on tuples consisting of [`MaybeUninit`] elements.

use crate::{search::*, Tuple, TupleLike, Unit};
use std::mem::MaybeUninit;

/// Provide operations on tuples consisting of [`MaybeUninit`] elements.
pub trait Uninit: TupleLike {
    type Initialized: TupleLike;

    /// Extract the values from a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init()`](TupleLike::uninit_assume_init())
    /// method as the wrapper for this [`assume_init()`](Uninit::assume_init()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init()`](MaybeUninit::assume_init()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write(12);
    /// uninit.uninit_write(true);
    /// uninit.uninit_write("hello");
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    unsafe fn assume_init(self) -> Self::Initialized;

    /// Read the values from a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init_read()`](TupleLike::uninit_assume_init_read())
    /// method as the wrapper for this [`assume_init_read()`](Uninit::assume_init_read()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_read()`](MaybeUninit::assume_init_read()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Option<Vec<u32>>)>::uninit();
    /// uninit.uninit_write(12);
    /// uninit.uninit_write(None);
    /// let tup1 = unsafe { uninit.uninit_assume_init_read() };
    /// // SAFETY: `i32` implements `Copy`, duplicating a `None` value is safe.
    /// let tup2 = unsafe { uninit.uninit_assume_init_read() };
    /// assert_eq!(tup1, tup2);
    /// ```
    unsafe fn assume_init_read(&self) -> Self::Initialized;

    /// Get immutable references to values from a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init_ref()`](TupleLike::uninit_assume_init_ref())
    /// method as the wrapper for this [`assume_init_ref()`](Uninit::assume_init_ref()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_ref()`](MaybeUninit::assume_init_ref()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write(12);
    /// uninit.uninit_write(vec![1, 2, 3]);
    /// let tup_ref = unsafe { uninit.uninit_assume_init_ref() };
    /// assert_eq!(get!(tup_ref; 0), &12);
    /// assert_eq!(get!(tup_ref; 1), &vec![1, 2, 3]);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    unsafe fn assume_init_ref(&self) -> <Self::Initialized as TupleLike>::AsRefOutput<'_>;

    /// Get mutable references to values from a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init_mut()`](TupleLike::uninit_assume_init_mut())
    /// method as the wrapper for this [`assume_init_mut()`](Uninit::assume_init_mut()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_mut()`](MaybeUninit::assume_init_mut()).
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write(12);
    /// uninit.uninit_write(vec![1, 2, 3]);
    /// let tup_mut = unsafe { uninit.uninit_assume_init_mut() };
    /// *get!(tup_mut; 0) += 1;
    /// get!(tup_mut; 1).push(4);
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(13, vec![1, 2, 3, 4]));
    /// ```
    unsafe fn assume_init_mut(&mut self) -> <Self::Initialized as TupleLike>::AsMutOutput<'_>;

    /// Drop values in place for a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init_drop()`](TupleLike::uninit_assume_init_drop())
    /// method as the wrapper for this [`assume_init_drop()`](Uninit::assume_init_drop()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_drop()`](MaybeUninit::assume_init_drop()).
    unsafe fn assume_init_drop(&mut self);

    /// Get points to values from a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_as_ptr()`](TupleLike::uninit_as_ptr())
    /// method as the wrapper for this [`as_ptr()`](Uninit::as_ptr()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write(12);
    /// uninit.uninit_write(vec![1, 2, 3]);
    /// let v = unsafe { &*get!(uninit.uninit_as_ptr(); 1) };
    /// assert_eq!(v.len(), 3);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    fn as_ptr(&self) -> <Self::Initialized as TupleLike>::AsPtrOutput;

    /// Get mutable points to values from a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_as_mut_ptr()`](TupleLike::uninit_as_mut_ptr())
    /// method as the wrapper for this [`as_mut_ptr()`](Uninit::as_mut_ptr()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{get, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, Vec<i32>)>::uninit();
    /// uninit.uninit_write(12);
    /// uninit.uninit_write(vec![1, 2, 3]);
    /// let v = unsafe { &mut *get!(uninit.uninit_as_mut_ptr(); 1) };
    /// v.push(4);
    /// assert_eq!(v.len(), 4);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    fn as_mut_ptr(&mut self) -> <Self::Initialized as TupleLike>::AsMutPtrOutput;

    /// Set value to a specific [`MaybeUninit`] element in a tuple.
    ///
    /// **NOTE**: The type of this element must exist only once in the tuple.
    ///
    /// Similar to [`MaybeUninit::write()`](MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_write()`](TupleLike::uninit_write())
    /// method as the wrapper for this [`write()`](Uninit::write()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write(12);
    /// uninit.uninit_write(true);
    /// uninit.uninit_write("hello");
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    fn write<T, I>(&mut self, value: T) -> &mut T
    where
        Self: Search<MaybeUninit<T>, I>;

    /// Set values to a tuple consisting of [`MaybeUninit`] elements.
    ///
    /// Similar to [`MaybeUninit::write()`](MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_write_all()`](TupleLike::uninit_write_all())
    /// method as the wrapper for this [`write_all()`](Uninit::write_all()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write_all(tuple!(12, true, "hello"));
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    fn write_all(
        &mut self,
        init: Self::Initialized,
    ) -> <Self::Initialized as TupleLike>::AsMutOutput<'_>;
}

impl Uninit for Unit {
    type Initialized = Unit;

    unsafe fn assume_init(self) -> Self::Initialized {
        self
    }

    unsafe fn assume_init_read(&self) -> Self::Initialized {
        Unit
    }

    unsafe fn assume_init_ref(&self) -> <Self::Initialized as TupleLike>::AsRefOutput<'_> {
        Unit
    }

    unsafe fn assume_init_mut(&mut self) -> <Self::Initialized as TupleLike>::AsMutOutput<'_> {
        Unit
    }

    unsafe fn assume_init_drop(&mut self) {}

    fn as_ptr(&self) -> <Self::Initialized as TupleLike>::AsPtrOutput {
        Unit
    }

    fn as_mut_ptr(&mut self) -> <Self::Initialized as TupleLike>::AsMutPtrOutput {
        Unit
    }

    fn write<T, I>(&mut self, _: T) -> &mut T
    where
        Self: Search<MaybeUninit<T>, I>,
    {
        unreachable!()
    }

    fn write_all(
        &mut self,
        _: Self::Initialized,
    ) -> <Self::Initialized as TupleLike>::AsMutOutput<'_> {
        Unit
    }
}

impl<First, Other> Uninit for Tuple<MaybeUninit<First>, Other>
where
    Other: Uninit,
{
    type Initialized = Tuple<First, Other::Initialized>;

    unsafe fn assume_init(self) -> Self::Initialized {
        Tuple(self.0.assume_init(), Uninit::assume_init(self.1))
    }

    unsafe fn assume_init_read(&self) -> Self::Initialized {
        Tuple(self.0.assume_init_read(), Uninit::assume_init_read(&self.1))
    }

    unsafe fn assume_init_ref(&self) -> <Self::Initialized as TupleLike>::AsRefOutput<'_> {
        Tuple(self.0.assume_init_ref(), Uninit::assume_init_ref(&self.1))
    }

    unsafe fn assume_init_mut(&mut self) -> <Self::Initialized as TupleLike>::AsMutOutput<'_> {
        Tuple(
            self.0.assume_init_mut(),
            Uninit::assume_init_mut(&mut self.1),
        )
    }

    unsafe fn assume_init_drop(&mut self) {
        self.0.assume_init_drop();
        Uninit::assume_init_drop(&mut self.1);
    }

    fn as_ptr(&self) -> <Self::Initialized as TupleLike>::AsPtrOutput {
        Tuple(self.0.as_ptr(), Uninit::as_ptr(&self.1))
    }

    fn as_mut_ptr(&mut self) -> <Self::Initialized as TupleLike>::AsMutPtrOutput {
        Tuple(self.0.as_mut_ptr(), Uninit::as_mut_ptr(&mut self.1))
    }

    fn write<T, I>(&mut self, value: T) -> &mut T
    where
        Self: Search<MaybeUninit<T>, I>,
    {
        Search::get_mut(self).write(value)
    }

    fn write_all(
        &mut self,
        init: Self::Initialized,
    ) -> <Self::Initialized as TupleLike>::AsMutOutput<'_> {
        Tuple(self.0.write(init.0), Uninit::write_all(&mut self.1, init.1))
    }
}

/// Provide subsequence operations on tuples consisting of [`MaybeUninit`] elements.
pub trait UninitSubseq<Seq, I>: Uninit + Subseq<Seq::Uninit, I>
where
    Seq: TupleLike,
{
    /// Set values to a subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Similar to [`MaybeUninit::write()`](MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_write_subseq()`](TupleLike::uninit_write_subseq())
    /// method as the wrapper for this [`write_subseq()`](UninitSubseq::write_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write(true);
    /// uninit.uninit_write_subseq(tuple!(12, "hello"));
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    fn write_subseq(&mut self, subseq: Seq) -> Seq::AsMutOutput<'_>;

    /// Drop values in place for a subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init_drop_subseq()`](TupleLike::uninit_assume_init_drop_subseq())
    /// method as the wrapper for this [`assume_init_drop_subseq()`](UninitSubseq::assume_init_drop_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_drop()`](MaybeUninit::assume_init_drop()).
    unsafe fn assume_init_drop_subseq(&mut self);
}

impl UninitSubseq<Unit, Complete> for Unit {
    fn write_subseq(&mut self, _: Unit) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }

    unsafe fn assume_init_drop_subseq(&mut self) {}
}

impl<First, Other1, Other2, I> UninitSubseq<Tuple<First, Other2>, Used<I>>
    for Tuple<MaybeUninit<First>, Other1>
where
    Other2: TupleLike,
    Other1: UninitSubseq<Other2, I>,
{
    fn write_subseq(
        &mut self,
        subseq: Tuple<First, Other2>,
    ) -> <Tuple<First, Other2> as TupleLike>::AsMutOutput<'_> {
        Tuple(
            self.0.write(subseq.0),
            UninitSubseq::write_subseq(&mut self.1, subseq.1),
        )
    }

    unsafe fn assume_init_drop_subseq(&mut self) {
        self.0.assume_init_drop();
        UninitSubseq::assume_init_drop_subseq(&mut self.1);
    }
}

impl<First, Other, T, I> UninitSubseq<T, Unused<I>> for Tuple<MaybeUninit<First>, Other>
where
    T: TupleLike,
    Other: TupleLike + UninitSubseq<T, I>,
{
    fn write_subseq(&mut self, subseq: T) -> <T as TupleLike>::AsMutOutput<'_> {
        UninitSubseq::write_subseq(&mut self.1, subseq)
    }

    unsafe fn assume_init_drop_subseq(&mut self) {
        UninitSubseq::assume_init_drop_subseq(&mut self.1);
    }
}

/// Provide contiguous subsequence operations on tuples consisting of [`MaybeUninit`] elements.
pub trait UninitConSubseq<Seq, I>: Uninit + ConSubseq<Seq::Uninit, I>
where
    Seq: TupleLike,
{
    /// Set values to a contiguous subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// Similar to [`MaybeUninit::write()`](MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_write_con_subseq()`](TupleLike::uninit_write_con_subseq())
    /// method as the wrapper for this [`write_con_subseq()`](UninitConSubseq::write_con_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write(true);
    /// uninit.uninit_write_subseq(tuple!(12, "hello"));
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    fn write_con_subseq(&mut self, subseq: Seq) -> Seq::AsMutOutput<'_>;

    /// Drop values in place for a contiguous subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// **NOTE**: The contiguous subsequence must have one and only one candidate in the supersequence.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init_drop_con_subseq()`](TupleLike::uninit_assume_init_drop_con_subseq())
    /// method as the wrapper for this [`assume_init_drop_con_subseq()`](UninitConSubseq::assume_init_drop_con_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_drop()`](MaybeUninit::assume_init_drop()).
    unsafe fn assume_init_drop_con_subseq(&mut self);
}

impl UninitConSubseq<Unit, Complete> for Unit {
    fn write_con_subseq(&mut self, _: Unit) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }

    unsafe fn assume_init_drop_con_subseq(&mut self) {}
}

impl<First, Other, T, I> UninitConSubseq<T, Unused<I>> for Tuple<MaybeUninit<First>, Other>
where
    T: TupleLike,
    Other: UninitConSubseq<T, I>,
{
    fn write_con_subseq(&mut self, subseq: T) -> <T as TupleLike>::AsMutOutput<'_> {
        UninitConSubseq::write_con_subseq(&mut self.1, subseq)
    }

    unsafe fn assume_init_drop_con_subseq(&mut self) {
        UninitConSubseq::assume_init_drop_con_subseq(&mut self.1);
    }
}

impl<First, Other, I> UninitConSubseq<Tuple<First, Unit>, Used<I>>
    for Tuple<MaybeUninit<First>, Other>
where
    Other: UninitConSubseq<Unit, I>,
{
    fn write_con_subseq(
        &mut self,
        subseq: Tuple<First, Unit>,
    ) -> <Tuple<First, Unit> as TupleLike>::AsMutOutput<'_> {
        Tuple(self.0.write(subseq.0), Unit)
    }

    unsafe fn assume_init_drop_con_subseq(&mut self) {
        self.0.assume_init_drop();
    }
}

impl<First1, First2, Other1, Other2, I>
    UninitConSubseq<Tuple<First1, Tuple<First2, Other2>>, Used<I>>
    for Tuple<MaybeUninit<First1>, Other1>
where
    Other1: UninitConSubseq<Tuple<First2, Other2>, Used<I>>,
    Other2: TupleLike,
{
    fn write_con_subseq(
        &mut self,
        subseq: Tuple<First1, Tuple<First2, Other2>>,
    ) -> <Tuple<First1, Tuple<First2, Other2>> as TupleLike>::AsMutOutput<'_> {
        Tuple(
            self.0.write(subseq.0),
            UninitConSubseq::write_con_subseq(&mut self.1, subseq.1),
        )
    }

    unsafe fn assume_init_drop_con_subseq(&mut self) {
        self.0.assume_init_drop();
        UninitConSubseq::assume_init_drop_con_subseq(&mut self.1);
    }
}
