//! Provide operations on tuples consisting of [`MaybeUninit`] elements.

use crate::{search::*, Tuple, TupleLike, Unit};
use std::mem::MaybeUninit;

/// Provide operations on tuples consisting of [`MaybeUninit`] elements.
pub trait Uninit: TupleLike {
    /// The type of the tuple consisting of values of each [`MaybeUninit`] elements.
    type Initialized: TupleLike;

    /// Extract the values of a tuple consisting of [`MaybeUninit`] elements.
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
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(true);
    /// uninit.uninit_write_one("hello");
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    unsafe fn assume_init(self) -> Self::Initialized;

    /// Read the values of a tuple consisting of [`MaybeUninit`] elements.
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
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(None);
    /// let tup1 = unsafe { uninit.uninit_assume_init_read() };
    /// // SAFETY: `i32` implements `Copy`, duplicating a `None` value is safe.
    /// let tup2 = unsafe { uninit.uninit_assume_init_read() };
    /// assert_eq!(tup1, tup2);
    /// ```
    unsafe fn assume_init_read(&self) -> Self::Initialized;

    /// Get immutable references to values of a tuple consisting of [`MaybeUninit`] elements.
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
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
    /// let tup_ref = unsafe { uninit.uninit_assume_init_ref() };
    /// assert_eq!(get!(tup_ref; 0), &12);
    /// assert_eq!(get!(tup_ref; 1), &vec![1, 2, 3]);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    unsafe fn assume_init_ref(&self) -> <Self::Initialized as TupleLike>::AsRefOutput<'_>;

    /// Get mutable references to values of a tuple consisting of [`MaybeUninit`] elements.
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
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
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

    /// Get points to values of a tuple consisting of [`MaybeUninit`] elements.
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
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
    /// let v = unsafe { &*get!(uninit.uninit_as_ptr(); 1) };
    /// assert_eq!(v.len(), 3);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    fn as_ptr(&self) -> <Self::Initialized as TupleLike>::AsPtrOutput;

    /// Get mutable points to values of a tuple consisting of [`MaybeUninit`] elements.
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
    /// uninit.uninit_write_one(12);
    /// uninit.uninit_write_one(vec![1, 2, 3]);
    /// let v = unsafe { &mut *get!(uninit.uninit_as_mut_ptr(); 1) };
    /// v.push(4);
    /// assert_eq!(v.len(), 4);
    /// unsafe { uninit.uninit_assume_init_drop(); }
    /// ```
    fn as_mut_ptr(&mut self) -> <Self::Initialized as TupleLike>::AsMutPtrOutput;

    /// Set values to a tuple consisting of [`MaybeUninit`] elements.
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
    /// uninit.uninit_write(tuple!(12, true, "hello"));
    /// let tup = unsafe { uninit.uninit_assume_init() };
    /// assert_eq!(tup, tuple!(12, true, "hello"));
    /// ```
    fn write(
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

    fn write(&mut self, _: Self::Initialized) -> <Self::Initialized as TupleLike>::AsMutOutput<'_> {
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

    fn write(
        &mut self,
        init: Self::Initialized,
    ) -> <Self::Initialized as TupleLike>::AsMutOutput<'_> {
        Tuple(self.0.write(init.0), Uninit::write(&mut self.1, init.1))
    }
}

/// Provide subsequence operations on tuples consisting of [`MaybeUninit`] elements.
pub trait UninitSubseq<Seq, I>: Subseq<Seq::Uninit, I>
where
    Seq: TupleLike,
{
    /// The type of tuple consisting of elements not in the subsequence and
    /// values of each [`MaybeUninit`] elements in the subsequence.
    type PartiallyInitialized;

    /// Extract values of a specific subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_assume_init_subseq()`](TupleLike::uninit_assume_init_subseq())
    /// method as the wrapper for this [`assume_init_subseq()`](UninitSubseq::assume_init_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init()`](MaybeUninit::assume_init()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let part_init = unsafe {
    ///     tup.uninit_assume_init_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(get!(part_init; 1), 0);
    /// assert_eq!(get!(part_init; 3), vec![1, 2, 3]);
    /// let _: tuple_t!(i32, i32, MaybeUninit<&str>, Vec<i32>, bool) = part_init;
    /// ```
    unsafe fn assume_init_subseq(self) -> Self::PartiallyInitialized;

    /// Read the values of a specific subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_assume_init_read_subseq()`](TupleLike::uninit_assume_init_read_subseq())
    /// method as the wrapper for this [`assume_init_read_subseq()`](UninitSubseq::assume_init_read_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_read()`](MaybeUninit::assume_init_read()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited = unsafe {
    ///     tup.uninit_assume_init_read_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited, tuple!(0, vec![1, 2, 3]));
    /// ```
    unsafe fn assume_init_read_subseq(&self) -> Seq;

    /// Get immutable references to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_assume_init_ref_subseq()`](TupleLike::uninit_assume_init_ref_subseq())
    /// method as the wrapper for this [`assume_init_ref_subseq()`](UninitSubseq::assume_init_ref_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_ref()`](MaybeUninit::assume_init_ref()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ref = unsafe {
    ///     tup.uninit_assume_init_ref_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited_ref, tuple!(&0, &vec![1, 2, 3]));
    /// unsafe { tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    unsafe fn assume_init_ref_subseq(&self) -> <Seq as TupleLike>::AsRefOutput<'_>;

    /// Get mutable references to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_assume_init_mut_subseq()`](TupleLike::uninit_assume_init_mut_subseq())
    /// method as the wrapper for this [`assume_init_mut_subseq()`](UninitSubseq::assume_init_mut_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_mut()`](MaybeUninit::assume_init_mut()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_mut = unsafe {
    ///     tup.uninit_assume_init_mut_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// *get!(inited_mut; 0) += 1;
    /// get!(inited_mut; 1).push(4);
    /// assert_eq!(inited_mut, tuple!(&mut 1, &mut vec![1, 2, 3, 4]));
    /// unsafe { tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    unsafe fn assume_init_mut_subseq(&mut self) -> <Seq as TupleLike>::AsMutOutput<'_>;

    /// Get pointers to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`uninit_subseq_as_ptr()`](TupleLike::uninit_subseq_as_ptr())
    /// method as the wrapper for this [`subseq_as_ptr()`](UninitSubseq::subseq_as_ptr()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_subseq_as_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     assert_eq!(*get!(inited_ptr; 0), 0);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3]);
    ///     tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    fn subseq_as_ptr(&self) -> <Seq as TupleLike>::AsPtrOutput;

    /// Get mutable pointers to values of a specific subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_subseq_as_mut_ptr()`](TupleLike::uninit_subseq_as_mut_ptr())
    /// method as the wrapper for this [`subseq_as_mut_ptr()`](UninitSubseq::subseq_as_mut_ptr()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<&str>::uninit(),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_subseq_as_mut_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     *get!(inited_ptr; 0) += 1;
    ///     (*get!(inited_ptr; 1)).push(4);
    ///     assert_eq!(*get!(inited_ptr; 0), 1);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3, 4]);
    ///     tup.uninit_assume_init_drop_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    fn subseq_as_mut_ptr(&mut self) -> <Seq as TupleLike>::AsMutPtrOutput;

    /// Set values to a subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// **NOTE**: The subsequence must have one and only one candidate in the supersequence.
    ///
    /// Similar to [`MaybeUninit::write()`](MaybeUninit::write()),
    /// this overwrites any previous value without dropping it.
    ///Hint: The [`TupleLike`] trait provides the [`uninit_write_subseq()`](TupleLike::uninit_write_subseq())
    /// method as the wrapper for this [`write_subseq()`](UninitSubseq::write_subseq()) method.
    /// Hint: The [`TupleLike`] trait provides the [`uninit_write_subseq()`](TupleLike::uninit_write_subseq())
    /// method as the wrapper for this [`write_subseq()`](UninitSubseq::write_subseq()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut uninit = <tuple_t!(i32, bool, &str)>::uninit();
    /// uninit.uninit_write_one(true);
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
    type PartiallyInitialized = Unit;

    unsafe fn assume_init_subseq(self) -> Self::PartiallyInitialized {
        Unit
    }

    unsafe fn assume_init_read_subseq(&self) -> Unit {
        Unit
    }

    unsafe fn assume_init_ref_subseq(&self) -> <Unit as TupleLike>::AsRefOutput<'_> {
        Unit
    }

    unsafe fn assume_init_mut_subseq(&mut self) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }

    fn subseq_as_ptr(&self) -> <Unit as TupleLike>::AsPtrOutput {
        Unit
    }

    fn subseq_as_mut_ptr(&mut self) -> <Unit as TupleLike>::AsMutPtrOutput {
        Unit
    }

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
    type PartiallyInitialized = Tuple<First, Other1::PartiallyInitialized>;

    unsafe fn assume_init_subseq(self) -> Self::PartiallyInitialized {
        Tuple(
            self.0.assume_init(),
            UninitSubseq::assume_init_subseq(self.1),
        )
    }

    unsafe fn assume_init_read_subseq(&self) -> Tuple<First, Other2> {
        Tuple(
            self.0.assume_init_read(),
            UninitSubseq::assume_init_read_subseq(&self.1),
        )
    }

    unsafe fn assume_init_ref_subseq(
        &self,
    ) -> <Tuple<First, Other2> as TupleLike>::AsRefOutput<'_> {
        Tuple(
            self.0.assume_init_ref(),
            UninitSubseq::assume_init_ref_subseq(&self.1),
        )
    }

    unsafe fn assume_init_mut_subseq(
        &mut self,
    ) -> <Tuple<First, Other2> as TupleLike>::AsMutOutput<'_> {
        Tuple(
            self.0.assume_init_mut(),
            UninitSubseq::assume_init_mut_subseq(&mut self.1),
        )
    }

    fn subseq_as_ptr(&self) -> <Tuple<First, Other2> as TupleLike>::AsPtrOutput {
        Tuple(self.0.as_ptr(), UninitSubseq::subseq_as_ptr(&self.1))
    }

    fn subseq_as_mut_ptr(&mut self) -> <Tuple<First, Other2> as TupleLike>::AsMutPtrOutput {
        Tuple(
            self.0.as_mut_ptr(),
            UninitSubseq::subseq_as_mut_ptr(&mut self.1),
        )
    }

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

impl<First, Other, T, I> UninitSubseq<T, Unused<I>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: TupleLike + UninitSubseq<T, I>,
{
    type PartiallyInitialized = Tuple<First, Other::PartiallyInitialized>;

    unsafe fn assume_init_subseq(self) -> Self::PartiallyInitialized {
        Tuple(self.0, UninitSubseq::assume_init_subseq(self.1))
    }

    unsafe fn assume_init_read_subseq(&self) -> T {
        UninitSubseq::assume_init_read_subseq(&self.1)
    }

    unsafe fn assume_init_ref_subseq(&self) -> <T as TupleLike>::AsRefOutput<'_> {
        UninitSubseq::assume_init_ref_subseq(&self.1)
    }

    unsafe fn assume_init_mut_subseq(&mut self) -> <T as TupleLike>::AsMutOutput<'_> {
        UninitSubseq::assume_init_mut_subseq(&mut self.1)
    }

    fn subseq_as_ptr(&self) -> <T as TupleLike>::AsPtrOutput {
        UninitSubseq::subseq_as_ptr(&self.1)
    }

    fn subseq_as_mut_ptr(&mut self) -> <T as TupleLike>::AsMutPtrOutput {
        UninitSubseq::subseq_as_mut_ptr(&mut self.1)
    }

    fn write_subseq(&mut self, subseq: T) -> <T as TupleLike>::AsMutOutput<'_> {
        UninitSubseq::write_subseq(&mut self.1, subseq)
    }

    unsafe fn assume_init_drop_subseq(&mut self) {
        UninitSubseq::assume_init_drop_subseq(&mut self.1);
    }
}

/// Provide contiguous subsequence operations on tuples consisting of [`MaybeUninit`] elements.
pub trait UninitConSubseq<Seq, I>: ConSubseq<Seq::Uninit, I>
where
    Seq: TupleLike,
{
    /// The type of tuple consisting of elements not in the contiguous subsequence and
    /// values of each [`MaybeUninit`] elements in the contiguous subsequence.
    type PartiallyInitialized;

    /// Extract values of a specific contiguous subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_assume_init_con_subseq()`](TupleLike::uninit_assume_init_con_subseq()) method as
    /// the wrapper for this [`assume_init_con_subseq()`](UninitConSubseq::assume_init_con_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init()`](MaybeUninit::assume_init()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let part_init = unsafe {
    ///     tup.uninit_assume_init_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(get!(part_init; 2), 13);
    /// assert_eq!(get!(part_init; 3), vec![1, 2, 3]);
    /// let _: tuple_t!(i32, MaybeUninit<i32>, i32, Vec<i32>, bool) = part_init;
    /// ```
    unsafe fn assume_init_con_subseq(self) -> Self::PartiallyInitialized;

    /// Read the values of a specific contiguous subsequence consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_assume_init_read_con_subseq()`](TupleLike::uninit_assume_init_read_con_subseq()) method as
    /// the wrapper for this [`assume_init_read_con_subseq()`](UninitConSubseq::assume_init_read_con_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_read()`](MaybeUninit::assume_init_read()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited = unsafe {
    ///     tup.uninit_assume_init_read_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited, tuple!(13, vec![1, 2, 3]));
    /// ```
    unsafe fn assume_init_read_con_subseq(&self) -> Seq;

    /// Get immutable references to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_assume_init_ref_con_subseq()`](TupleLike::uninit_assume_init_ref_con_subseq()) method as
    /// the wrapper for this [`assume_init_ref_con_subseq()`](UninitConSubseq::assume_init_ref_con_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_ref()`](MaybeUninit::assume_init_ref()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ref = unsafe {
    ///     tup.uninit_assume_init_ref_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// assert_eq!(inited_ref, tuple!(&13, &vec![1, 2, 3]));
    /// unsafe { tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    unsafe fn assume_init_ref_con_subseq(&self) -> <Seq as TupleLike>::AsRefOutput<'_>;

    /// Get mutable references to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_assume_init_mut_con_subseq()`](TupleLike::uninit_assume_init_mut_con_subseq()) method as
    /// the wrapper for this [`assume_init_mut_con_subseq()`](UninitConSubseq::assume_init_mut_con_subseq()) method.
    ///
    /// # Safety
    ///
    /// Same as [`MaybeUninit::assume_init_mut()`](MaybeUninit::assume_init_mut()).
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_mut = unsafe {
    ///     tup.uninit_assume_init_mut_con_subseq::<tuple_t!(i32, Vec<i32>), _>()
    /// };
    /// *get!(inited_mut; 0) += 1;
    /// get!(inited_mut; 1).push(4);
    /// assert_eq!(inited_mut, tuple!(&mut 14, &mut vec![1, 2, 3, 4]));
    /// unsafe { tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>() };
    /// ```
    unsafe fn assume_init_mut_con_subseq(&mut self) -> <Seq as TupleLike>::AsMutOutput<'_>;

    /// Get pointers to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_con_subseq_as_ptr()`](TupleLike::uninit_con_subseq_as_ptr()) method as
    /// the wrapper for this [`con_subseq_as_ptr()`](UninitConSubseq::con_subseq_as_ptr()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_con_subseq_as_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     assert_eq!(*get!(inited_ptr; 0), 13);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3]);
    ///     tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    fn con_subseq_as_ptr(&self) -> <Seq as TupleLike>::AsPtrOutput;

    /// Get mutable pointers to values of a specific contiguous subsequence
    /// consisting of [`MaybeUninit`] elements.
    ///
    /// Hint: The [`TupleLike`] trait provides the
    /// [`uninit_con_subseq_as_mut_ptr()`](TupleLike::uninit_con_subseq_as_mut_ptr()) method as
    /// the wrapper for this [`con_subseq_as_mut_ptr()`](UninitConSubseq::con_subseq_as_mut_ptr()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use tuplez::{get, tuple, TupleLike, tuple_t};
    ///
    /// let mut tup = tuple!(
    ///     12,
    ///     MaybeUninit::<i32>::zeroed(),
    ///     MaybeUninit::<i32>::new(13),
    ///     MaybeUninit::<Vec<i32>>::uninit(),
    ///     false,
    /// );
    /// tup.uninit_write_one(vec![1, 2, 3]);
    /// let inited_ptr = tup.uninit_con_subseq_as_mut_ptr::<tuple_t!(i32, Vec<i32>), _>();
    /// unsafe {
    ///     *get!(inited_ptr; 0) += 1;
    ///     (*get!(inited_ptr; 1)).push(4);
    ///     assert_eq!(*get!(inited_ptr; 0), 14);
    ///     assert_eq!(*get!(inited_ptr; 1), vec![1, 2, 3, 4]);
    ///     tup.uninit_assume_init_drop_con_subseq::<tuple_t!(i32, Vec<i32>), _>();
    /// }
    /// ```
    fn con_subseq_as_mut_ptr(&mut self) -> <Seq as TupleLike>::AsMutPtrOutput;

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
    /// uninit.uninit_write_one(true);
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
    type PartiallyInitialized = Unit;

    unsafe fn assume_init_con_subseq(self) -> Self::PartiallyInitialized {
        Unit
    }

    unsafe fn assume_init_read_con_subseq(&self) -> Unit {
        Unit
    }

    unsafe fn assume_init_ref_con_subseq(&self) -> <Unit as TupleLike>::AsRefOutput<'_> {
        Unit
    }

    unsafe fn assume_init_mut_con_subseq(&mut self) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }

    fn con_subseq_as_ptr(&self) -> <Unit as TupleLike>::AsPtrOutput {
        Unit
    }

    fn con_subseq_as_mut_ptr(&mut self) -> <Unit as TupleLike>::AsMutPtrOutput {
        Unit
    }

    fn write_con_subseq(&mut self, _: Unit) -> <Unit as TupleLike>::AsMutOutput<'_> {
        Unit
    }

    unsafe fn assume_init_drop_con_subseq(&mut self) {}
}

impl<First, Other, T, I> UninitConSubseq<T, Unused<I>> for Tuple<First, Other>
where
    T: TupleLike,
    Other: UninitConSubseq<T, I>,
{
    type PartiallyInitialized = Tuple<First, Other::PartiallyInitialized>;

    unsafe fn assume_init_con_subseq(self) -> Self::PartiallyInitialized {
        Tuple(self.0, UninitConSubseq::assume_init_con_subseq(self.1))
    }

    unsafe fn assume_init_read_con_subseq(&self) -> T {
        UninitConSubseq::assume_init_read_con_subseq(&self.1)
    }

    unsafe fn assume_init_ref_con_subseq(&self) -> <T as TupleLike>::AsRefOutput<'_> {
        UninitConSubseq::assume_init_ref_con_subseq(&self.1)
    }

    unsafe fn assume_init_mut_con_subseq(&mut self) -> <T as TupleLike>::AsMutOutput<'_> {
        UninitConSubseq::assume_init_mut_con_subseq(&mut self.1)
    }

    fn con_subseq_as_ptr(&self) -> <T as TupleLike>::AsPtrOutput {
        UninitConSubseq::con_subseq_as_ptr(&self.1)
    }

    fn con_subseq_as_mut_ptr(&mut self) -> <T as TupleLike>::AsMutPtrOutput {
        UninitConSubseq::con_subseq_as_mut_ptr(&mut self.1)
    }

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
    type PartiallyInitialized = Tuple<First, Other>;

    unsafe fn assume_init_con_subseq(self) -> Self::PartiallyInitialized {
        Tuple(self.0.assume_init(), self.1)
    }

    unsafe fn assume_init_read_con_subseq(&self) -> Tuple<First, Unit> {
        Tuple(self.0.assume_init_read(), Unit)
    }

    unsafe fn assume_init_ref_con_subseq(
        &self,
    ) -> <Tuple<First, Unit> as TupleLike>::AsRefOutput<'_> {
        Tuple(self.0.assume_init_ref(), Unit)
    }

    unsafe fn assume_init_mut_con_subseq(
        &mut self,
    ) -> <Tuple<First, Unit> as TupleLike>::AsMutOutput<'_> {
        Tuple(self.0.assume_init_mut(), Unit)
    }

    fn con_subseq_as_ptr(&self) -> <Tuple<First, Unit> as TupleLike>::AsPtrOutput {
        Tuple(self.0.as_ptr(), Unit)
    }

    fn con_subseq_as_mut_ptr(&mut self) -> <Tuple<First, Unit> as TupleLike>::AsMutPtrOutput {
        Tuple(self.0.as_mut_ptr(), Unit)
    }

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
    type PartiallyInitialized = Tuple<First1, Other1::PartiallyInitialized>;

    unsafe fn assume_init_con_subseq(self) -> Self::PartiallyInitialized {
        Tuple(
            self.0.assume_init(),
            UninitConSubseq::assume_init_con_subseq(self.1),
        )
    }

    unsafe fn assume_init_read_con_subseq(&self) -> Tuple<First1, Tuple<First2, Other2>> {
        Tuple(
            self.0.assume_init_read(),
            UninitConSubseq::assume_init_read_con_subseq(&self.1),
        )
    }

    unsafe fn assume_init_ref_con_subseq(
        &self,
    ) -> <Tuple<First1, Tuple<First2, Other2>> as TupleLike>::AsRefOutput<'_> {
        Tuple(
            self.0.assume_init_ref(),
            UninitConSubseq::assume_init_ref_con_subseq(&self.1),
        )
    }

    unsafe fn assume_init_mut_con_subseq(
        &mut self,
    ) -> <Tuple<First1, Tuple<First2, Other2>> as TupleLike>::AsMutOutput<'_> {
        Tuple(
            self.0.assume_init_mut(),
            UninitConSubseq::assume_init_mut_con_subseq(&mut self.1),
        )
    }

    fn con_subseq_as_ptr(
        &self,
    ) -> <Tuple<First1, Tuple<First2, Other2>> as TupleLike>::AsPtrOutput {
        Tuple(self.0.as_ptr(), UninitConSubseq::con_subseq_as_ptr(&self.1))
    }

    fn con_subseq_as_mut_ptr(
        &mut self,
    ) -> <Tuple<First1, Tuple<First2, Other2>> as TupleLike>::AsMutPtrOutput {
        Tuple(
            self.0.as_mut_ptr(),
            UninitConSubseq::con_subseq_as_mut_ptr(&mut self.1),
        )
    }

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
