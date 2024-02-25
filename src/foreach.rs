//! Provides the ability to traverse tuples.
//!
//! Check the documentation page of [`Mapper`] for details.
use crate::{Tuple, TupleLike, Unit};

/// Define functors for traversing the tuple.
///
/// To traverse a tuple with type [`Tuple<T0, T1, ... Tn>`](crate::Tuple), you need to construct a custom functor type,
/// which implements [`Mapper<T0>`], [`Mapper<T1>`] ... [`Mapper<Tn>`].
/// Pass your functor to tuple's [`foreach()`](TupleLike::foreach()) method, then the tuple will call
/// functor's [`map()`](Mapper::map()) method in order of its elements and move the elements in.
///
/// NOTE: Traversing a tuple will consume it. If this is not what you want, call [`as_ref()`](TupleLike::as_ref())
/// or [`as_mut()`](TupleLike::as_mut()) to create a new tuple that references its all members before traversing.
///
/// Tip: [`Mapper`] map elements by their types. If you are looking for a way to map elements by their order,
/// then what you are looking for is to
/// [pass a tuple containing callables into `fold()` method](Tuple#fold-tuples-in-order-of-their-elements-but-collecting-results-in-a-tuple).
///
/// # The [`mapper!`](crate::mapper!) macro
///
/// There is a [`mapper!`](crate::mapper!) macro that helps you build a functor simply, here is an example:
///
/// ```
/// use tuplez::{mapper, tuple, TupleLike};
///
/// let tup = tuple!(1, "hello", 3.14).foreach(mapper!{
///     |x: i32| -> i64 { x as i64 }
///     |x: f32| -> String { x.to_string() }
///     <'a> |x: &'a str| -> &'a [u8] { x.as_bytes() }
/// });
/// assert_eq!(tup, tuple!(1i64, b"hello" as &[u8], "3.14".to_string()));
/// ```
///
/// Check the documentation page of [`mapper!`](crate::mapper!) for detailed syntax.
///
/// # Custom functor
///
/// For more complex cases that cannot be covered by the [`mapper!`](crate::mapper!) macro,
/// for example, you want to save some results inside your functor,
/// you need to implement [`Mapper<Ti>`] for your functor for all element type `Ti`s in tuples.
/// Generic can be used.
///
/// For example:
///
/// ```
/// use tuplez::{foreach::Mapper, tuple, TupleLike};
///
/// struct MyElement(i32);
///
/// #[derive(Default)]
/// struct Collector(Vec<String>);
///
/// impl<T: ToString> Mapper<&T> for Collector {
///     type Output = ();
///     fn map(&mut self, value: &T) -> Self::Output {
///         self.0.push(format!(
///             "{} : {}",
///             std::any::type_name::<T>(),
///             value.to_string()
///         ))
///     }
/// }
///
/// impl Mapper<&MyElement> for Collector {
///     type Output = ();
///     fn map(&mut self, value: &MyElement) -> Self::Output {
///         self.0.push(format!("MyElement : {}", value.0))
///     }
/// }
///
/// let mut collector = Collector::default();
/// tuple!(1, "hello", MyElement(14)).as_ref().foreach(&mut collector);
/// assert_eq!(
///     collector.0,
///     vec![
///         "i32 : 1".to_string(),
///         "&str : hello".to_string(),
///         "MyElement : 14".to_string()
///     ]
/// );
/// ```
pub trait Mapper<T> {
    /// Output type of mapping.
    type Output;

    /// Map an element to another value.
    fn map(&mut self, value: T) -> Self::Output;
}

/// Traverse the tuple.
///
/// # The Functor `F`
///
/// For traversing [`Tuple<T0, T1, ... Tn>`](crate::Tuple), you need to construct a custom functor type,
/// which needs to implement [`Mapper<T0>`], [`Mapper<T1>`] ... [`Mapper<Tn>`].
///
/// See the documentation page of [`Mapper`] for details.
pub trait Foreach<F> {
    /// The type of tuple generated by traversing the tuple.
    type Output: TupleLike;

    /// Traverse the tuple, and collect the output of traversal into a new tuple.
    ///
    /// NOTE: Traversing a tuple will consume it. If this is not what you want, call [`as_ref()`](TupleLike::as_ref())
    /// or [`as_mut()`](TupleLike::as_mut()) to create a new tuple that references its all members before traversing.
    ///
    /// Hint: The [`TupleLike`] trait provides the [`foreach()`](TupleLike::foreach()) method as the wrapper
    /// for this [`foreach()`](Foreach::foreach()) method.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::{mapper, tuple, TupleLike};
    ///
    /// let tup = tuple!(1, "hello", 3.14).foreach(mapper!{
    ///     |x: i32| -> i64 { x as i64 }
    ///     |x: f32| -> String { x.to_string() }
    ///     <'a> |x: &'a str| -> &'a [u8] { x.as_bytes() }
    /// });
    /// assert_eq!(tup, tuple!(1i64, b"hello" as &[u8], "3.14".to_string()));
    /// ```
    fn foreach(self, f: &mut F) -> Self::Output;
}

impl<F> Foreach<F> for Unit {
    type Output = Unit;
    fn foreach(self, _: &mut F) -> Self::Output {
        Unit
    }
}

impl<F, First, Other> Foreach<F> for Tuple<First, Other>
where
    F: Mapper<First>,
    Other: Foreach<F>,
{
    type Output = Tuple<<F as Mapper<First>>::Output, <Other as Foreach<F>>::Output>;
    fn foreach(self, f: &mut F) -> Self::Output {
        Tuple(f.map(self.0), self.1.foreach(f))
    }
}
