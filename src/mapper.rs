use crate::TupleLike;

/// Define functors for traversing the tuple by immutable references to tuple's elements.
///
/// To traverse a tuple with type `Tuple<T0, T1, ... Tn>`, you need to construct a custom functor type,
/// which implements [`Mapper<T0>`], [`Mapper<T1>`] ... [`Mapper<Tn>`].
/// Pass your functor to tuple's [`foreach()`](Foreach::foreach()) method, then the tuple will call
/// functor's [`map()`](Mapper::map()) method in order of its elements and pass in the immutable reference
/// of the element.
///
/// # The [`mapper!`] macro
///
/// There is a [`mapper!`] macro that helps you build a functor simply, here is an example:
///
/// ```
/// use tuplez::*;
///
/// let tup = tuple!(1, "hello", 3.14).foreach(mapper!{
///     x: i32 => i64: *x as i64;
///     x: f32 => String: x.to_string();
///     x, 'a: &'a str => &'a [u8]: x.as_bytes()
/// });
/// assert_eq!(tup, tuple!(1i64, b"hello" as &[u8], "3.14".to_string()));
/// ```
///
/// Check the documentation page of [`mapper!`] for detailed syntax.
///
/// # Custom functor
///
/// For more complex cases that cannot be covered by the [`mapper!`] macro, for example, you want to save some results
/// inside your functor, you need to implement [`Mapper<Ti>`] for your functor for all element type `Ti`s in tuples.
/// Generic can be used.
///
/// For example:
///
/// ```
/// use tuplez::*;
///
/// struct MyElement(i32);
///
/// #[derive(Default)]
/// struct Collector(Vec<String>);
///
/// impl<T: ToString> Mapper<T> for Collector {
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
/// impl Mapper<MyElement> for Collector {
///     type Output = ();
///     fn map(&mut self, value: &MyElement) -> Self::Output {
///         self.0.push(format!("MyElement : {}", value.0))
///     }
/// }
///
/// let mut collector = Collector::default();
/// tuple!(1, "hello", MyElement(14)).foreach(&mut collector);
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

    /// Map an element to another value through its immutable reference.
    fn map(&mut self, value: &T) -> Self::Output;
}

/// Define functors for traversing the tuple by mutable references to tuple's elements.
///
/// To traverse a tuple with type `Tuple<T0, T1, ... Tn>`, you need to construct a custom functor type,
/// which implements [`MapperMut<T0>`], [`MapperMut<T1>`] ... [`MapperMut<Tn>`].
/// Pass your functor to tuple's [`foreach_mut()`](ForeachMut::foreach_mut()) method, then the tuple will call
/// functor's [`map_mut()`](MapperMut::map_mut()) method in order of its elements and pass in the mutable reference
/// of the element.
///
/// # The [`mapper_mut!`] macro
///
/// There is a [`mapper_mut!`] macro that helps you build a functor simply, here is an example:
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
///
/// Check the documentation page of [`mapper_mut!`] for detailed syntax.
///
/// # Custom functor
///
/// For more complex cases that cannot be covered by the [`mapper_mut!`] macro, for example, you want to save some results
/// inside your functor, you need to implement [`MapperMut<Ti>`] for your functor for all element type `Ti`s in tuples.
/// Generic can be used.
///
/// For example:
///
/// ```
/// use tuplez::*;
///
/// #[derive(PartialEq, Eq, Debug)]
/// struct MyNonDefault(i32);
///
/// #[derive(Default)]
/// struct TakeValue {
///     is_my_struct: Vec<bool>,
/// }
///
/// impl<T: Default> MapperMut<T> for TakeValue {
///     type Output = T;
///     fn map_mut(&mut self, value: &mut T) -> Self::Output {
///         self.is_my_struct.push(false);
///         std::mem::take(value)
///     }
/// }
///
/// impl MapperMut<MyNonDefault> for TakeValue {
///     type Output = i32;
///     fn map_mut(&mut self, value: &mut MyNonDefault) -> Self::Output {
///         self.is_my_struct.push(true);
///         std::mem::take(&mut value.0)
///     }
/// }
///
/// let mut take_value = TakeValue::default();
/// let mut tup = tuple!(3.14, "hello".to_string(), MyNonDefault(14));
/// let tup2 = tup.foreach_mut(&mut take_value);
/// assert_eq!(take_value.is_my_struct, vec![false, false, true]);
/// assert_eq!(tup, tuple!(0.0, String::new(), MyNonDefault(0)));
/// assert_eq!(tup2, tuple!(3.14, "hello".to_string(), 14));
/// ```
pub trait MapperMut<T> {
    /// Output type of mapping.
    type Output;

    /// Map an element to another value through its immutable reference.
    fn map_mut(&mut self, value: &mut T) -> Self::Output;
}

/// Define functors for traversing the tuple by taking its elements.
///
/// To traverse a tuple with type `Tuple<T0, T1, ... Tn>`, you need to construct a custom functor type,
/// which implements [`MapperOnce<T0>`], [`MapperOnce<T1>`] ... [`MapperOnce<Tn>`].
/// Pass your functor to tuple's [`foreach_once()`](ForeachOnce::foreach_once()) method, then the tuple will call
/// functor's [`map_once()`](MapperOnce::map_once()) method in order of its elements and move its elements in.
///
/// # The [`mapper_once!`] macro
///
/// There is a [`mapper_once!`] macro that helps you build a functor simply, here is an example:
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
///
/// Check the documentation page of [`mapper_once!`] for detailed syntax.
///
/// # Custom functor
///
/// For more complex cases that cannot be covered by the [`mapper_once!`] macro, for example, you want to save some results
/// inside your functor, you need to implement [`MapperOnce<Ti>`] for your functor for all element type `Ti`s in tuples.
/// Generic can be used.
///
/// For example:
///
/// ```
/// use tuplez::*;
/// 
/// #[derive(Debug, Default)]
/// struct MyWrapper<T>(T);
/// 
/// struct Unwrapper;
/// 
/// impl<T: Default> MapperOnce<Option<T>> for Unwrapper {
///     type Output = T;
///     fn map_once(&mut self, value: Option<T>) -> Self::Output {
///         value.unwrap_or_default()
///     }
/// }
/// 
/// impl<T: Default, E> MapperOnce<Result<T, E>> for Unwrapper {
///     type Output = T;
///     fn map_once(&mut self, value: Result<T, E>) -> Self::Output {
///         value.unwrap_or_default()
///     }
/// }
/// 
/// impl<T: Default> MapperOnce<MyWrapper<T>> for Unwrapper {
///     type Output = T;
///     fn map_once(&mut self, value: MyWrapper<T>) -> Self::Output {
///         value.0
///     }
/// }
/// 
/// let tup = tuple!(
///     Some([3.14, 9.8]),
///     Result::<i32, ()>::Err(()),
///     MyWrapper("hello".to_string())
/// );
/// let tup2 = tup.foreach_once(&mut Unwrapper);
/// // assert_eq!(tup, ... ); // No, `tup` has been moved
/// assert_eq!(tup2, tuple!([3.14, 9.8], 0, "hello".to_string()));
/// ```
pub trait MapperOnce<T> {
    /// Output type of mapping.
    type Output;

    /// Take an element and map it to another value.
    fn map_once(&mut self, value: T) -> Self::Output;
}

/// Traverse the tuple by immutable references to its elements.
///
/// # The Functor `F`
///
/// For traversing `Tuple<T0, T1, ... Tn>`, you need to construct a custom functor type,
/// which needs to implement [`Mapper<T0>`], [`Mapper<T1>`] ... [`Mapper<Tn>`].
///
/// See the documentation page of [`Mapper`] for details.
pub trait Foreach<F>: TupleLike {
    /// The type of tuple generated by traversing the tuple.
    type Output: TupleLike;

    /// Traverse the tuple by immutable references to its elements,
    /// and collect the output of traversal into a new tuple.
    ///
    /// # Example
    ///
    /// ```
    /// use tuplez::*;
    ///
    /// let tup = tuple!(1, "hello", 3.14).foreach(mapper!{
    ///     x: i32 => i64: *x as i64;
    ///     x: f32 => String: x.to_string();
    ///     x, 'a: &'a str => &'a [u8]: x.as_bytes()
    /// });
    /// assert_eq!(tup, tuple!(1i64, b"hello" as &[u8], "3.14".to_string()));
    /// ```
    fn foreach(&self, f: &mut F) -> Self::Output;
}

/// Traverse the tuple by mutable references to its elements.
///
/// # The Functor `F`
///
/// For traversing `Tuple<T0, T1, ... Tn>`, you need to construct a custom functor type,
/// which needs to implement [`MapperMut<T0>`], [`MapperMut<T1>`] ... [`MapperMut<Tn>`].
///
/// See the documentation page of [`MapperMut`] for details.
pub trait ForeachMut<F>: TupleLike {
    /// The type of tuple generated by traversing the tuple.
    type Output: TupleLike;

    /// Traverse the tuple by mutable references to its elements,
    /// and collect the output of traversal into a new tuple.
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
    fn foreach_mut(&mut self, f: &mut F) -> Self::Output;
}

/// Traverse the tuple by taking its elements.
///
/// # The Functor `F`
///
/// For traversing `Tuple<T0, T1, ... Tn>`, you need to construct a custom functor type,
/// which needs to implement [`MapperOnce<T0>`], [`MapperOnce<T1>`] ... [`MapperOnce<Tn>`].
///
/// See the documentation page of [`MapperOnce`] for details.
pub trait ForeachOnce<F>: TupleLike {
    /// The type of tuple generated by traversing the tuple.
    type Output: TupleLike;

    /// Traverse the tuple by take its elements,
    /// and collect the output of traversal into a new tuple.
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
    fn foreach_once(self, f: &mut F) -> Self::Output;
}
