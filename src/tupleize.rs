/// Convert between [`Tuple`](crate::Tuple) and struct types.
///
/// If there are no special requirements then you should use [the derive marco](derive@crate::Tupleize).
///
/// # Example
/// ```
/// use tuplez::{tuple, Tupleize};
///
/// #[derive(Tupleize, Debug, PartialEq, Eq)]
/// struct Person<Meta> {
///     name: &'static str,
///     age: u32,
///     meta: Meta,
/// }
///
/// let john = Person {
///     name: "John",
///     age: 21,
///     meta: vec![9, 8, 7],
/// };
/// assert_eq!(john.tupleize(), tuple!("John", 21, vec![9, 8, 7]));
///
/// let smith = Person {
///     name: "Smith",
///     age: 49,
///     meta: Some(88.88),
/// };
/// assert_eq!(smith, Person::from(tuple!("Smith", 49, Some(88.88))));
/// ```
pub trait Tupleize: From<Self::Equivalent> + Into<Self::Equivalent> {
    /// The equivalent tuple type with the same number of elements, the same element types,
    /// and the same element order as the struct.
    type Equivalent: From<Self>;

    /// Convert self into a tuple.
    fn tupleize(self) -> Self::Equivalent {
        <Self::Equivalent as From<Self>>::from(self)
    }
}
