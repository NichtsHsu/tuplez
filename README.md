# tuplez

This crate introduces a tuple type represented in recursive form rather than parallel form.

## Motivation

The [primitive tuple types](https://doc.rust-lang.org/std/primitive.tuple.html) are represented in parallel form, like:

```text
(a, b, c, d ...)
```

Since Rust doesn't support variadic generics, we cannot add methods to primitive tuples with any number of elements.

Currently, most tuple crates use declarative macros to implement methods for tuples whose number of elements is less than
a certain limit (usually 32).

To solve this, tuplez introduces a `Tuple` type represented in recursive form, like:

```text
Tuple(a, Tuple(b, Tuple(c, Tuple(d, ...))))
```

The advantage of this representation is that you can implement methods recursively for all tuples,
and there is no longer a limit on the number of tuple's elements. And, in almost all cases, the `Tuple` takes no more memory than
the primitive tuples.

## Functionality

* Create tuples with any number of elements.
* Access elements in a tuple at any index, or by their types.
* Push element to a tuple or pop element from a tuple.
* Join two tuples or split a tuple into two parts.
* Rich tuple operations, e.g.: reverse, left rotate, zip.
* Get subsequences.
* If all element types implement a `Trait` (e.g. `Eq`, `Add`), then the `Tuple` also implement that `Trait`.
* Traverse all elements of a tuple, or fold a tuple.
* When the number of elements of a tuple doesn't exceed 32, then it can be converted from/to a primitive tuple or a primitive array.

Please check the [documentation](https://docs.rs/tuplez) for details.
