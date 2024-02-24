extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

mod parser;

use parser::*;

#[proc_macro]
pub fn tuple(input: TokenStream) -> TokenStream {
    let TupleGen(exprs) = parse_macro_input!(input as TupleGen);
    let mut unpack = quote!(Unit);
    for expr in exprs.into_iter().rev() {
        unpack = quote!( Tuple( #expr, #unpack) );
    }
    unpack.into()
}

#[proc_macro]
pub fn tuple_t(input: TokenStream) -> TokenStream {
    let TupleType(types) = parse_macro_input!(input as TupleType);
    let mut unpack = quote!(Unit);
    for ty in types.into_iter().rev() {
        unpack = quote!( Tuple< #ty, #unpack> );
    }
    unpack.into()
}

#[proc_macro]
pub fn tuple_pat(input: TokenStream) -> TokenStream {
    let TuplePat { mut pats, leader } = parse_macro_input!(input as TuplePat);
    let mut unpack;
    if pats.is_empty() {
        unpack = quote!(_);
    } else if leader {
        unpack = quote!(..);
        for pat in pats.into_iter().rev() {
            unpack = quote!( Tuple( #pat, #unpack) );
        }
    } else {
        let last = pats.pop().unwrap();
        unpack = quote!(#last);
        for pat in pats.into_iter().rev() {
            unpack = quote!( Tuple( #pat, #unpack) );
        }
    }
    unpack.into()
}

#[proc_macro]
pub fn get(input: TokenStream) -> TokenStream {
    let TupleIndex { tup, index } = parse_macro_input!(input as TupleIndex);
    let field = quote!(. 1);
    let fields = vec![field.clone(); index];
    quote!( (#tup) #(#fields)* . 0).into()
}

#[proc_macro]
pub fn split_at(input: TokenStream) -> TokenStream {
    let TupleIndex { tup, index } = parse_macro_input!(input as TupleIndex);
    let mut unpack = quote!( (Unit, (#tup)) );
    for _ in 0..index {
        unpack = quote!({
            let (splitted, Tuple(first, other)) = #unpack;
            (splitted.push_back(first), other)
        });
    }
    unpack.into()
}
