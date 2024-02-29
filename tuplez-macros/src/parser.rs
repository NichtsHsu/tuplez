use std::collections::VecDeque;

use syn::{parse::Parse, Expr, ExprBlock, Generics, Ident, LitInt, Pat, Token, Type};

pub struct TupleGen(pub Vec<Expr>);

impl Parse for TupleGen {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut exprs = vec![];
        loop {
            if input.is_empty() {
                return Ok(TupleGen(exprs));
            }
            let ty: Expr = input.parse()?;
            if input.is_empty() {
                exprs.push(ty);
                return Ok(TupleGen(exprs));
            }
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
                exprs.push(ty);
                continue;
            }
            if lookahead.peek(Token![;]) {
                let _: Token![;] = input.parse()?;
                let num: LitInt = input.parse()?;
                let num: usize = num.base10_parse()?;
                for _ in 0..num {
                    exprs.push(ty.clone());
                }
                if input.is_empty() {
                    return Ok(TupleGen(exprs));
                }
                let _: Token![,] = input.parse()?;
            } else {
                return Err(lookahead.error());
            }
        }
    }
}

pub struct TupleType(pub Vec<Type>);

impl Parse for TupleType {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut types = vec![];
        loop {
            if input.is_empty() {
                return Ok(TupleType(types));
            }
            let ty: Type = input.parse()?;
            if input.is_empty() {
                types.push(ty);
                return Ok(TupleType(types));
            }
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
                types.push(ty);
                continue;
            }
            if lookahead.peek(Token![;]) {
                let _: Token![;] = input.parse()?;
                let num: LitInt = input.parse()?;
                let num: usize = num.base10_parse()?;
                for _ in 0..num {
                    types.push(ty.clone());
                }
                if input.is_empty() {
                    return Ok(TupleType(types));
                }
                let _: Token![,] = input.parse()?;
            } else {
                return Err(lookahead.error());
            }
        }
    }
}

pub struct TuplePat {
    pub pats: Vec<Pat>,
    pub leader: bool,
}

impl Parse for TuplePat {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut pats = vec![];
        let leader = if input.peek(Token![#]) {
            let _: Token![#] = input.parse()?;
            false
        } else {
            true
        };
        loop {
            if input.is_empty() {
                return Ok(TuplePat { pats, leader });
            }
            let pat = Pat::parse_multi(input)?;
            if input.is_empty() {
                pats.push(pat);
                return Ok(TuplePat { pats, leader });
            }
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
                pats.push(pat);
                continue;
            }
            if lookahead.peek(Token![;]) {
                let _: Token![;] = input.parse()?;
                let num: LitInt = input.parse()?;
                let num: usize = num.base10_parse()?;
                for _ in 0..num {
                    pats.push(pat.clone());
                }
                if input.is_empty() {
                    return Ok(TuplePat { pats, leader });
                }
                let _: Token![,] = input.parse()?;
            } else {
                return Err(lookahead.error());
            }
        }
    }
}

pub struct TupleIndex {
    pub tup: Expr,
    pub index: usize,
}

impl Parse for TupleIndex {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let tup: Expr = input.parse()?;
        let _: Token![;] = input.parse()?;
        let index: LitInt = input.parse()?;
        let index: usize = index.base10_parse()?;
        Ok(TupleIndex { tup, index })
    }
}

pub enum IndexOrType {
    Index(usize),
    Type(Type),
}

pub struct TupleTake {
    pub tup: Expr,
    pub ext: IndexOrType,
}

impl Parse for TupleTake {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let tup: Expr = input.parse()?;
        let _: Token![;] = input.parse()?;
        if input.peek(LitInt) {
            let index: LitInt = input.parse()?;
            let index: usize = index.base10_parse()?;
            return Ok(TupleTake {
                tup,
                ext: IndexOrType::Index(index),
            });
        }
        let ty: Type = input.parse()?;
        Ok(TupleTake {
            tup,
            ext: IndexOrType::Type(ty),
        })
    }
}

pub struct Rule {
    pub generic: Option<Generics>,
    pub inputs: VecDeque<(Ident, Option<Type>, bool)>,
    pub output_type: Option<Type>,
    pub body: ExprBlock,
}

impl Parse for Rule {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let generic = if input.peek(Token![<]) {
            Some(input.parse()?)
        } else {
            None
        };
        let _: Token![|] = input.parse()?;
        let mut inputs = VecDeque::new();
        loop {
            let mut mutable = false;
            if input.peek(Token![mut]) {
                let _: Token![mut] = input.parse()?;
                mutable = true;
            }
            let ident = input.parse()?;
            let mut ty = None;
            if input.peek(Token![:]) {
                let _: Token![:] = input.parse()?;
                ty = Some(input.parse()?);
            }
            inputs.push_back((ident, ty, mutable));
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
            } else if lookahead.peek(Token![|]) {
                let _: Token![|] = input.parse()?;
                break;
            } else {
                return Err(lookahead.error());
            }
        }
        let mut output_type = None;
        if input.peek(Token![->]) {
            let _: Token![->] = input.parse()?;
            output_type = Some(input.parse()?);
        }
        let body = input.parse()?;
        loop {
            if input.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
            } else if input.peek(Token![;]) {
                let _: Token![;] = input.parse()?;
            } else {
                break;
            }
        }

        Ok(Rule {
            generic,
            inputs,
            output_type,
            body,
        })
    }
}

pub struct Mapper(pub Vec<Rule>);

impl Parse for Mapper {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut rules: Vec<Rule> = vec![];
        loop {
            if input.is_empty() {
                break;
            }
            rules.push(input.parse()?);
        }
        for r in &mut rules {
            if r.inputs.len() != 1 {
                return Err(input.error("expected exactly one parameter"));
            }
            if r.inputs[0].1.is_none() {
                return Err(input.error("expected type annotation for the parameter"));
            }
            r.output_type.get_or_insert(r.inputs[0].1.clone().unwrap());
        }
        Ok(Mapper(rules))
    }
}

pub struct Folder(pub Vec<Rule>);

impl Parse for Folder {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let acc_type: Type = input.parse()?;
        let _: Token![;] = input.parse()?;
        let mut rules: Vec<Rule> = vec![];
        loop {
            if input.is_empty() {
                break;
            }
            rules.push(input.parse()?);
        }
        for r in &mut rules {
            if r.inputs.len() != 2 {
                return Err(input.error("expected exactly two parameters"));
            }
            if r.inputs[1].1.is_none() {
                return Err(input.error("expected type annotation for the second parameter"));
            }
            r.inputs[0].1.get_or_insert(acc_type.clone());
            r.output_type.get_or_insert(acc_type.clone());
        }
        Ok(Folder(rules))
    }
}
