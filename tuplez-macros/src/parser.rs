use std::{
    collections::VecDeque,
    ops::{Add, AddAssign},
};

use quote::ToTokens;
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

pub struct TuplePick {
    pub tup: Expr,
    pub indices: Vec<usize>,
}

impl Parse for TuplePick {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let tup = input.parse()?;
        let mut indices = Vec::<usize>::default();
        let _: Token![;] = input.parse()?;
        loop {
            let start: LitInt = input.parse()?;
            let start: usize = start.base10_parse()?;
            let mut end = start;
            if input.peek(Token![-]) {
                let _: Token![-] = input.parse()?;
                let end_: LitInt = input.parse()?;
                end = end_.base10_parse()?;
            }
            if input.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
            }
            if start <= end {
                (start..=end).for_each(|i| indices.push(i));
            } else {
                (end..=start).rev().for_each(|i| indices.push(i));
            }
            if input.is_empty() {
                break;
            }
        }

        Ok(TuplePick { tup, indices })
    }
}

pub enum TupleArg {
    Move(usize),
    Ref(usize),
    Mut(usize),
}

#[derive(Default)]
pub struct ArgList(pub Vec<TupleArg>);

impl Add for ArgList {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign for ArgList {
    fn add_assign(&mut self, mut rhs: Self) {
        self.0.append(&mut rhs.0);
    }
}

impl Parse for ArgList {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut args = Vec::new();

        let mut ctor: fn(usize) -> TupleArg = TupleArg::Move;
        if input.peek(Token![&]) {
            let _: Token![&] = input.parse()?;
            ctor = TupleArg::Ref;
            if input.peek(Token![mut]) {
                let _: Token![mut] = input.parse()?;
                ctor = TupleArg::Mut;
            }
        }

        let start: LitInt = input.parse()?;
        let start: usize = start.base10_parse()?;
        let mut end = start;
        if input.peek(Token![-]) {
            let _: Token![-] = input.parse()?;
            let end_: LitInt = input.parse()?;
            end = end_.base10_parse()?;
        }
        if start <= end {
            (start..=end).for_each(|i| args.push(ctor(i)));
        } else {
            (end..=start).rev().for_each(|i| args.push(ctor(i)));
        }

        Ok(ArgList(args))
    }
}

pub struct TupleSwap {
    pub tup: Expr,
    pub left: Vec<usize>,
    pub right: Vec<usize>,
}

impl Parse for TupleSwap {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let tup = input.parse()?;
        let mut left = vec![];
        let mut right = vec![];
        let _: Token![;] = input.parse()?;

        let left_start: LitInt = input.parse()?;
        let left_start: usize = left_start.base10_parse()?;
        let mut left_end = left_start;
        if input.peek(Token![-]) {
            let _: Token![-] = input.parse()?;
            let end: LitInt = input.parse()?;
            left_end = end.base10_parse()?;
        }
        if left_start <= left_end {
            (left_start..=left_end).for_each(|i| left.push(i));
        } else {
            (left_end..=left_start).rev().for_each(|i| left.push(i));
        }

        let _: Token![,] = input.parse()?;

        let right_start: LitInt = input.parse()?;
        let right_start: usize = right_start.base10_parse()?;
        let mut right_end = right_start;
        if input.peek(Token![-]) {
            let _: Token![-] = input.parse()?;
            let end: LitInt = input.parse()?;
            right_end = end.base10_parse()?;
        }
        if right_start <= right_end {
            (right_start..=right_end).for_each(|i| right.push(i));
        } else {
            (right_end..=right_start).rev().for_each(|i| right.push(i));
        }

        if left.len() != right.len() {
            return Err(input.error("Indices groups must be of equal length"));
        }

        if left.iter().any(|i| right.contains(i)) {
            return Err(input.error("Indices overlap"));
        }
        Ok(TupleSwap { tup, left, right })
    }
}

pub struct TupleApply {
    pub tup: Expr,
    pub func: Expr,
    pub args: ArgList,
}

impl Parse for TupleApply {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let tup = input.parse()?;
        let _: Token![=>] = input.parse()?;
        let mut func: Expr = input.parse()?;

        let args = match &mut func {
            Expr::Call(call) => std::mem::take(&mut call.args),
            Expr::MethodCall(call) => std::mem::take(&mut call.args),
            _ => return Err(input.error("expected function call")),
        }
        .into_iter()
        .map(|arg| syn::parse2::<ArgList>(arg.into_token_stream()))
        .try_fold(ArgList::default(), |acc, x| x.map(|x| acc + x))?;

        Ok(TupleApply { tup, func, args })
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
