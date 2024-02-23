use syn::{parse::Parse, Expr, LitInt, Token, Type};

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

pub struct TupleIndex {
    pub tup: Expr,
    pub index: usize,
}

impl Parse for TupleIndex {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let tup: Expr = input.parse()?;
        let _: Token![;] = input.parse()?;
        let index: LitInt = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("expected end of macro invocation"));
        }
        let index: usize = index.base10_parse()?;
        Ok(TupleIndex { tup, index })
    }
}
