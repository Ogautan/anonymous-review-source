//! Bounded integer facts for source-level container element accesses.

use quote::ToTokens;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum IndexValue {
    Constant(usize),
    Integer,
    Unknown,
}

impl IndexValue {
    pub(crate) fn join(self, other: Self) -> Self {
        if self == other {
            self
        } else if self != Self::Unknown && other != Self::Unknown {
            Self::Integer
        } else {
            Self::Unknown
        }
    }

    pub(crate) fn from_type(ty: &syn::Type) -> Self {
        match ty {
            syn::Type::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
                if matches!(
                    path.path.segments[0].ident.to_string().as_str(),
                    "usize"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "isize"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                ) {
                    Self::Integer
                } else {
                    Self::Unknown
                }
            }
            _ => Self::Unknown,
        }
    }

    pub(crate) fn constant(self) -> Option<usize> {
        match self {
            Self::Constant(value) => Some(value),
            _ => None,
        }
    }

    pub(crate) fn context(self) -> String {
        match self {
            Self::Constant(value) => format!("container_element_index:{value}"),
            _ => "container_element_index:dynamic".to_string(),
        }
    }
}

pub(crate) fn evaluate(expr: &syn::Expr, lookup: &impl Fn(&str) -> IndexValue) -> IndexValue {
    use IndexValue::{Constant, Integer, Unknown};
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(value),
            ..
        }) => value.base10_parse().map(Constant).unwrap_or(Integer),
        syn::Expr::Path(path) => lookup(&path.path.to_token_stream().to_string().replace(' ', "")),
        syn::Expr::Paren(expr) => evaluate(&expr.expr, lookup),
        syn::Expr::Group(expr) => evaluate(&expr.expr, lookup),
        syn::Expr::Cast(expr) if IndexValue::from_type(&expr.ty) == Integer => {
            // Preserve only constants representable on every supported pointer
            // width and in the selected unsigned target. Other casts are dynamic.
            let width = match expr.ty.to_token_stream().to_string().as_str() {
                "u8" => Some(8),
                "u16" => Some(16),
                "u32" | "usize" => Some(32),
                "u64" => Some(64),
                "u128" => Some(128),
                _ => None,
            };
            match (evaluate(&expr.expr, lookup), width) {
                (Constant(value), Some(width))
                    if width >= usize::BITS || value < (1usize << width) =>
                {
                    Constant(value)
                }
                _ => Integer,
            }
        }
        syn::Expr::Binary(expr) => {
            let left = evaluate(&expr.left, lookup);
            let right = evaluate(&expr.right, lookup);
            if left != Unknown && right != Unknown {
                match (&expr.op, left, right) {
                    (syn::BinOp::Rem(_), _, Constant(1))
                    | (syn::BinOp::Mul(_) | syn::BinOp::BitAnd(_), _, Constant(0))
                    | (syn::BinOp::Mul(_) | syn::BinOp::BitAnd(_), Constant(0), _) => {
                        return Constant(0);
                    }
                    _ => {}
                }
            }
            if let (Constant(left), Constant(right)) = (left, right) {
                let value = match expr.op {
                    syn::BinOp::Add(_) => left.checked_add(right),
                    syn::BinOp::Sub(_) => left.checked_sub(right),
                    syn::BinOp::Mul(_) => left.checked_mul(right),
                    syn::BinOp::Div(_) => left.checked_div(right),
                    syn::BinOp::Rem(_) => left.checked_rem(right),
                    syn::BinOp::BitAnd(_) => Some(left & right),
                    syn::BinOp::BitOr(_) => Some(left | right),
                    syn::BinOp::BitXor(_) => Some(left ^ right),
                    _ => None,
                };
                // The source's integer width is not always resolved. Host
                // usize arithmetic must not turn a narrow wrapping operation
                // into an out-of-range constant that excludes a real access.
                return value
                    .filter(|value| *value <= smallest_integer_max(left.max(right)))
                    .map(Constant)
                    .unwrap_or(Integer);
            }
            if left != Unknown && right != Unknown {
                Integer
            } else {
                Unknown
            }
        }
        _ => Unknown,
    }
}

fn smallest_integer_max(operand: usize) -> usize {
    for bits in [8, 16, 32, 64] {
        if bits > usize::BITS {
            break;
        }
        let unsigned = usize::MAX >> (usize::BITS - bits);
        for maximum in [unsigned >> 1, unsigned] {
            if operand <= maximum {
                return maximum;
            }
        }
    }
    usize::MAX
}
