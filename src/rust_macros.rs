//! Recover evaluated expression arguments of simple declarative macro arms.
//! No procedural expansion, repetitions, or execution through opaque macros.

use proc_macro2::{Delimiter, Group, Ident, TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;

#[derive(Clone)]
enum Argument {
    Literal(String),
    Fragment(String, String),
}

#[derive(Clone)]
struct Arm {
    arguments: Vec<Argument>,
    evaluated: Vec<usize>,
}

#[derive(Clone)]
pub(crate) struct ExpressionArguments(Vec<Arm>);

impl ExpressionArguments {
    pub(crate) fn parse(tokens: TokenStream) -> Option<Self> {
        let mut tokens = tokens.into_iter().peekable();
        let mut arms = Vec::new();
        while tokens.peek().is_some() {
            let TokenTree::Group(matcher) = tokens.next()? else {
                return None;
            };
            if !matches!(tokens.next()?, TokenTree::Punct(p) if p.as_char() == '=')
                || !matches!(tokens.next()?, TokenTree::Punct(p) if p.as_char() == '>')
            {
                return None;
            }
            let TokenTree::Group(expansion) = tokens.next()? else {
                return None;
            };
            if matches!(tokens.peek(), Some(TokenTree::Punct(p)) if matches!(p.as_char(), ';' | ','))
            {
                tokens.next();
            }
            let mut arguments = Vec::new();
            let mut current = Vec::new();
            for token in matcher.stream() {
                if matches!(&token, TokenTree::Punct(p) if p.as_char() == ',') {
                    arguments.push(parse_argument(&current)?);
                    current.clear();
                } else {
                    current.push(token);
                }
            }
            if !current.is_empty() {
                arguments.push(parse_argument(&current)?);
            }
            // Generated placeholders must not coincide with identifiers in
            // the source expansion, including an arm that discards its input.
            let expansion_text = expansion.stream().to_string();
            let mut marker_prefix = "__fs_macro_argument".to_string();
            while expansion_text.contains(&marker_prefix) {
                marker_prefix.push('_');
            }
            let body = substitute(expansion.stream(), &arguments, &marker_prefix)?;
            let block: syn::Block = syn::parse2(TokenStream::from(TokenTree::Group(Group::new(
                Delimiter::Brace,
                body,
            ))))
            .ok()?;
            struct Evaluated<'a> {
                arguments: &'a [Argument],
                marker_prefix: &'a str,
                indices: Vec<usize>,
            }
            impl<'ast> Visit<'ast> for Evaluated<'_> {
                fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
                    for (index, argument) in self.arguments.iter().enumerate() {
                        if matches!(argument, Argument::Fragment(_, kind) if matches!(kind.as_str(), "expr" | "block"))
                            && expr
                                .path
                                .is_ident(&format!("{}_{index}", self.marker_prefix))
                        {
                            self.indices.push(index);
                        }
                    }
                }
                fn visit_item(&mut self, _: &'ast syn::Item) {}
                fn visit_expr_closure(&mut self, _: &'ast syn::ExprClosure) {}
                fn visit_macro(&mut self, _: &'ast syn::Macro) {}
            }
            let mut visitor = Evaluated {
                arguments: &arguments,
                marker_prefix: &marker_prefix,
                indices: Vec::new(),
            };
            visitor.visit_block(&block);
            visitor.indices.sort_unstable();
            visitor.indices.dedup();
            let evaluated = std::mem::take(&mut visitor.indices);
            arms.push(Arm {
                arguments,
                evaluated,
            });
        }
        Some(Self(arms))
    }

    pub(crate) fn evaluated<'a>(&self, arguments: &'a [syn::Expr]) -> Vec<&'a syn::Expr> {
        let Some(arm) =
            self.0.iter().find(|arm| {
                arm.arguments.len() == arguments.len()
            && arm.arguments.iter().zip(arguments).all(|(pattern, actual)| match pattern {
                Argument::Literal(literal) => actual.to_token_stream().to_string() == *literal,
                Argument::Fragment(_, kind) => match kind.as_str() {
                    "block" => matches!(actual, syn::Expr::Block(_)),
                    "ident" => matches!(actual, syn::Expr::Path(p) if p.path.segments.len() == 1),
                    "expr" | "ty" => true,
                    _ => false,
                },
            })
            })
        else {
            return Vec::new();
        };
        arm.evaluated
            .iter()
            .filter_map(|index| arguments.get(*index))
            .collect()
    }
}

fn parse_argument(tokens: &[TokenTree]) -> Option<Argument> {
    match tokens {
        [
            TokenTree::Punct(dollar),
            TokenTree::Ident(name),
            TokenTree::Punct(colon),
            TokenTree::Ident(kind),
        ] if dollar.as_char() == '$' && colon.as_char() == ':' => {
            Some(Argument::Fragment(name.to_string(), kind.to_string()))
        }
        tokens
            if !tokens.is_empty()
                && !tokens
                    .iter()
                    .any(|t| matches!(t, TokenTree::Punct(p) if p.as_char() == '$')) =>
        {
            Some(Argument::Literal(
                tokens.iter().cloned().collect::<TokenStream>().to_string(),
            ))
        }
        _ => None,
    }
}

fn substitute(
    tokens: TokenStream,
    arguments: &[Argument],
    marker_prefix: &str,
) -> Option<TokenStream> {
    let mut tokens = tokens.into_iter();
    let mut out = TokenStream::new();
    while let Some(token) = tokens.next() {
        let token = match token {
            TokenTree::Punct(punct) if punct.as_char() == '$' => {
                let TokenTree::Ident(name) = tokens.next()? else {
                    return None;
                };
                let index = arguments.iter().position(|argument| matches!(argument, Argument::Fragment(parameter, _) if name == parameter.as_str()))?;
                let marker =
                    TokenTree::Ident(Ident::new(&format!("{marker_prefix}_{index}"), name.span()));
                if matches!(&arguments[index], Argument::Fragment(_, kind) if kind == "block") {
                    let mut block = Group::new(Delimiter::Brace, TokenStream::from(marker));
                    block.set_span(name.span());
                    TokenTree::Group(block)
                } else {
                    marker
                }
            }
            TokenTree::Group(group) => {
                let mut replacement = Group::new(
                    group.delimiter(),
                    substitute(group.stream(), arguments, marker_prefix)?,
                );
                replacement.set_span(group.span());
                TokenTree::Group(replacement)
            }
            token => token,
        };
        out.extend([token]);
    }
    Some(out)
}
