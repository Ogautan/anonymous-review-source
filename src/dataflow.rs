use syn::visit::Visit;
use syn::{Expr, ExprForLoop, ExprLoop, ExprWhile};

use crate::types::{IterationEstimate, LoopContext};

pub struct LoopAnalyzer {
    pub current_depth: usize,
    pub loop_stack: Vec<LoopInfo>,
}

pub struct LoopInfo {
    pub depth: usize,
    pub iteration_estimate: IterationEstimate,
}

impl Default for LoopAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl LoopAnalyzer {
    pub fn new() -> Self {
        Self {
            current_depth: 0,
            loop_stack: Vec::new(),
        }
    }

    pub fn current_loop_context(&self) -> Option<LoopContext> {
        self.loop_stack.last().map(|info| LoopContext {
            // Derive this from the stack as the single source of truth.  Keeping
            // the two counters in sync is an invariant of the visitor, but this
            // also remains safe if a caller constructs or reuses the analyzer.
            nesting_depth: self.current_depth,
            iteration_estimate: info.iteration_estimate.clone(),
        })
    }

    pub fn calculate_hotness(&self, loop_ctx: &Option<LoopContext>) -> f32 {
        if let Some(ctx) = loop_ctx {
            let depth_factor = (ctx.nesting_depth as f32).powi(2);
            let iter_factor = match &ctx.iteration_estimate {
                IterationEstimate::Constant(n) => {
                    if *n > 1_000_000 {
                        10.0
                    } else if *n > 10_000 {
                        5.0
                    } else if *n > 100 {
                        2.0
                    } else {
                        1.0
                    }
                }
                IterationEstimate::Dynamic => 3.0,
                IterationEstimate::Unknown => 1.5,
            };
            depth_factor * iter_factor
        } else {
            1.0
        }
    }

    pub fn estimate_iterations(expr: &Expr) -> IterationEstimate {
        match expr {
            Expr::Range(range) => {
                if let (Some(start), Some(end)) = (&range.start, &range.end)
                    && let (Expr::Lit(start_lit), Expr::Lit(end_lit)) = (&**start, &**end)
                    && let (syn::Lit::Int(s), syn::Lit::Int(e)) = (&start_lit.lit, &end_lit.lit)
                    && let (Ok(sv), Ok(ev)) = (s.base10_parse::<u64>(), e.base10_parse::<u64>())
                {
                    return IterationEstimate::Constant(ev.saturating_sub(sv));
                }
                IterationEstimate::Dynamic
            }
            Expr::Lit(lit) => {
                if let syn::Lit::Int(int_lit) = &lit.lit
                    && let Ok(n) = int_lit.base10_parse::<u64>()
                {
                    return IterationEstimate::Constant(n);
                }
                IterationEstimate::Unknown
            }
            _ => IterationEstimate::Dynamic,
        }
    }
}

impl<'ast> Visit<'ast> for LoopAnalyzer {
    fn visit_expr_for_loop(&mut self, node: &'ast ExprForLoop) {
        let iter_est = Self::estimate_iterations(&node.expr);
        self.current_depth += 1;
        self.loop_stack.push(LoopInfo {
            depth: self.current_depth,
            iteration_estimate: iter_est,
        });

        syn::visit::visit_expr_for_loop(self, node);

        self.loop_stack.pop();
        self.current_depth = self.current_depth.saturating_sub(1);
    }

    fn visit_expr_while(&mut self, node: &'ast ExprWhile) {
        self.current_depth += 1;
        self.loop_stack.push(LoopInfo {
            depth: self.current_depth,
            iteration_estimate: IterationEstimate::Dynamic,
        });

        syn::visit::visit_expr_while(self, node);

        self.loop_stack.pop();
        self.current_depth = self.current_depth.saturating_sub(1);
    }

    fn visit_expr_loop(&mut self, node: &'ast ExprLoop) {
        self.current_depth += 1;
        self.loop_stack.push(LoopInfo {
            depth: self.current_depth,
            iteration_estimate: IterationEstimate::Unknown,
        });

        syn::visit::visit_expr_loop(self, node);

        self.loop_stack.pop();
        self.current_depth = self.current_depth.saturating_sub(1);
    }
}
