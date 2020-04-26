/-
Copyright (c) 2020 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex J. Best

Factor naturals inside of a conv.
-/
import data.nat.prime
import tactic.converter.interactive
import tactic.norm_num

namespace conv
open tactic

/-- `to_factors_aux` tactic factors a `nat` expression into prime factors,
returning a proof that the original expession is product of these factors,
expanded as a sequence of `mul`'s. The tactic does not provide proofs that
the factors are indeed prime. -/
meta def to_factors_aux : expr → tactic (expr × expr) :=
λ e₁, do
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  match α with
  | `(nat) := do

    n₁ ← e₁.to_nat,
    factors_expr ← mk_app ``nat.factors [e₁],
    factors_list ← eval_expr (list ℕ) factors_expr,

    factor_prod ← (mk_app ``list.prod [reflect factors_list]),
    (mul_expr, p_mul) ← expr.simp factor_prod {} failed tt []
      [simp_arg_type.expr (expr.const `list.prod_cons []),
      simp_arg_type.expr (expr.const `list.prod_nil []),
      simp_arg_type.expr (expr.const `nat.mul_one [])],
    p ← to_expr ``(by norm_num : %%e₁ = %%mul_expr),
    return (mul_expr, p)
  | _ := failed
  end

/-- The `to_factors` tactic factors a `nat` into prime factors inside of a `conv` block.
The number to be factored must be the current target. -/
meta def to_factors : conv unit := conv.replace_lhs to_factors_aux

end conv
