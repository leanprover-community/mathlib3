/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.norm_cast

/-!
# A tactic to shift `ℕ` goals to `ℤ`

It is often easier to work in `ℤ`, where subtraction is well behaved, than in `ℕ` where it isn't.
`zify` is a tactic that casts goals and hypotheses about natural numbers to ones about integers.
It makes use of `push_cast`, part of the `norm_cast` family, for simplifying these goals.

## Implementation notes

`zify` is extensible.
TODO
-/

-- TODO: are these dangerout??
@[norm_cast]
lemma int.coe_nat_bit0 (n : ℕ) : ((bit0 n : ℕ) : ℤ) = bit0 (n : ℤ) := rfl

@[norm_cast]
lemma int.coe_nat_bit1 (n : ℕ) : ((bit1 n : ℕ) : ℤ) = bit1 (n : ℤ) := rfl

open tactic

namespace zify

@[user_attribute]
meta def zify_attr : user_attribute unit unit :=
{ name := `zify,
  descr := "",
  after_set := some $ λ n _ _, do
    d ← get_decl n,
    guard (d.type = `(expr → tactic  (expr × expr)))
      <|> fail "zify patterns must have type `expr → tactic (expr × expr)`" }

/-- Returns a list of all `zify` patterns in the context. -/
meta def get_patterns : tactic (list (expr → tactic  (expr × expr))) :=
attribute.get_instances `zify >>= mmap (λ t, mk_const t >>= eval_expr (expr → tactic (expr × expr)))

private meta def mk_app_tuple (lem : name) (lhs rhs : expr) (pe : pexpr) : tactic (expr × expr) :=
do type ← to_expr pe,
   eq_pf ← mk_app lem [lhs, rhs],
   return (type, eq_pf)

/-- A `zify` pattern for equalities and inequalities. -/
@[zify]
meta def comparison : expr → tactic (expr × expr)
| `(@has_le.le ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_le_coe_nat_iff lhs rhs ``((%%lhs : ℤ) ≤ %%rhs)
| `(@has_lt.lt ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_lt_coe_nat_iff lhs rhs ``((%%lhs : ℤ) < %%rhs)
| `(@ge ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_le_coe_nat_iff lhs rhs ``((%%lhs : ℤ) ≥ %%rhs)
| `(@gt ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_lt_coe_nat_iff lhs rhs ``((%%lhs : ℤ) > %%rhs)
| `(@eq ℕ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_eq_coe_nat_iff lhs rhs ``((%%lhs : ℤ) = %%rhs)
| _ := failed

end zify

/--
Given `e` a proposition about natural numbers,
`zify e` tries to translate it to a proposition `e'` about integers.
Returns `e'` and a proof that `e = e'`. -/
meta def tactic.zify (e : expr) : tactic (expr × expr) :=
do zify_patterns ← zify.get_patterns,
   (zv, iff_pf) ← zify_patterns.mfirst (λ f, f e),
   (s, _) ← mk_simp_set tt [`push_cast] [],
   (newe, cast_eq) ← simplify (s.erase [`int.coe_nat_succ]) [] zv,
   pex_pf ← mk_app `propext [iff_pf] >>= mk_eq_symm,
   prod.mk newe <$> mk_eq_trans pex_pf cast_eq

/--
Given `h` a proof of a proposition about natural numbers,
`zify_proof h` tries to translate it to a proof of a proposition about integers.
-/
meta def tactic.zify_proof (h : expr) : tactic expr :=
do (_, pf) ← infer_type h >>= tactic.zify,
   mk_eq_mp pf h

section

setup_tactic_parser

meta def tactic.interactive.zify (l : parse location) : tactic unit :=
do locs ← l.get_locals,
replace_at tactic.zify locs l.include_goal >>= guardb

end

example (a b c x y z : ℕ) (h : x*y*z < 0) : a + 3*b > c :=
begin
  zify at h ⊢,
end
