/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.norm_cast
import data.int.basic

/-!
# A tactic to shift `ℕ` goals to `ℤ`

It is often easier to work in `ℤ`, where subtraction is well behaved, than in `ℕ` where it isn't.
`zify` is a tactic that casts goals and hypotheses about natural numbers to ones about integers.
It makes use of `push_cast`, part of the `norm_cast` family, to simplify these goals.

## Implementation notes

`zify` is extensible, using the attribute `@[zify]` to label lemmas used for moving propositions
from `ℕ` to `ℤ`.
`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.

`zify` is very nearly just `simp only with zify push_cast`. There are a few minor differences:
* `zify` lemmas are used in the opposite order of the standard simp form.
  E.g. we will rewrite with `int.coe_nat_le_coe_nat_iff` from right to left.
* `zify` should fail if no `zify` lemma applies (i.e. it was unable to shift any proposition to ℤ).
  However, once this succeeds, it does not necessarily need to rewrite with any `push_cast` rules.
-/

open tactic

namespace zify

/--
The `zify` attribute is used by the `zify` tactic. It applies to lemmas that shift propositions
between `nat` and `int`.

`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.
-/
@[user_attribute]
meta def zify_attr : user_attribute simp_lemmas unit :=
{ name := `zify,
  descr := "Used to tag lemmas for use in the `zify` tactic",
  cache_cfg :=
    { mk_cache :=
        λ ns, mmap (λ n, do c ← mk_const n, return (c, tt)) ns >>= simp_lemmas.mk.append_with_symm,
      dependencies := [] } }

/--
Given an expression `e`, `lift_to_z e` looks for subterms of `e` that are propositions "about"
natural numbers and change them to propositions about integers.

Returns an expression `e'` and a proof that `e = e'`.

Includes `ge_iff_le` and `gt_iff_lt` in the simp set. These can't be tagged with `zify` as we
want to use them in the "forward", not "backward", direction.
-/
meta def lift_to_z (e : expr) : tactic (expr × expr) :=
do sl ← zify_attr.get_cache,
   sl ← sl.add_simp `ge_iff_le, sl ← sl.add_simp `gt_iff_lt,
   simplify sl [] e

/--
A small variant of `push_cast` suited for non-interactive use.

`push_casts e` returns an expression `e'` and a proof that `e = e'`.
-/
meta def push_casts (e : expr) : tactic (expr × expr) :=
do (s, _) ← mk_simp_set tt [`push_cast] [],
   simplify (s.erase [`int.coe_nat_succ]) [] e {fail_if_unchanged := ff}

attribute [zify] int.coe_nat_le_coe_nat_iff int.coe_nat_lt_coe_nat_iff int.coe_nat_eq_coe_nat_iff

end zify

/--
`zify e` is used to shift propositions in `e` from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

Returns an expression `e'` and a proof that `e = e'`.-/
meta def tactic.zify : expr → tactic (expr × expr) := λ z,
do (z1, p1) ← zify.lift_to_z z <|> fail "failed to find an applicable zify lemma",
   (z2, p2) ← zify.push_casts z1,
   prod.mk z2 <$> mk_eq_trans p1 p2

/--
A variant of `tactic.zify` that takes `h`, a proof of a proposition about natural numbers,
and returns a proof of the zified version of that propositon.
-/
meta def tactic.zify_proof (h : expr) : tactic expr :=
do (_, pf) ← infer_type h >>= tactic.zify,
   mk_eq_mp pf h

section

setup_tactic_parser

/--
The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

```lean
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b :=
begin
  zify,
  zify at h,
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/

`zify` makes use of the `@[zify]` attribute to move propositions,
and the `push_cast` tactic to simplify the `ℤ`-valued expressions.
end
```
-/
meta def tactic.interactive.zify (l : parse location) : tactic unit :=
do locs ← l.get_locals,
replace_at tactic.zify locs l.include_goal >>= guardb

end

add_tactic_doc
{ name := "zify",
  category := doc_category.attr,
  decl_names := [`zify.zify_attr] }

add_tactic_doc
{ name := "zify",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.zify] }
