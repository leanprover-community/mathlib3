/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao
-/

import tactic.norm_cast
import data.rat.cast

/-!
# A tactic to shift `ℕ` or `ℤ` goals to `ℚ`

Note that this file is following from `zify`.

Division in `ℕ` and `ℤ` is not always working fine (e.g. (5 : ℕ) / 2 = 2), so it's easier
to work in `ℚ`, where division and subtraction are well behaved. `qify` can be used to cast goals
and hypotheses about natural numbers or integers to rational numbers. It makes use of `push_cast`,
part of the `norm_cast` family, to simplify these goals.

## Implementation notes

`qify` is extensible, using the attribute `@[qify]` to label lemmas used for moving propositions
from `ℕ` or `ℤ` to `ℚ`.
`qify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pq (a₁ : ℚ) ... (aₙ : ℚ) ↔ Pn a₁ ... aₙ`.
For example, `rat.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `qify` lemma.

`qify` is very nearly just `simp only with qify push_cast`. There are a few minor differences:
* `qify` lemmas are used in the opposite order of the standard simp form.
  E.g. we will rewrite with `rat.coe_nat_le_coe_nat_iff` from right to left.
* `qify` should fail if no `qify` lemma applies (i.e. it was unable to shift any proposition to ℚ).
  However, once this succeeds, it does not necessarily need to rewrite with any `push_cast` rules.
-/

open tactic

namespace qify

/--
The `qify` attribute is used by the `qify` tactic. It applies to lemmas that shift propositions
from `nat` or `int` to `rat`.

`qify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pq (a₁ : ℚ) ... (aₙ : ℚ) ↔ Pn a₁ ... aₙ` or
 `∀ a₁ ... aₙ : ℤ, Pq (a₁ : ℚ) ... (aₙ : ℚ) ↔ Pz a₁ ... aₙ`.
For example, `rat.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `qify` lemma.
-/
@[user_attribute]
meta def qify_attr : user_attribute simp_lemmas unit :=
{ name := `qify,
  descr := "Used to tag lemmas for use in the `qify` tactic",
  cache_cfg :=
    { mk_cache :=
        λ ns, mmap (λ n, do c ← mk_const n, return (c, tt)) ns >>= simp_lemmas.mk.append_with_symm,
      dependencies := [] } }

/--
Given an expression `e`, `lift_to_q e` looks for subterms of `e` that are propositions "about"
natural numbers or integers and change them to propositions about rational numbers.

Returns an expression `e'` and a proof that `e = e'`.

Includes `ge_iff_le` and `gt_iff_lt` in the simp set. These can't be tagged with `qify` as we
want to use them in the "forward", not "backward", direction.
-/
meta def lift_to_q (e : expr) : tactic (expr × expr) :=
do sl ← qify_attr.get_cache,
   sl ← sl.add_simp `ge_iff_le, sl ← sl.add_simp `gt_iff_lt,
   (e', prf, _) ← simplify sl [] e,
   return (e', prf)

@[qify] lemma rat.coe_nat_le_coe_nat_iff (a b : ℕ) : (a : ℚ) ≤ b ↔ a ≤ b := by simp
@[qify] lemma rat.coe_nat_lt_coe_nat_iff (a b : ℕ) : (a : ℚ) < b ↔ a < b := by simp
@[qify] lemma rat.coe_nat_eq_coe_nat_iff (a b : ℕ) : (a : ℚ) = b ↔ a = b := by simp
@[qify] lemma rat.coe_nat_ne_coe_nat_iff (a b : ℕ) : (a : ℚ) ≠ b ↔ a ≠ b := by simp

@[qify] lemma rat.coe_int_le_coe_int_iff (a b : ℤ) : (a : ℚ) ≤ b ↔ a ≤ b := by simp
@[qify] lemma rat.coe_int_lt_coe_int_iff (a b : ℤ) : (a : ℚ) < b ↔ a < b := by simp
@[qify] lemma rat.coe_int_eq_coe_int_iff (a b : ℤ) : (a : ℚ) = b ↔ a = b := by simp
@[qify] lemma rat.coe_int_ne_coe_int_iff (a b : ℤ) : (a : ℚ) ≠ b ↔ a ≠ b := by simp

end qify

/--
`qify extra_lems e` is used to shift propositions in `e` from `ℕ` or `ℤ` to `ℚ`.
This is often useful since `ℚ` has well-behaved division and subtraction.

The list of extra lemmas is used in the `push_cast` step.

Returns an expression `e'` and a proof that `e = e'`.-/
meta def tactic.qify (extra_lems : list simp_arg_type) : expr → tactic (expr × expr) := λ q,
do (q1, p1) ← qify.lift_to_q q <|> fail "failed to find an applicable qify lemma",
   (q2, p2) ← norm_cast.derive_push_cast extra_lems q1,
   prod.mk q2 <$> mk_eq_trans p1 p2

/--
A variant of `tactic.qify` that takes `h`, a proof of a proposition about natural numbers
or integers, and returns a proof of the qified version of that propositon.
-/
meta def tactic.qify_proof (extra_lems : list simp_arg_type) (h : expr) : tactic expr :=
do (_, pf) ← infer_type h >>= tactic.qify extra_lems,
   mk_eq_mp pf h

section

setup_tactic_parser

/--
The `qify` tactic is used to shift propositions from `ℕ` or `ℤ` to `ℚ`.
This is often useful since `ℚ` has well-behaved division and subtraction.

```lean
example (a b c : ℕ) (x y z : ℤ) (h : ¬ x*y*z < 0) : c < a + 3*b :=
begin
  qify,
  qify at h,
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
end
```

`qify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of subtraction and division: passing `≤` or `∣` arguments will allow `push_cast`
to do more work.
```
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : false :=
begin
  qify [hab] at h,
  /- h : ↑a - ↑b < ↑c -/
end
```

```
example (a b c : ℕ) (h : a / b = c) (hab : b ∣ a) : false :=
begin
  qify [hab] at h,
  /- h : ↑a / ↑b = ↑c -/
end
```

`qify` makes use of the `@[qify]` attribute to move propositions,
and the `push_cast` tactic to simplify the `ℚ`-valued expressions.
-/
meta def tactic.interactive.qify (sl : parse simp_arg_list) (l : parse location) : tactic unit :=
do locs ← l.get_locals,
replace_at (tactic.qify sl) locs l.include_goal >>= guardb

end

add_tactic_doc
{ name := "qify",
  category := doc_category.attr,
  decl_names := [`qify.qify_attr],
  tags := ["coercions", "transport"] }

add_tactic_doc
{ name := "qify",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.qify],
  tags := ["coercions", "transport"] }
