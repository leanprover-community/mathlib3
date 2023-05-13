/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import analysis.special_functions.pow_nnreal

/-!
# Tactics for power functions

This file contains extensions to the `norm_num` and `positivity` tactics to handle power operations
on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/

open_locale nnreal ennreal

/-!
## Complex case
-/

namespace norm_num

theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, hb, complex.cpow_nat_cast]

theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ)
  (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, hb, complex.cpow_neg, complex.cpow_nat_cast]

end norm_num

/-!
## Real case
-/

namespace norm_num
open tactic

theorem rpow_pos (a b : ℝ) (b' : ℕ) (c : ℝ) (hb : (b':ℝ) = b) (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, ← hb, real.rpow_nat_cast]

theorem rpow_neg (a b : ℝ) (b' : ℕ) (c c' : ℝ)
  (a0 : 0 ≤ a) (hb : (b':ℝ) = b) (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, ← hb, real.rpow_neg a0, real.rpow_nat_cast]

/-- Evaluate `real.rpow a b` where `a` is a rational numeral and `b` is an integer.
(This cannot go via the generalized version `prove_rpow'` because `rpow_pos` has a side condition;
we do not attempt to evaluate `a ^ b` where `a` and `b` are both negative because it comes
out to some garbage.) -/
meta def prove_rpow (a b : expr) : tactic (expr × expr) := do
  na ← a.to_rat,
  ic ← mk_instance_cache `(ℝ),
  match match_sign b with
  | sum.inl b := do
    (ic, a0) ← guard (na ≥ 0) >> prove_nonneg ic a,
    nc ← mk_instance_cache `(ℕ),
    (ic, nc, b', hb) ← prove_nat_uncast ic nc b,
    (ic, c, h) ← prove_pow a na ic b',
    cr ← c.to_rat,
    (ic, c', hc) ← prove_inv ic c cr,
    pure (c', (expr.const ``rpow_neg []).mk_app [a, b, b', c, c', a0, hb, h, hc])
  | sum.inr ff := pure (`(1:ℝ), expr.const ``real.rpow_zero [] a)
  | sum.inr tt := do
    nc ← mk_instance_cache `(ℕ),
    (ic, nc, b', hb) ← prove_nat_uncast ic nc b,
    (ic, c, h) ← prove_pow a na ic b',
    pure (c, (expr.const ``rpow_pos []).mk_app [a, b, b', c, hb, h])
  end

end norm_num

namespace tactic
namespace positivity

/-- Auxiliary definition for the `positivity` tactic to handle real powers of reals. -/
meta def prove_rpow (a b : expr) : tactic strictness :=
do
  strictness_a ← core a,
  match strictness_a with
  | nonnegative p := nonnegative <$> mk_app ``real.rpow_nonneg_of_nonneg [p, b]
  | positive p := positive <$> mk_app ``real.rpow_pos_of_pos [p, b]
  | _ := failed
  end

end positivity
end tactic

/-!
## General-purpose tactics

The following code covers all the cases `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞` together.
-/

namespace norm_num
open tactic

/-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
meta def prove_rpow' (pos neg zero : name) (α β one a b : expr) : tactic (expr × expr) := do
  na ← a.to_rat,
  icα ← mk_instance_cache α,
  icβ ← mk_instance_cache β,
  match match_sign b with
  | sum.inl b := do
    nc ← mk_instance_cache `(ℕ),
    (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b,
    (icα, c, h) ← prove_pow a na icα b',
    cr ← c.to_rat,
    (icα, c', hc) ← prove_inv icα c cr,
    pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
  | sum.inr ff := pure (one, expr.const zero [] a)
  | sum.inr tt := do
    nc ← mk_instance_cache `(ℕ),
    (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b,
    (icα, c, h) ← prove_pow a na icα b',
    pure (c, (expr.const pos []).mk_app [a, b, b', c, hb, h])
  end

open_locale nnreal ennreal

theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0)
  (hb : b = b') (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, hb, nnreal.rpow_nat_cast]

theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0)
  (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, hb, nnreal.rpow_neg, nnreal.rpow_nat_cast]

theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞)
  (hb : b = b') (h : a ^ b' = c) : a ^ b = c :=
by rw [← h, hb, ennreal.rpow_nat_cast]

theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞)
  (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') : a ^ -b = c' :=
by rw [← hc, ← h, hb, ennreal.rpow_neg, ennreal.rpow_nat_cast]

/-- Evaluate `complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
meta def prove_cpow : expr → expr → tactic (expr × expr) :=
prove_rpow' ``cpow_pos ``cpow_neg ``complex.cpow_zero `(ℂ) `(ℂ) `(1:ℂ)

/-- Evaluate `nnreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
meta def prove_nnrpow : expr → expr → tactic (expr × expr) :=
prove_rpow' ``nnrpow_pos ``nnrpow_neg ``nnreal.rpow_zero `(ℝ≥0) `(ℝ) `(1:ℝ≥0)

/-- Evaluate `ennreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
meta def prove_ennrpow : expr → expr → tactic (expr × expr) :=
prove_rpow' ``ennrpow_pos ``ennrpow_neg ``ennreal.rpow_zero `(ℝ≥0∞) `(ℝ) `(1:ℝ≥0∞)

/-- Evaluates expressions of the form `rpow a b`, `cpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num] meta def eval_rpow_cpow : expr → tactic (expr × expr)
| `(@has_pow.pow _ _ real.has_pow %%a %%b) := b.to_int >> prove_rpow a b
| `(real.rpow %%a %%b) := b.to_int >> prove_rpow a b
| `(@has_pow.pow _ _ complex.has_pow %%a %%b) := b.to_int >> prove_cpow a b
| `(complex.cpow %%a %%b) := b.to_int >> prove_cpow a b
| `(@has_pow.pow _ _ nnreal.real.has_pow %%a %%b) := b.to_int >> prove_nnrpow a b
| `(nnreal.rpow %%a %%b) := b.to_int >> prove_nnrpow a b
| `(@has_pow.pow _ _ ennreal.real.has_pow %%a %%b) := b.to_int >> prove_ennrpow a b
| `(ennreal.rpow %%a %%b) := b.to_int >> prove_ennrpow a b
| _ := tactic.failed

end norm_num

namespace tactic
namespace positivity

private lemma nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b := nnreal.rpow_pos ha

/-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals. -/
meta def prove_nnrpow (a b : expr) : tactic strictness :=
do
  strictness_a ← core a,
  match strictness_a with
  | positive p := positive <$> mk_app ``nnrpow_pos [p, b]
  | _ := failed -- We already know `0 ≤ x` for all `x : ℝ≥0`
  end

private lemma ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
ennreal.rpow_pos_of_nonneg ha hb.le

/-- Auxiliary definition for the `positivity` tactic to handle real powers of extended nonnegative
reals. -/
meta def prove_ennrpow (a b : expr) : tactic strictness :=
do
  strictness_a ← core a,
  strictness_b ← core b,
  match strictness_a, strictness_b with
  | positive pa, positive pb := positive <$> mk_app ``ennrpow_pos [pa, pb]
  | positive pa, nonnegative pb := positive <$> mk_app ``ennreal.rpow_pos_of_nonneg [pa, pb]
  | _, _ := failed -- We already know `0 ≤ x` for all `x : ℝ≥0∞`
  end

end positivity

open positivity

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when the
base is nonnegative and positive when the base is positive. -/
@[positivity]
meta def positivity_rpow : expr → tactic strictness
| `(@has_pow.pow _ _ real.has_pow %%a %%b) := prove_rpow a b
| `(real.rpow %%a %%b) := prove_rpow a b
| `(@has_pow.pow _ _ nnreal.real.has_pow %%a %%b) := prove_nnrpow a b
| `(nnreal.rpow %%a %%b) := prove_nnrpow a b
| `(@has_pow.pow _ _ ennreal.real.has_pow %%a %%b) := prove_ennrpow a b
| `(ennreal.rpow %%a %%b) := prove_ennrpow a b
| _ := failed

end tactic
