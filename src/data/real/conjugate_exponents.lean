/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import data.real.basic

/-!
# Real conjugate exponents

`p.is_conjugate_exponent q` registers the fact that the real numbers `p` and `q` are `> 1` and
satisfy `1/p + 1/q = 1`. This property shows up often in analysis, especially when dealing with
`L^p` spaces.

We make several basic facts available through dot notation in this situation.

We also introduce `p.conjugate_exponent` for `p / (p-1)`. When `p > 1`, it is conjugate to `p`.
-/

noncomputable theory
namespace real

/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
structure is_conjugate_exponent (p q : ℝ) : Prop :=
(one_lt : 1 < p)
(inv_add_inv_conj : 1/p + 1/q = 1)

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjugate_exponent (p : ℝ) : ℝ := p/(p-1)

namespace is_conjugate_exponent

variables {p q : ℝ} (h : p.is_conjugate_exponent q)
include h

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
lemma pos : 0 < p :=
lt_trans zero_lt_one h.one_lt

lemma nonneg : 0 ≤ p := le_of_lt h.pos

lemma ne_zero : p ≠ 0 :=
ne_of_gt h.pos

lemma sub_one_pos : 0 < p - 1 :=
sub_pos.2 h.one_lt

lemma sub_one_ne_zero : p - 1 ≠ 0 :=
ne_of_gt h.sub_one_pos

lemma one_div_pos : 0 < 1/p :=
one_div_pos_of_pos h.pos

lemma one_div_nonneg : 0 ≤ 1/p :=
le_of_lt h.one_div_pos

lemma one_div_ne_zero : 1/p ≠ 0 :=
ne_of_gt (h.one_div_pos)

lemma conj_eq : q = p/(p-1) :=
begin
  have := h.inv_add_inv_conj,
  rw [← eq_sub_iff_add_eq', one_div_eq_inv, inv_eq_iff] at this,
  field_simp [← this, h.ne_zero]
end

lemma conjugate_eq : conjugate_exponent p = q := h.conj_eq.symm

lemma sub_one_mul_conj : (p - 1) * q = p :=
mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq

lemma mul_eq_add : p * q = p + q :=
by simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj

@[symm] protected lemma symm : q.is_conjugate_exponent p :=
{ one_lt := by { rw [h.conj_eq], exact one_lt_div_of_lt _ h.sub_one_pos (sub_one_lt p) },
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj }

end is_conjugate_exponent

lemma is_conjugate_exponent_iff {p q : ℝ} (h : 1 < p) :
  p.is_conjugate_exponent q ↔ q = p/(p-1) :=
⟨λ H, H.conj_eq, λ H, ⟨h, by field_simp [H, ne_of_gt (lt_trans zero_lt_one h)]⟩⟩

lemma is_conjugate_exponent_conjugate_exponent {p : ℝ} (h : 1 < p) :
  p.is_conjugate_exponent (conjugate_exponent p) :=
(is_conjugate_exponent_iff h).2 rfl

end real
