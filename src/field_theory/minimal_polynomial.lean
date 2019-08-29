/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/

import ring_theory.adjoin_root
import ring_theory.integral_closure

universes u v w
open polynomial set function

namespace polynomial
variables {α : Type*} [decidable_eq α] [comm_semiring α]

@[simp] lemma monic.leading_coeff {p : polynomial α} (hp : p.monic) :
  leading_coeff p = 1 := hp

lemma degree_eq_iff_nat_degree_eq {p : polynomial α} {n : ℕ} (hp : p ≠ 0) :
  p.degree = n ↔ p.nat_degree = n :=
by rw [degree_eq_nat_degree hp, with_bot.coe_eq_coe]

lemma degree_eq_iff_nat_degree_eq_of_pos {p : polynomial α} {n : ℕ} (hn : n > 0) :
  p.degree = n ↔ p.nat_degree = n :=
begin
  split,
  { intro H, rwa ← degree_eq_iff_nat_degree_eq, rintro rfl,
    rw degree_zero at H, exact option.no_confusion H },
  { intro H, rwa degree_eq_iff_nat_degree_eq, rintro rfl,
    rw nat_degree_zero at H, linarith }
end

instance coeff.is_add_group_hom {n : ℕ} : is_add_monoid_hom (λ p : polynomial α, p.coeff n) :=
{ map_add  := λ p q, coeff_add p q n,
  map_zero := coeff_zero _ }

lemma coeff_eq_zero_degree_lt {p : polynomial α} {n : ℕ} (h : p.degree < n) :
  p.coeff n = 0 :=
begin
  suffices : n ∉ p.support, { rwa finsupp.not_mem_support_iff at this },
  contrapose! h,
  apply finset.le_sup h
end

lemma coeff_eq_zero_nat_degree_lt {p : polynomial α} {n : ℕ} (h : p.nat_degree < n) :
  p.coeff n = 0 :=
begin
  apply coeff_eq_zero_degree_lt,
  by_cases hp : p = 0,
  { subst hp, exact with_bot.bot_lt_coe n },
  { rwa [degree_eq_nat_degree hp, with_bot.coe_lt_coe] }
end

lemma as_sum (p : polynomial α) :
  p = (finset.range (p.nat_degree + 1)).sum (λ i, C (p.coeff i) * X^i) :=
begin
  rw ext, intro n, symmetry,
  calc _ = _ : (finset.sum_hom (λ q : polynomial α, q.coeff n)).symm
     ... = _ :
  begin
    rw finset.sum_eq_single n;
    try { simp only [mul_one, coeff_X_pow, if_pos rfl, coeff_C_mul], },
    { intros i hi hne, rw [if_neg hne.symm, mul_zero] },
    { intro h, rw [finset.mem_range, not_lt] at h,
      exact coeff_eq_zero_nat_degree_lt h }
  end
end

lemma zero_is_root_of_coeff_zero_eq_zero {p : polynomial α} (hp : p.coeff 0 = 0) :
  is_root p 0 :=
begin
  rw p.as_sum,
  calc _ = _ : (finset.sum_hom _).symm
      ... = _ : finset.sum_eq_zero $
  begin
    intros i hi, clear hi,
    by_cases hi : i = 0, { rw [hi, hp, C_0, zero_mul, eval_zero] },
    rw [eval_mul, eval_pow, eval_X, zero_pow (nat.pos_of_ne_zero hi), mul_zero]
  end
end

end polynomial

noncomputable theory

/- Turn down the instance priority for subtype.decidable_eq and use classical.dec_eq everywhere,
  to avoid diamonds -/
local attribute [instance, priority 0] subtype.decidable_eq

variables {α : Type u} {β : Type v}

section min_poly_def
variables [decidable_eq α] [decidable_eq β] [comm_ring α] [comm_ring β] [algebra α β]

def minimal_polynomial {x : β} (hx : is_integral α x) : polynomial α :=
well_founded.min polynomial.degree_lt_wf _ (ne_empty_iff_exists_mem.mpr hx)

end min_poly_def

namespace minimal_polynomial

section ring
variables [decidable_eq α] [decidable_eq β] [comm_ring α] [comm_ring β] [algebra α β]
variables {x : β} (hx : is_integral α x)

lemma monic : monic (minimal_polynomial hx) :=
(well_founded.min_mem degree_lt_wf _ (ne_empty_iff_exists_mem.mpr hx)).1

@[simp] lemma aeval : aeval α β x (minimal_polynomial hx) = 0 :=
(well_founded.min_mem degree_lt_wf _ (ne_empty_iff_exists_mem.mpr hx)).2

lemma min {p : polynomial α} (pmonic : p.monic) (hp : polynomial.aeval α β x p = 0) :
  degree (minimal_polynomial hx) ≤ degree p :=
le_of_not_lt $ well_founded.not_lt_min degree_lt_wf _ (ne_empty_iff_exists_mem.mpr hx) ⟨pmonic, hp⟩

end ring

section field
variables [discrete_field α] [discrete_field β] [algebra α β]
variables {x : β} (hx : is_integral α x)

lemma ne_zero : (minimal_polynomial hx) ≠ 0 := ne_zero_of_monic (monic hx)

lemma degree_le_of_ne_zero {p : polynomial α} (pnz : p ≠ 0) (hp : polynomial.aeval α β x p = 0) :
  degree (minimal_polynomial hx) ≤ degree p :=
begin
  rw ← degree_mul_leading_coeff_inv p pnz,
  apply min _ (monic_mul_leading_coeff_inv pnz),
  simp [hp]
end

lemma unique {p : polynomial α} (pmonic : p.monic) (hp : polynomial.aeval α β x p = 0)
  (pmin : ∀ q : polynomial α, q.monic → polynomial.aeval α β x q = 0 → degree p ≤ degree q) :
  p = minimal_polynomial hx :=
begin
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := degree_le_of_ne_zero hx hnz (by simp [hp]),
  contrapose! this,
  apply degree_sub_lt _ (ne_zero hx),
  { rw [(monic hx).leading_coeff, pmonic.leading_coeff] },
  { exact le_antisymm (min hx pmonic hp) (pmin (minimal_polynomial hx) (monic hx) (aeval hx)) },
end

lemma dvd {p : polynomial α} (hp : polynomial.aeval α β x p = 0) :
  minimal_polynomial hx ∣ p :=
begin
  rw ← dvd_iff_mod_by_monic_eq_zero (monic hx),
  by_contra hnz,
  have := degree_le_of_ne_zero hx hnz _,
  { contrapose! this,
    exact degree_mod_by_monic_lt _ (monic hx) (ne_zero hx) },
  { rw ← mod_by_monic_add_div p (monic hx) at hp,
    simpa using hp }
end

lemma degree_ne_zero : degree (minimal_polynomial hx) ≠ 0 :=
begin
  assume deg_eq_zero,
  have ndeg_eq_zero : nat_degree (minimal_polynomial hx) = 0,
  { simpa using congr_arg nat_degree (eq_C_of_degree_eq_zero deg_eq_zero) },
  have eq_one : minimal_polynomial hx = 1,
  { rw eq_C_of_degree_eq_zero deg_eq_zero, congr,
    simpa [ndeg_eq_zero.symm] using (monic hx).leading_coeff },
  simpa [eq_one, aeval_def] using aeval hx
end

lemma not_is_unit : ¬ is_unit (minimal_polynomial hx) :=
begin
  intro H, apply degree_ne_zero hx,
  exact degree_eq_zero_of_is_unit H
end

lemma degree_pos : 0 < degree (minimal_polynomial hx) :=
degree_pos_of_ne_zero_of_nonunit (ne_zero hx) (not_is_unit hx)

lemma prime : prime (minimal_polynomial hx) :=
begin
  refine ⟨ne_zero hx, not_is_unit hx, _⟩,
  rintros p q ⟨d, h⟩,
  have :    polynomial.aeval α β x (p*q) = 0 := by simp [h, aeval hx],
  replace : polynomial.aeval α β x p = 0 ∨ polynomial.aeval α β x q = 0 := by simpa,
  cases this; [left, right]; apply dvd; assumption
end

lemma irreducible : irreducible (minimal_polynomial hx) :=
irreducible_of_prime (prime hx)

lemma root {x : β} (hx : is_integral α x) {y : α}
  (h : is_root (minimal_polynomial hx) y) : algebra_map β y = x :=
begin
  have ndeg_one : nat_degree (minimal_polynomial hx) = 1,
  { rw ← polynomial.degree_eq_iff_nat_degree_eq_of_pos (nat.zero_lt_one),
    exact degree_eq_one_of_irreducible_of_root (irreducible hx) h },
  have coeff_one : (minimal_polynomial hx).coeff 1 = 1,
  { simpa [ndeg_one, leading_coeff] using (monic hx).leading_coeff },
  have hy : y = - coeff (minimal_polynomial hx) 0,
  { rw (minimal_polynomial hx).as_sum at h,
    apply eq_neg_of_add_eq_zero,
    simpa [ndeg_one, finset.sum_range_succ, coeff_one] using h },
  subst y,
  rw [algebra.map_neg, neg_eq_iff_add_eq_zero],
  have H := aeval hx,
  rw (minimal_polynomial hx).as_sum at H,
  simpa [ndeg_one, finset.sum_range_succ, coeff_one, aeval_def] using H
end

lemma coeff_zero_ne_zero (h : x ≠ 0) : coeff (minimal_polynomial hx) 0 ≠ 0 :=
begin
  contrapose! h,
  have zero_root := polynomial.zero_is_root_of_coeff_zero_eq_zero h,
  rw ← root hx zero_root,
  exact is_ring_hom.map_zero _
end

end field

end minimal_polynomial
