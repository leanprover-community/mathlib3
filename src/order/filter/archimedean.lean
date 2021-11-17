/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import algebra.order.archimedean
import order.filter.at_top_bot

/-!
# `at_top` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `coe ∘ f : α → R` tends to `at_top` along a filter `l` if and only if so does `f`.
We also prove that `coe : ℕ → R` tends to `at_top` along `at_top`, as well as version of these
two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/

variables {α R : Type*}

open filter set

lemma tendsto_coe_nat_at_top_iff [ordered_semiring R] [nontrivial R] [archimedean R]
  {f : α → ℕ} {l : filter α} :
  tendsto (λ n, (f n : R)) l at_top ↔ tendsto f l at_top :=
tendsto_at_top_embedding (assume a₁ a₂, nat.cast_le) exists_nat_ge

lemma tendsto_coe_nat_at_top_at_top [ordered_semiring R] [archimedean R] :
  tendsto (coe : ℕ → R) at_top at_top :=
nat.mono_cast.tendsto_at_top_at_top exists_nat_ge

lemma tendsto_coe_int_at_top_iff [ordered_ring R] [nontrivial R] [archimedean R]
  {f : α → ℤ} {l : filter α} :
  tendsto (λ n, (f n : R)) l at_top ↔ tendsto f l at_top :=
tendsto_at_top_embedding (assume a₁ a₂, int.cast_le) $
  assume r, let ⟨n, hn⟩ := exists_nat_ge r in ⟨(n:ℤ), hn⟩

lemma tendsto_coe_int_at_top_at_top [ordered_ring R] [archimedean R] :
  tendsto (coe : ℤ → R) at_top at_top :=
int.cast_mono.tendsto_at_top_at_top $ λ b,
  let ⟨n, hn⟩ := exists_nat_ge b in ⟨n, hn⟩

lemma tendsto_coe_rat_at_top_iff [linear_ordered_field R] [archimedean R]
  {f : α → ℚ} {l : filter α} :
  tendsto (λ n, (f n : R)) l at_top ↔ tendsto f l at_top :=
tendsto_at_top_embedding (assume a₁ a₂, rat.cast_le) $
  assume r, let ⟨n, hn⟩ := exists_nat_ge r in ⟨(n:ℚ), by assumption_mod_cast⟩

lemma at_top_countable_basis_of_archimedean [linear_ordered_semiring R] [archimedean R] :
  (at_top : filter R).has_countable_basis (λ n : ℕ, true) (λ n, Ici n) :=
{ countable := countable_encodable _,
  to_has_basis := at_top_basis.to_has_basis
    (λ x hx, let ⟨n, hn⟩ := exists_nat_ge x in ⟨n, trivial, Ici_subset_Ici.2 hn⟩)
    (λ n hn, ⟨n, trivial, subset.rfl⟩) }

lemma at_bot_countable_basis_of_archimedean [linear_ordered_ring R] [archimedean R] :
  (at_bot : filter R).has_countable_basis (λ m : ℤ, true) (λ m, Iic m) :=
{ countable := countable_encodable _,
  to_has_basis := at_bot_basis.to_has_basis
    (λ x hx, let ⟨m, hm⟩ := exists_int_lt x in ⟨m, trivial, Iic_subset_Iic.2 hm.le⟩)
    (λ m hm, ⟨m, trivial, subset.rfl⟩) }

@[priority 100]
instance at_top_countably_generated_of_archimedean [linear_ordered_semiring R] [archimedean R] :
  (at_top : filter R).is_countably_generated :=
at_top_countable_basis_of_archimedean.is_countably_generated

@[priority 100]
instance at_bot_countably_generated_of_archimedean [linear_ordered_ring R] [archimedean R] :
  (at_bot : filter R).is_countably_generated :=
at_bot_countable_basis_of_archimedean.is_countably_generated

variables [linear_ordered_semiring R] [archimedean R]
variables {l : filter α} {f : α → R} {r : R}

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.const_mul_at_top`). -/
lemma filter.tendsto.const_mul_at_top' (hr : 0 < r) (hf : tendsto f l at_top) :
  tendsto (λx, r * f x) l at_top :=
begin
  apply tendsto_at_top.2 (λb, _),
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := archimedean.arch 1 hr,
  rw nsmul_eq_mul' at hn,
  filter_upwards [tendsto_at_top.1 hf (n * max b 0)],
  assume x hx,
  calc b ≤ 1 * max b 0 : by { rw [one_mul], exact le_max_left _ _ }
  ... ≤ (r * n) * max b 0 : mul_le_mul_of_nonneg_right hn (le_max_right _ _)
  ... = r * (n * max b 0) : by rw [mul_assoc]
  ... ≤ r * f x : mul_le_mul_of_nonneg_left hx (le_of_lt hr)
end

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.at_top_mul_const`). -/
lemma filter.tendsto.at_top_mul_const' (hr : 0 < r) (hf : tendsto f l at_top) :
  tendsto (λx, f x * r) l at_top :=
begin
  apply tendsto_at_top.2 (λb, _),
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := archimedean.arch 1 hr,
  have hn' : 1 ≤ (n : R) * r, by rwa nsmul_eq_mul at hn,
  filter_upwards [tendsto_at_top.1 hf (max b 0 * n)],
  assume x hx,
  calc b ≤ max b 0 * 1 : by { rw [mul_one], exact le_max_left _ _ }
  ... ≤ max b 0 * (n * r) : mul_le_mul_of_nonneg_left hn' (le_max_right _ _)
  ... = (max b 0 * n) * r : by rw [mul_assoc]
  ... ≤ f x * r : mul_le_mul_of_nonneg_right hx (le_of_lt hr)
end
