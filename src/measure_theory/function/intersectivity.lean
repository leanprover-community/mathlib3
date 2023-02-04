/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import measure_theory.function.lp_space

/-!
# Bergelson's intersectivity lemma

This file prove the Bergelson intersectivity lemma.

## TODO

Restate the theorem using the upper density of a set of naturals, once we have it.
-/

open measure_theory
open_locale ennreal

section
variables {α F : Type*} [measurable_space α] [normed_add_comm_group F] {μ : measure α} {x : ℝ}

lemma meas_lt_of_snorm_ess_sup_le (hx : snorm_ess_sup f μ ≤ x)
  (hf : is_bounded_under (≤) μ.ae f . is_bounded_default) : μ {y | x < f y} = 0 :=
by { simp_rw ←not_le, exact ae_le_of_ess_sup_le hx hf }

lemma meas_snorm_ess_sup_lt_nnnorm {f : α → F} : μ {a | snorm_ess_sup f μ < ‖f a‖₊} = 0 :=
begin

end

end

variables {α : Type*} [measurable_space α] {μ : measure α} [is_finite_measure μ] {s : ℕ → set α}
  {r : ℝ≥0∞}

/-- **Bergelson Intersectivity Lemma**: -/
lemma bergelson (hs : ∀ n, measurable_set (s n)) (hr : ∀ n, r ≤ μ (s n)) :
  ∃ t : set ℕ, t.infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.finite → 0 < μ (⋂ n ∈ u, s n) :=
begin
  let N : (α → ℝ) → set α := λ f, {x | snorm_ess_sup f μ < ‖f x‖₊},
  have hN : ∀ f, μ (N f) = 0,
  intro n,
  exact meas_snorm_ess_sup_lt_nnnorm,
end
