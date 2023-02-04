/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import measure_theory.function.lp_space

/-!
# Bergelson's intersectivity lemma

This file proves the Bergelson intersectivity lemma.

## TODO

Restate the theorem using the upper density of a set of naturals, once we have it.
-/

open filter measure_theory set
open_locale ennreal nnreal

namespace with_top
variables {α : Type*} [preorder α] {s : set (with_top α)}

open_locale classical

lemma Sup_eq [has_Sup α] (hs : ⊤ ∉ s) (hs' : bdd_above (coe ⁻¹' s : set α)) :
  Sup s = ↑(Sup (coe ⁻¹' s) : α) :=
(if_neg hs).trans $ if_pos hs'

lemma Inf_eq [has_Inf α] (hs : ¬ s ⊆ {⊤}) : Inf s = ↑(Inf (coe ⁻¹' s) : α) := if_neg hs

end with_top

namespace function
variables {α β : Type*} [has_zero β] [has_one β] [ne_zero (1 : β)]

@[simp] lemma support_one : support (1 : α → β) = univ := support_const one_ne_zero
@[simp] lemma mul_support_zero : mul_support (0 : α → β) = univ := mul_support_const zero_ne_one

end function

section
variables {α M : Type*} [measurable_space α] {μ : measure α} [has_one M] {f : α → M} {s : set α}

@[to_additive]
lemma mul_indicator_ae_eq_one : s.mul_indicator f =ᵐ[μ] 1 ↔ μ (s ∩ f.mul_support) = 0 :=
by simpa [eventually_eq, eventually_iff, measure.ae, compl_set_of]

end

variables {α : Type*} [measurable_space α] {μ : measure α} [is_finite_measure μ] {s : ℕ → set α}
  {r : ℝ≥0∞}

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume. -/
lemma bergelson (hs : ∀ n, measurable_set (s n)) (hr : ∀ n, r ≤ μ (s n)) :
  ∃ t : set ℕ, t.infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.finite → 0 < μ (⋂ n ∈ u, s n) :=
begin
  let N : (α → ℝ) → set α := λ f, {x | snorm_ess_sup f μ < ‖f x‖₊},
  let M : set α := ⋃ u : finset ℕ, N (set.indicator (u.inf s) 1),
  have : μ M = 0 :=  measure_Union_null (λ u, meas_lt_of_snorm_ess_sup_le le_rfl
    ⟨1, eventually_map.2 $ eventually_of_forall $ _⟩),
  have : ∀ u : finset ℕ, (u.inf s \ M).nonempty → 0 < μ (u.inf s),
  { simp_rw pos_iff_ne_zero,
    rintro u ⟨x, hx⟩ hu,
    refine hx.2 (mem_Union.2 ⟨u, (_ : _ < _)⟩),
    rw [indicator_of_mem hx.1, snorm_ess_sup_eq_zero_iff.2],
    simp,
    rwa [_root_.indicator_ae_eq_zero, function.support_one, inter_univ] },
  sorry,
  rintro x,
  rw indicator,
  split_ifs; simp,
end
