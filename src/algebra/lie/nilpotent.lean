/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.solvable

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `lie_module.lower_central_series`
  * `lie_module.is_nilpotent`

## Tags

lie algebra, lower central series, nilpotent
-/

universes u v w w₁ w₂

namespace lie_module

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

/-- The lower central series of Lie submodules of a Lie module. -/
def lower_central_series (k : ℕ) : lie_submodule R L M := (λ I, ⁅(⊤ : lie_ideal R L), I⁆)^[k] ⊤

@[simp] lemma lower_central_series_zero : lower_central_series R L M 0 = ⊤ := rfl

@[simp] lemma lower_central_series_succ (k : ℕ) :
  lower_central_series R L M (k + 1) = ⁅(⊤ : lie_ideal R L), lower_central_series R L M k⁆ :=
function.iterate_succ_apply' (λ I, ⁅(⊤ : lie_ideal R L), I⁆) k ⊤

lemma trivial_iff_lower_central_eq_bot : is_trivial L M ↔ lower_central_series R L M 1 = ⊥ :=
begin
  split; intros h,
  { erw [eq_bot_iff, lie_submodule.lie_span_le], rintros m ⟨x, n, hn⟩, rw [← hn, h.trivial], simp,},
  { rw lie_submodule.eq_bot_iff at h, apply is_trivial.mk, intros x m, apply h,
    apply lie_submodule.subset_lie_span, use [x, m], refl, },
end

open lie_algebra

lemma derived_series_le_lower_central_series (k : ℕ) :
  derived_series R L k ≤ lower_central_series R L L k :=
begin
  induction k with k h,
  { exact le_refl _, },
  { have h' : derived_series R L k ≤ ⊤, { by simp only [le_top], },
    rw [derived_series_def, derived_series_of_ideal_succ, lower_central_series_succ],
    exact lie_submodule.mono_lie _ _ _ _ h' h, },
end

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
class is_nilpotent : Prop :=
(nilpotent : ∃ k, lower_central_series R L M k = ⊥)

@[priority 100]
instance trivial_is_nilpotent [is_trivial L M] : is_nilpotent R L M :=
⟨by { use 1, change ⁅⊤, ⊤⁆ = ⊥, simp, }⟩

end lie_module

@[priority 100]
instance lie_algebra.is_solvable_of_is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [hL : lie_module.is_nilpotent R L L] :
  lie_algebra.is_solvable R L :=
begin
  obtain ⟨k, h⟩ : ∃ k, lie_module.lower_central_series R L L k = ⊥ := hL.nilpotent,
  use k, rw ← le_bot_iff at h ⊢,
  exact le_trans (lie_module.derived_series_le_lower_central_series R L k) h,
end
