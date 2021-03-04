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

section nilpotent_algebras

-- TODO Generalise the below to Lie modules if / when we define morphisms, equivs of Lie modules
-- covering a Lie algebra morphism of (possibly different) Lie algebras.

variables (R : Type u) (L : Type v) (L' : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']

/-- We say a Lie algebra is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
abbreviation lie_algebra.is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] : Prop :=
lie_module.is_nilpotent R L L

variables {R L L'}
open lie_algebra
open lie_module (lower_central_series)

lemma lie_ideal.lower_central_series_map_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
  lie_ideal.map f (lower_central_series R L L k) ≤ lower_central_series R L' L' k :=
begin
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero, le_top], },
  { simp only [lie_module.lower_central_series_succ],
    exact le_trans (lie_ideal.map_bracket_le f) (lie_submodule.mono_lie _ _ _ _ le_top ih), },
end

lemma lie_ideal.lower_central_series_map_eq (k : ℕ) {f : L →ₗ⁅R⁆ L'}
  (h : function.surjective f) :
  lie_ideal.map f (lower_central_series R L L k) = lower_central_series R L' L' k :=
begin
  have h' : (⊤ : lie_ideal R L).map f = ⊤, { exact f.ideal_range_eq_top_of_surjective h, },
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero], exact h', },
  { simp only [lie_module.lower_central_series_succ, lie_ideal.map_bracket_eq f h, ih, h'], },
end

lemma function.injective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L'] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.injective f) : is_nilpotent R L :=
{ nilpotent :=
  begin
    tactic.unfreeze_local_instances, obtain ⟨k, hk⟩ := h₁,
    use k,
    apply lie_ideal.bot_of_map_eq_bot h₂, rw [eq_bot_iff, ← hk],
    apply lie_ideal.lower_central_series_map_le,
  end, }

lemma function.surjective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.surjective f) : is_nilpotent R L' :=
{ nilpotent :=
  begin
    tactic.unfreeze_local_instances, obtain ⟨k, hk⟩ := h₁,
    use k,
    rw [← lie_ideal.lower_central_series_map_eq k h₂, hk],
    simp only [lie_hom.map_bot_iff, bot_le],
  end, }

lemma lie_algebra.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
  is_nilpotent R L ↔ is_nilpotent R L' :=
begin
  split; introsI h,
  { exact e.symm.injective.lie_algebra_is_nilpotent, },
  { exact e.injective.lie_algebra_is_nilpotent, },
end

end nilpotent_algebras
