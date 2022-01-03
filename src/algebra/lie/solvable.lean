/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.abelian
import algebra.lie.ideal_operations
import order.hom.basic

/-!
# Solvable Lie algebras

Like groups, Lie algebras admit a natural concept of solvability. We define this here via the
derived series and prove some related results. We also define the radical of a Lie algebra and
prove that it is solvable when the Lie algebra is Noetherian.

## Main definitions

  * `lie_algebra.derived_series_of_ideal`
  * `lie_algebra.derived_series`
  * `lie_algebra.is_solvable`
  * `lie_algebra.is_solvable_add`
  * `lie_algebra.radical`
  * `lie_algebra.radical_is_solvable`
  * `lie_algebra.derived_length_of_ideal`
  * `lie_algebra.derived_length`
  * `lie_algebra.derived_abelian_of_ideal`

## Tags

lie algebra, derived series, derived length, solvable, radical
-/

universes u v w w₁ w₂

variables (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
variables (I J : lie_ideal R L) {f : L' →ₗ⁅R⁆ L}

namespace lie_algebra

/-- A generalisation of the derived series of a Lie algebra, whose zeroth term is a specified ideal.

It can be more convenient to work with this generalisation when considering the derived series of
an ideal since it provides a type-theoretic expression of the fact that the terms of the ideal's
derived series are also ideals of the enclosing algebra.

See also `lie_ideal.derived_series_eq_derived_series_of_ideal_comap` and
`lie_ideal.derived_series_eq_derived_series_of_ideal_map` below. -/
def derived_series_of_ideal (k : ℕ) : lie_ideal R L → lie_ideal R L := (λ I, ⁅I, I⁆)^[k]

@[simp] lemma derived_series_of_ideal_zero :
  derived_series_of_ideal R L 0 I = I := rfl

@[simp] lemma derived_series_of_ideal_succ (k : ℕ) :
  derived_series_of_ideal R L (k + 1) I =
  ⁅derived_series_of_ideal R L k I, derived_series_of_ideal R L k I⁆ :=
function.iterate_succ_apply' (λ I, ⁅I, I⁆) k I

/-- The derived series of Lie ideals of a Lie algebra. -/
abbreviation derived_series (k : ℕ) : lie_ideal R L := derived_series_of_ideal R L k ⊤

lemma derived_series_def (k : ℕ) :
  derived_series R L k = derived_series_of_ideal R L k ⊤ := rfl

variables {R L}

local notation `D` := derived_series_of_ideal R L

lemma derived_series_of_ideal_add (k l : ℕ) : D (k + l) I = D k (D l I) :=
begin
  induction k with k ih,
  { rw [zero_add, derived_series_of_ideal_zero], },
  { rw [nat.succ_add k l, derived_series_of_ideal_succ, derived_series_of_ideal_succ, ih], },
end

@[mono] lemma derived_series_of_ideal_le {I J : lie_ideal R L} {k l : ℕ} (h₁ : I ≤ J) (h₂ : l ≤ k) :
  D k I ≤ D l J :=
begin
  revert l, induction k with k ih; intros l h₂,
  { rw nat.le_zero_iff at h₂, rw [h₂, derived_series_of_ideal_zero], exact h₁, },
  { have h : l = k.succ ∨ l ≤ k, by rwa [le_iff_eq_or_lt, nat.lt_succ_iff] at h₂,
    cases h,
    { rw [h, derived_series_of_ideal_succ, derived_series_of_ideal_succ],
      exact lie_submodule.mono_lie _ _ _ _ (ih (le_refl k)) (ih (le_refl k)), },
    { rw derived_series_of_ideal_succ, exact le_trans (lie_submodule.lie_le_left _ _) (ih h), }, },
end

lemma derived_series_of_ideal_succ_le (k : ℕ) : D (k + 1) I ≤ D k I :=
derived_series_of_ideal_le (le_refl I) k.le_succ

lemma derived_series_of_ideal_le_self (k : ℕ) : D k I ≤ I :=
derived_series_of_ideal_le (le_refl I) (zero_le k)

lemma derived_series_of_ideal_mono {I J : lie_ideal R L} (h : I ≤ J) (k : ℕ) : D k I ≤ D k J :=
derived_series_of_ideal_le h (le_refl k)

lemma derived_series_of_ideal_antitone {k l : ℕ} (h : l ≤ k) : D k I ≤ D l I :=
derived_series_of_ideal_le (le_refl I) h

lemma derived_series_of_ideal_add_le_add (J : lie_ideal R L) (k l : ℕ) :
  D (k + l) (I + J) ≤ (D k I) + (D l J) :=
begin
  let D₁ : lie_ideal R L →o lie_ideal R L :=
  { to_fun    := λ I, ⁅I, I⁆,
    monotone' := λ I J h, lie_submodule.mono_lie I J I J h h, },
  have h₁ : ∀ (I J : lie_ideal R L), D₁ (I ⊔ J) ≤ (D₁ I) ⊔ J,
  { simp [lie_submodule.lie_le_right, lie_submodule.lie_le_left, le_sup_of_le_right], },
  rw ← D₁.iterate_sup_le_sup_iff at h₁,
  exact h₁ k l I J,
end

lemma derived_series_of_bot_eq_bot (k : ℕ) : derived_series_of_ideal R L k ⊥ = ⊥ :=
by { rw eq_bot_iff, exact derived_series_of_ideal_le_self ⊥ k, }

lemma abelian_iff_derived_one_eq_bot : is_lie_abelian I ↔ derived_series_of_ideal R L 1 I = ⊥ :=
by rw [derived_series_of_ideal_succ, derived_series_of_ideal_zero,
  lie_submodule.lie_abelian_iff_lie_self_eq_bot]

lemma abelian_iff_derived_succ_eq_bot (I : lie_ideal R L) (k : ℕ) :
  is_lie_abelian (derived_series_of_ideal R L k I) ↔ derived_series_of_ideal R L (k + 1) I = ⊥ :=
by rw [add_comm, derived_series_of_ideal_add I 1 k, abelian_iff_derived_one_eq_bot]

end lie_algebra

namespace lie_ideal

open lie_algebra

variables {R L}

lemma derived_series_eq_derived_series_of_ideal_comap (k : ℕ) :
  derived_series R I k = (derived_series_of_ideal R L k I).comap I.incl :=
begin
  induction k with k ih,
  { simp only [derived_series_def, comap_incl_self, derived_series_of_ideal_zero], },
  { simp only [derived_series_def, derived_series_of_ideal_succ] at ⊢ ih, rw ih,
    exact comap_bracket_incl_of_le I
      (derived_series_of_ideal_le_self I k) (derived_series_of_ideal_le_self I k), },
end

lemma derived_series_eq_derived_series_of_ideal_map (k : ℕ) :
  (derived_series R I k).map I.incl = derived_series_of_ideal R L k I :=
by { rw [derived_series_eq_derived_series_of_ideal_comap, map_comap_incl, inf_eq_right],
     apply derived_series_of_ideal_le_self, }

lemma derived_series_eq_bot_iff (k : ℕ) :
  derived_series R I k = ⊥ ↔ derived_series_of_ideal R L k I = ⊥ :=
by rw [← derived_series_eq_derived_series_of_ideal_map, map_eq_bot_iff, ker_incl, eq_bot_iff]

lemma derived_series_add_eq_bot {k l : ℕ} {I J : lie_ideal R L}
  (hI : derived_series R I k = ⊥) (hJ : derived_series R J l = ⊥) :
  derived_series R ↥(I + J) (k + l) = ⊥ :=
begin
  rw lie_ideal.derived_series_eq_bot_iff at hI hJ ⊢,
  rw ← le_bot_iff,
  let D := derived_series_of_ideal R L, change D k I = ⊥ at hI, change D l J = ⊥ at hJ,
  calc D (k + l) (I + J) ≤ (D k I) + (D l J) : derived_series_of_ideal_add_le_add I J k l
                     ... ≤ ⊥ : by { rw [hI, hJ], simp, },
end

lemma derived_series_map_le (k : ℕ) :
  (derived_series R L' k).map f ≤ derived_series R L k :=
begin
  induction k with k ih,
  { simp only [derived_series_def, derived_series_of_ideal_zero, le_top], },
  { simp only [derived_series_def, derived_series_of_ideal_succ] at ih ⊢,
    exact le_trans (map_bracket_le f) (lie_submodule.mono_lie _ _ _ _ ih ih), },
end

lemma derived_series_map_eq (k : ℕ) (h : function.surjective f) :
  (derived_series R L' k).map f = derived_series R L k :=
begin
  induction k with k ih,
  { change (⊤ : lie_ideal R L').map f = ⊤,
    rw ←f.ideal_range_eq_map,
    exact f.ideal_range_eq_top_of_surjective h, },
  { simp only [derived_series_def, map_bracket_eq f h, ih, derived_series_of_ideal_succ], },
end

end lie_ideal

namespace lie_algebra

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
class is_solvable : Prop :=
(solvable : ∃ k, derived_series R L k = ⊥)

instance is_solvable_bot : is_solvable R ↥(⊥ : lie_ideal R L) :=
⟨⟨0, @subsingleton.elim _ lie_ideal.subsingleton_of_bot _ ⊥⟩⟩

instance is_solvable_add {I J : lie_ideal R L} [hI : is_solvable R I] [hJ : is_solvable R J] :
  is_solvable R ↥(I + J) :=
begin
  tactic.unfreeze_local_instances,
  obtain ⟨k, hk⟩ := hI,
  obtain ⟨l, hl⟩ := hJ,
  exact ⟨⟨k+l, lie_ideal.derived_series_add_eq_bot hk hl⟩⟩,
end

end lie_algebra

variables {R L}

namespace function

open lie_algebra

lemma injective.lie_algebra_is_solvable [h₁ : is_solvable R L] (h₂ : injective f) :
  is_solvable R L' :=
begin
  tactic.unfreeze_local_instances, obtain ⟨k, hk⟩ := h₁,
  use k,
  apply lie_ideal.bot_of_map_eq_bot h₂, rw [eq_bot_iff, ← hk],
  apply lie_ideal.derived_series_map_le,
end

lemma surjective.lie_algebra_is_solvable [h₁ : is_solvable R L'] (h₂ : surjective f) :
  is_solvable R L :=
begin
  tactic.unfreeze_local_instances, obtain ⟨k, hk⟩ := h₁,
  use k,
  rw [← lie_ideal.derived_series_map_eq k h₂, hk],
  simp only [lie_ideal.map_eq_bot_iff, bot_le],
end

end function

lemma lie_hom.is_solvable_range (f : L' →ₗ⁅R⁆ L) [h : lie_algebra.is_solvable R L'] :
  lie_algebra.is_solvable R f.range :=
f.surjective_range_restrict.lie_algebra_is_solvable

namespace lie_algebra

lemma solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : is_solvable R L' ↔ is_solvable R L :=
begin
  split; introsI h,
  { exact e.symm.injective.lie_algebra_is_solvable, },
  { exact e.injective.lie_algebra_is_solvable, },
end

lemma le_solvable_ideal_solvable {I J : lie_ideal R L} (h₁ : I ≤ J) (h₂ : is_solvable R J) :
  is_solvable R I :=
(lie_ideal.hom_of_le_injective h₁).lie_algebra_is_solvable

variables (R L)

@[priority 100]
instance of_abelian_is_solvable [is_lie_abelian L] : is_solvable R L :=
begin
  use 1,
  rw [← abelian_iff_derived_one_eq_bot, lie_abelian_iff_equiv_lie_abelian lie_ideal.top_equiv_self],
  apply_instance,
end

/-- The (solvable) radical of Lie algebra is the `Sup` of all solvable ideals. -/
def radical := Sup { I : lie_ideal R L | is_solvable R I }

/-- The radical of a Noetherian Lie algebra is solvable. -/
instance radical_is_solvable [is_noetherian R L] : is_solvable R (radical R L) :=
begin
  have hwf := lie_submodule.well_founded_of_noetherian R L L,
  rw ← complete_lattice.is_sup_closed_compact_iff_well_founded at hwf,
  refine hwf { I : lie_ideal R L | is_solvable R I } _ _,
  { use ⊥, exact lie_algebra.is_solvable_bot R L, },
  { intros I J hI hJ, apply lie_algebra.is_solvable_add R L; [exact hI, exact hJ], },
end

/-- The `→` direction of this lemma is actually true without the `is_noetherian` assumption. -/
lemma lie_ideal.solvable_iff_le_radical [is_noetherian R L] (I : lie_ideal R L) :
  is_solvable R I ↔ I ≤ radical R L :=
begin
  split; intros h,
  { exact le_Sup h, },
  { apply le_solvable_ideal_solvable h, apply_instance, },
end

lemma center_le_radical : center R L ≤ radical R L :=
have h : is_solvable R (center R L), { apply_instance, }, le_Sup h

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
natural number `k` (the number of inclusions).

For a non-solvable ideal, the value is 0. -/
noncomputable def derived_length_of_ideal (I : lie_ideal R L) : ℕ :=
Inf {k | derived_series_of_ideal R L k I = ⊥}

/-- The derived length of a Lie algebra is the derived length of its 'top' Lie ideal.

See also `lie_algebra.derived_length_eq_derived_length_of_ideal`. -/
noncomputable abbreviation derived_length : ℕ := derived_length_of_ideal R L ⊤

lemma derived_series_of_derived_length_succ (I : lie_ideal R L) (k : ℕ) :
  derived_length_of_ideal R L I = k + 1 ↔
  is_lie_abelian (derived_series_of_ideal R L k I) ∧ derived_series_of_ideal R L k I ≠ ⊥ :=
begin
  rw abelian_iff_derived_succ_eq_bot,
  let s := {k | derived_series_of_ideal R L k I = ⊥}, change Inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s,
  have hs : ∀ (k₁ k₂ : ℕ), k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s,
  { intros k₁ k₂ h₁₂ h₁,
    suffices : derived_series_of_ideal R L k₂ I ≤ ⊥, { exact eq_bot_iff.mpr this, },
    change derived_series_of_ideal R L k₁ I = ⊥ at h₁, rw ← h₁,
    exact derived_series_of_ideal_antitone I h₁₂, },
  exact nat.Inf_upward_closed_eq_succ_iff hs k,
end

lemma derived_length_eq_derived_length_of_ideal (I : lie_ideal R L) :
  derived_length R I = derived_length_of_ideal R L I :=
begin
  let s₁ := {k | derived_series R I k = ⊥},
  let s₂ := {k | derived_series_of_ideal R L k I = ⊥},
  change Inf s₁ = Inf s₂,
  congr, ext k, exact I.derived_series_eq_bot_iff k,
end

variables {R L}

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
`k-1`th term in the derived series (and is therefore an Abelian ideal contained in `I`).

For a non-solvable ideal, this is the zero ideal, `⊥`. -/
noncomputable def derived_abelian_of_ideal (I : lie_ideal R L) : lie_ideal R L :=
match derived_length_of_ideal R L I with
| 0     := ⊥
| k + 1 := derived_series_of_ideal R L k I
end

lemma abelian_derived_abelian_of_ideal (I : lie_ideal R L) :
  is_lie_abelian (derived_abelian_of_ideal I) :=
begin
  dunfold derived_abelian_of_ideal,
  cases h : derived_length_of_ideal R L I with k,
  { exact is_lie_abelian_bot R L, },
  { rw derived_series_of_derived_length_succ at h, exact h.1, },
end

lemma derived_length_zero (I : lie_ideal R L) [hI : is_solvable R I] :
  derived_length_of_ideal R L I = 0 ↔ I = ⊥ :=
begin
  let s := {k | derived_series_of_ideal R L k I = ⊥}, change Inf s = 0 ↔ _,
  have hne : s ≠ ∅,
  { rw set.ne_empty_iff_nonempty,
    tactic.unfreeze_local_instances, obtain ⟨k, hk⟩ := hI, use k,
    rw [derived_series_def, lie_ideal.derived_series_eq_bot_iff] at hk, exact hk, },
  simp [hne],
end

lemma abelian_of_solvable_ideal_eq_bot_iff (I : lie_ideal R L) [h : is_solvable R I] :
  derived_abelian_of_ideal I = ⊥ ↔ I = ⊥ :=
begin
  dunfold derived_abelian_of_ideal,
  cases h : derived_length_of_ideal R L I with k,
  { rw derived_length_zero at h, rw h, refl, },
  { obtain ⟨h₁, h₂⟩ := (derived_series_of_derived_length_succ R L I k).mp h,
    have h₃ : I ≠ ⊥, { intros contra, apply h₂, rw contra, apply derived_series_of_bot_eq_bot, },
    change derived_series_of_ideal R L k I = ⊥ ↔ I = ⊥,
    split; contradiction, },
end

end lie_algebra
