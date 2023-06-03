/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Yury Kudryashov
-/
import measure_theory.measure.measure_space

/-! # Mutually singular measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Two measures `μ`, `ν` are said to be mutually singular (`measure_theory.measure.mutually_singular`,
localized notation `μ ⟂ₘ ν`) if there exists a measurable set `s` such that `μ s = 0` and
`ν sᶜ = 0`. The measurability of `s` is an unnecessary assumption (see
`measure_theory.measure.mutually_singular.mk`) but we keep it because this way `rcases (h : μ ⟂ₘ ν)`
gives us a measurable set and usually it is easy to prove measurability.

In this file we define the predicate `measure_theory.measure.mutually_singular` and prove basic
facts about it.

## Tags

measure, mutually singular
-/

open set
open_locale measure_theory nnreal ennreal

namespace measure_theory

namespace measure

variables {α : Type*} {m0 : measurable_space α} {μ μ₁ μ₂ ν ν₁ ν₂ : measure α}

/-- Two measures `μ`, `ν` are said to be mutually singular if there exists a measurable set `s`
such that `μ s = 0` and `ν sᶜ = 0`. -/
def mutually_singular {m0 : measurable_space α} (μ ν : measure α) : Prop :=
∃ (s : set α), measurable_set s ∧ μ s = 0 ∧ ν sᶜ = 0

localized "infix (name := measure.mutually_singular)
  ` ⟂ₘ `:60 := measure_theory.measure.mutually_singular" in measure_theory

namespace mutually_singular

lemma mk {s t : set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ ⊆ s ∪ t) :
  mutually_singular μ ν :=
begin
  use [to_measurable μ s, measurable_set_to_measurable _ _, (measure_to_measurable _).trans hs],
  refine measure_mono_null (λ x hx, (hst trivial).resolve_left $ λ hxs, hx _) ht,
  exact subset_to_measurable _ _ hxs
end

@[simp] lemma zero_right : μ ⟂ₘ 0 := ⟨∅, measurable_set.empty, measure_empty, rfl⟩

@[symm] lemma symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν :=
let ⟨i, hi, his, hit⟩ := h in ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩

lemma comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ := ⟨λ h, h.symm, λ h, h.symm⟩

@[simp] lemma zero_left : 0 ⟂ₘ μ := zero_right.symm

lemma mono_ac (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂ :=
let ⟨s, hs, h₁, h₂⟩ := h in ⟨s, hs, hμ h₁, hν h₂⟩

lemma mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≤ μ₁) (hν : ν₂ ≤ ν₁) : μ₂ ⟂ₘ ν₂ :=
h.mono_ac hμ.absolutely_continuous hν.absolutely_continuous

@[simp] lemma sum_left {ι : Type*} [countable ι] {μ : ι → measure α} :
  (sum μ) ⟂ₘ ν ↔ ∀ i, μ i ⟂ₘ ν :=
begin
  refine ⟨λ h i, h.mono (le_sum _ _) le_rfl, λ H, _⟩,
  choose s hsm hsμ hsν using H,
  refine ⟨⋂ i, s i, measurable_set.Inter hsm, _, _⟩,
  { rw [sum_apply _ (measurable_set.Inter hsm), ennreal.tsum_eq_zero],
    exact λ i, measure_mono_null (Inter_subset _ _) (hsμ i) },
  { rwa [compl_Inter, measure_Union_null_iff], }
end

@[simp] lemma sum_right {ι : Type*} [countable ι] {ν : ι → measure α} :
  μ ⟂ₘ sum ν ↔ ∀ i, μ ⟂ₘ ν i :=
comm.trans $ sum_left.trans $ forall_congr $ λ i, comm

@[simp] lemma add_left_iff : μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν :=
by rw [← sum_cond, sum_left, bool.forall_bool, cond, cond, and.comm]

@[simp] lemma add_right_iff : μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂ :=
comm.trans $ add_left_iff.trans $ and_congr comm comm

lemma add_left (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ :=
add_left_iff.2 ⟨h₁, h₂⟩

lemma add_right (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂ :=
add_right_iff.2 ⟨h₁, h₂⟩

lemma smul (r : ℝ≥0∞) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
h.mono_ac (absolutely_continuous.rfl.smul r) absolutely_continuous.rfl

lemma smul_nnreal (r : ℝ≥0) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ := h.smul r

end mutually_singular

end measure

end measure_theory
