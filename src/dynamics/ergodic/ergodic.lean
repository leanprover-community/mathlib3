/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import dynamics.ergodic.measure_preserving

/-!
# Ergodic maps and measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only measurable sets `s` such that
`f⁻¹' s = s` are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API. Quasi-ergodicity is a weaker condition than ergodicity for which the measure
preserving condition is relaxed to quasi measure preserving.

# Main definitions:

 * `pre_ergodic`: the ergodicity condition without the measure preserving condition. This exists
   to share code between the `ergodic` and `quasi_ergodic` definitions.
 * `ergodic`: the definition of ergodic maps / measures.
 * `quasi_ergodic`: the definition of quasi ergodic maps / measures.
 * `ergodic.quasi_ergodic`: an ergodic map / measure is quasi ergodic.
 * `quasi_ergodic.ae_empty_or_univ'`: when the map is quasi measure preserving, one may relax the
   strict invariance condition to almost invariance in the ergodicity condition.

-/

open set function filter measure_theory measure_theory.measure
open_locale ennreal

variables {α : Type*} {m : measurable_space α} (f : α → α) {s : set α}
include m

/-- A map `f : α → α` is said to be pre-ergodic with respect to a measure `μ` if any measurable
strictly invariant set is either almost empty or full. -/
structure pre_ergodic (μ : measure α . volume_tac) : Prop :=
(ae_empty_or_univ : ∀ ⦃s⦄, measurable_set s → f⁻¹' s = s → s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ)

/-- A map `f : α → α` is said to be ergodic with respect to a measure `μ` if it is measure
preserving and pre-ergodic. -/
@[nolint has_nonempty_instance] structure ergodic (μ : measure α . volume_tac) extends
  measure_preserving f μ μ, pre_ergodic f μ : Prop

/-- A map `f : α → α` is said to be quasi ergodic with respect to a measure `μ` if it is quasi
measure preserving and pre-ergodic. -/
@[nolint has_nonempty_instance] structure quasi_ergodic (μ : measure α . volume_tac) extends
  quasi_measure_preserving f μ μ, pre_ergodic f μ : Prop

variables {f} {μ : measure α}

namespace pre_ergodic

lemma measure_self_or_compl_eq_zero (hf : pre_ergodic f μ)
  (hs : measurable_set s) (hs' : f⁻¹' s = s) :
  μ s = 0 ∨ μ sᶜ = 0 :=
by simpa using hf.ae_empty_or_univ hs hs'

/-- On a probability space, the (pre)ergodicity condition is a zero one law. -/
lemma prob_eq_zero_or_one [is_probability_measure μ] (hf : pre_ergodic f μ)
  (hs : measurable_set s) (hs' : f⁻¹' s = s) :
  μ s = 0 ∨ μ s = 1 :=
by simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'

lemma of_iterate (n : ℕ) (hf : pre_ergodic (f^[n]) μ) : pre_ergodic f μ :=
⟨λ s hs hs', hf.ae_empty_or_univ hs $ is_fixed_pt.preimage_iterate hs' n⟩

end pre_ergodic

namespace measure_theory.measure_preserving

variables {β : Type*} {m' : measurable_space β} {μ' : measure β} {s' : set β} {g : α → β}

lemma pre_ergodic_of_pre_ergodic_conjugate (hg : measure_preserving g μ μ')
  (hf : pre_ergodic f μ) {f' : β → β} (h_comm : g ∘ f = f' ∘ g) :
  pre_ergodic f' μ' :=
⟨begin
  intros s hs₀ hs₁,
  replace hs₁ : f⁻¹' (g⁻¹' s) = g⁻¹' s, { rw [← preimage_comp, h_comm, preimage_comp, hs₁], },
  cases hf.ae_empty_or_univ (hg.measurable hs₀) hs₁ with hs₂ hs₂;
  [left, right],
  { simpa only [ae_eq_empty, hg.measure_preimage hs₀] using hs₂, },
  { simpa only [ae_eq_univ, ← preimage_compl, hg.measure_preimage hs₀.compl] using hs₂, },
end⟩

lemma pre_ergodic_conjugate_iff {e : α ≃ᵐ β} (h : measure_preserving e μ μ') :
  pre_ergodic (e ∘ f ∘ e.symm) μ' ↔ pre_ergodic f μ :=
begin
  refine ⟨λ hf, pre_ergodic_of_pre_ergodic_conjugate (h.symm e) hf _,
          λ hf, pre_ergodic_of_pre_ergodic_conjugate h hf _⟩,
  { change (e.symm ∘ e) ∘ f ∘ e.symm = f ∘ e.symm,
    rw [measurable_equiv.symm_comp_self, comp.left_id], },
  { change e ∘ f = e ∘ f ∘ e.symm ∘ e,
    rw [measurable_equiv.symm_comp_self, comp.right_id], },
end

lemma ergodic_conjugate_iff {e : α ≃ᵐ β} (h : measure_preserving e μ μ') :
  ergodic (e ∘ f ∘ e.symm) μ' ↔ ergodic f μ :=
begin
  have : measure_preserving (e ∘ f ∘ e.symm) μ' μ' ↔ measure_preserving f μ μ :=
    by rw [h.comp_left_iff, (measure_preserving.symm e h).comp_right_iff],
  replace h : pre_ergodic (e ∘ f ∘ e.symm) μ' ↔ pre_ergodic f μ := h.pre_ergodic_conjugate_iff,
  exact ⟨λ hf, { .. this.mp hf.to_measure_preserving, .. h.mp hf.to_pre_ergodic, },
         λ hf, { .. this.mpr hf.to_measure_preserving, .. h.mpr hf.to_pre_ergodic, }⟩,
end

end measure_theory.measure_preserving

namespace quasi_ergodic

/-- For a quasi ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
lemma ae_empty_or_univ'
  (hf : quasi_ergodic f μ) (hs : measurable_set s) (hs' : f⁻¹' s =ᵐ[μ] s) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
begin
  obtain ⟨t, h₀, h₁, h₂⟩ := hf.to_quasi_measure_preserving.exists_preimage_eq_of_preimage_ae hs hs',
  rcases hf.ae_empty_or_univ h₀ h₂ with h₃ | h₃;
  [left, right];
  exact ae_eq_trans h₁.symm h₃,
end

end quasi_ergodic

namespace ergodic

/-- An ergodic map is quasi ergodic. -/
lemma quasi_ergodic (hf : ergodic f μ) : quasi_ergodic f μ :=
{ .. hf.to_pre_ergodic,
  .. hf.to_measure_preserving.quasi_measure_preserving, }

/-- See also `ergodic.ae_empty_or_univ_of_preimage_ae_le`. -/
lemma ae_empty_or_univ_of_preimage_ae_le'
  (hf : ergodic f μ) (hs : measurable_set s) (hs' : f⁻¹' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
begin
  refine hf.quasi_ergodic.ae_empty_or_univ' hs _,
  refine ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).symm.le _ h_fin,
  exact measurable_set_preimage hf.measurable hs,
end

/-- See also `ergodic.ae_empty_or_univ_of_ae_le_preimage`. -/
lemma ae_empty_or_univ_of_ae_le_preimage'
  (hf : ergodic f μ) (hs : measurable_set s) (hs' : s ≤ᵐ[μ] f⁻¹' s) (h_fin : μ s ≠ ∞) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
begin
  replace h_fin : μ (f⁻¹' s) ≠ ∞, { rwa hf.measure_preimage hs, },
  refine hf.quasi_ergodic.ae_empty_or_univ' hs _,
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm,
end

/-- See also `ergodic.ae_empty_or_univ_of_image_ae_le`. -/
lemma ae_empty_or_univ_of_image_ae_le'
  (hf : ergodic f μ) (hs : measurable_set s) (hs' : f '' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
begin
  replace hs' : s ≤ᵐ[μ] f ⁻¹' s :=
    (has_subset.subset.eventually_le (subset_preimage_image f s)).trans
    (hf.quasi_measure_preserving.preimage_mono_ae hs'),
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin,
end

section is_finite_measure

variables [is_finite_measure μ]

lemma ae_empty_or_univ_of_preimage_ae_le
  (hf : ergodic f μ) (hs : measurable_set s) (hs' : f⁻¹' s ≤ᵐ[μ] s) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
ae_empty_or_univ_of_preimage_ae_le' hf hs hs' $ measure_ne_top μ s

lemma ae_empty_or_univ_of_ae_le_preimage
  (hf : ergodic f μ) (hs : measurable_set s) (hs' : s ≤ᵐ[μ] f⁻¹' s) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
ae_empty_or_univ_of_ae_le_preimage' hf hs hs' $ measure_ne_top μ s

lemma ae_empty_or_univ_of_image_ae_le
  (hf : ergodic f μ) (hs : measurable_set s) (hs' : f '' s ≤ᵐ[μ] s) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
ae_empty_or_univ_of_image_ae_le' hf hs hs' $ measure_ne_top μ s

end is_finite_measure

end ergodic
