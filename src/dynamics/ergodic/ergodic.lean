/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import dynamics.ergodic.measure_preserving

/-!
# Ergodic maps and measures

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only measurable sets `s` such that
`f⁻¹' s = s` are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API.

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

variables {α : Type*} [measurable_space α] (f : α → α) {s : set α}

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
⟨λ s hs hs',
begin
  apply hf.ae_empty_or_univ hs,
  rw preimage_iterate_eq,
  exact is_fixed_pt.iterate hs' n,
end⟩

end pre_ergodic

namespace ergodic

/-- An ergodic map is quasi ergodic. -/
lemma quasi_ergodic (hf : ergodic f μ) : quasi_ergodic f μ :=
{ .. hf.to_pre_ergodic,
  .. hf.to_measure_preserving.quasi_measure_preserving, }

end ergodic

namespace quasi_ergodic

/-- For a quasi ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full.-/
lemma ae_empty_or_univ'
  (hf : quasi_ergodic f μ) (hs : measurable_set s) (hs' : f⁻¹' s =ᵐ[μ] s) :
  s =ᵐ[μ] (∅ : set α) ∨ s =ᵐ[μ] univ :=
begin
  let t := limsup (λ n, (preimage f)^[n] s) at_top, -- `liminf` would work just as well.
  have ht₀ : t =ᵐ[μ] s := hf.to_quasi_measure_preserving.limsup_preimage_iterate_ae_eq hs',
  have ht₁ : measurable_set t := measurable_set.measurable_set_limsup
    (λ n, by { rw ← preimage_iterate_eq, exact hf.measurable.iterate n hs, }),
  have ht₂ : complete_lattice_hom.set_preimage f t = t :=
    (complete_lattice_hom.set_preimage f).apply_limsup_iterate s,
  rcases hf.ae_empty_or_univ ht₁ ht₂ with ht₃ | ht₃;
  [left, right];
  exact ae_eq_trans ht₀.symm ht₃,
end

end quasi_ergodic
