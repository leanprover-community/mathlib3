/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.action
import measure_theory.group.pointwise

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.
-/

open_locale ennreal pointwise topological_space nnreal ennreal
open measure_theory measure_theory.measure set function

namespace measure_theory

/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
@[protect_proj] structure is_add_fundamental_domain (G : Type*) {α : Type*} [has_zero G]
  [has_vadd G α] [measurable_space α] (s : set α) (μ : measure α . volume_tac) : Prop :=
(measurable_set : measurable_set s)
(ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s)
(ae_disjoint : ∀ g ≠ (0 : G), μ ((g +ᵥ s) ∩ s) = 0)

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[protect_proj, to_additive is_add_fundamental_domain]
structure is_fundamental_domain (G : Type*) {α : Type*} [has_one G] [has_scalar G α]
  [measurable_space α] (s : set α) (μ : measure α . volume_tac) : Prop :=
(measurable_set : measurable_set s)
(ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
(ae_disjoint : ∀ g ≠ (1 : G), μ ((g • s) ∩ s) = 0)

namespace is_fundamental_domain

variables {G α : Type*} [group G] [mul_action G α] [measurable_space α] {s t : set α}
  {μ : measure α}

@[to_additive] lemma Union_smul_ae_eq (h : is_fundamental_domain G s μ) :
  (⋃ g : G, g • s) =ᵐ[μ] univ :=
filter.eventually_eq_univ.2 $ h.ae_covers.mono $
  λ x ⟨g, hg⟩, mem_Union.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

variables [measurable_space G] [has_measurable_smul G α]

@[to_additive]
lemma measurable_set_smul (h : is_fundamental_domain G s μ) (g : G) : measurable_set (g • s) :=
h.measurable_set.const_smul g

variables [smul_invariant_measure G α μ]

@[to_additive] lemma pairwise_ae_disjoint (h : is_fundamental_domain G s μ) :
  pairwise (λ g₁ g₂ : G, μ (g₁ • s ∩ g₂ • s) = 0) :=
λ g₁ g₂ hne,
calc μ (g₁ • s ∩ g₂ • s) = μ (g₂ • ((g₂⁻¹ * g₁) • s ∩ s)) :
  by rw [smul_set_inter, ← mul_smul, mul_inv_cancel_left]
... = μ ((g₂⁻¹ * g₁) • s ∩ s) : measure_smul_set _ _ _
... = 0 : h.ae_disjoint _ $ mt inv_mul_eq_one.1 hne.symm

variables [encodable G]

@[to_additive] lemma measure_eq_tsum' (h : is_fundamental_domain G s μ) (t : set α) :
  μ t = ∑' g : G, μ (t ∩ g • s) :=
calc μ t = μ.restrict t (⋃ g : G, g • s) :
  by rw [measure_congr (ae_mono measure.restrict_le_self h.Union_smul_ae_eq), restrict_apply_univ]
... = ∑' g : G, μ.restrict t (g • s) :
  measure_Union_of_null_inter h.measurable_set_smul $ h.pairwise_ae_disjoint.mono $
    λ g₁ g₂ H, measure.restrict_le_self.absolutely_continuous H
... = ∑' g : G, μ (t ∩ g • s) :
  tsum_congr $ λ g, by rw [measure.restrict_apply (h.measurable_set_smul g), inter_comm]

@[to_additive] lemma measure_eq_tsum (h : is_fundamental_domain G s μ) (t : set α) :
  μ t = ∑' g : G, μ (g • t ∩ s) :=
calc μ t = ∑' g : G, μ (t ∩ g • s) : h.measure_eq_tsum' t
     ... = ∑' g : G, μ (t ∩ g⁻¹ • s) : ((equiv.inv G).tsum_eq _).symm
     ... = ∑' g : G, μ (g • t ∩ s) :
  tsum_congr $ λ g, by rw [← measure_smul_set g μ, smul_set_inter, smul_inv_smul]

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive] protected lemma measure_eq (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) : μ s = μ t :=
calc μ s = ∑' g : G, μ (s ∩ g • t) : ht.measure_eq_tsum' s
     ... = ∑' g : G, μ (g • t ∩ s) : by simp only [inter_comm]
     ... = μ t : (hs.measure_eq_tsum t).symm

end is_fundamental_domain

end measure_theory
