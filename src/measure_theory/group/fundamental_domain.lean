/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.action
import measure_theory.group.pointwise
import measure_theory.integral.set_integral

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to measure `μ` if

* `s` is a measurable set;

* the union of the sets `g • s` over all `g : G` covers the whole space but a set of measure zero;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.
-/

open_locale ennreal pointwise topological_space nnreal ennreal measure_theory
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

@[to_additive] lemma mono (h : is_fundamental_domain G s μ) {ν : measure α} (hle : ν ≪ μ) :
  is_fundamental_domain G s ν :=
⟨h.1, hle h.2, λ g hg, hle (h.3 g hg)⟩

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

variables [encodable G] {ν : measure α}

@[to_additive] lemma sum_restrict_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) :
  sum (λ g : G, ν.restrict (g • s)) = ν :=
by rw [← restrict_Union_ae (h.pairwise_ae_disjoint.mono $ λ i j h, hν h) h.measurable_set_smul,
  restrict_congr_set (hν h.Union_smul_ae_eq), restrict_univ]

@[to_additive] lemma lintegral_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ)
  (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν :=
by rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[to_additive] lemma set_lintegral_eq_tsum (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞)
  (t : set α) :
  ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g • x) ∂μ :=
calc ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂(μ.restrict t) :
  h.lintegral_eq_tsum_of_ac restrict_le_self.absolutely_continuous _
... = ∑' g : G, ∫⁻ x in g • s ∩ t, f x ∂μ : by simp only [restrict_restrict, h.measurable_set_smul]
... = ∑' g : G, ∫⁻ x in g⁻¹ • s ∩ t, f x ∂μ : ((equiv.inv G).tsum_eq _).symm
... = ∑' g : G, ∫⁻ x in g⁻¹ • (s ∩ g • t), f (g⁻¹ • g • x) ∂μ :
  by simp only [smul_set_inter, inv_smul_smul]
... = ∑' g : G, ∫⁻ x in s ∩ g • t, f (g • x) ∂μ :
  tsum_congr $ λ g, (measure_preserving_smul g⁻¹ μ).set_lintegral
... = _ : _

@[to_additive] lemma measure_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ)
  (t : set α) :
  ν t = ∑' g : G, ν (t ∩ g • s) :=
by simpa only [set_lintegral_one, pi.one_def, measure.restrict_apply (h.measurable_set_smul _),
  inter_comm]
  using h.lintegral_eq_tsum_of_ac (measure.restrict_le_self.absolutely_continuous.trans hν ) 1

@[to_additive] lemma measure_eq_tsum' (h : is_fundamental_domain G s μ) (t : set α) :
  μ t = ∑' g : G, μ (t ∩ g • s) :=
h.measure_eq_tsum_of_ac absolutely_continuous.rfl t

@[to_additive] lemma measure_eq_tsum (h : is_fundamental_domain G s μ) (t : set α) :
  μ t = ∑' g : G, μ (g • t ∩ s) :=
calc μ t = ∑' g : G, μ (t ∩ g • s) : h.measure_eq_tsum' t
     ... = ∑' g : G, μ (t ∩ g⁻¹ • s) : ((equiv.inv G).tsum_eq _).symm
     ... = ∑' g : G, μ (g • t ∩ s) :
  tsum_congr $ λ g, by rw [← measure_smul_set g μ, smul_set_inter, smul_inv_smul]

/-- If `s` and `t` are to fundamental domains of the same action, then their measures are equal. -/
@[to_additive] protected lemma measure_congr (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) : μ s = μ t :=
calc μ s = ∑' g : G, μ (s ∩ g • t) : ht.measure_eq_tsum' s
     ... = ∑' g : G, μ (g • t ∩ s) : by simp only [inter_comm]
     ... = μ t : (hs.measure_eq_tsum t).symm

@[to_additive] protected lemma lintegral_congr (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) (f : α → ℝ≥0∞) (hf : ∀ (g : G) x, f (g • x) = f x) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
calc ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in g • t, f x ∂(μ.restrict s) :
  ht.lintegral_eq_tsum_of_ac measure.restrict_le_self.absolutely_continuous _
... = ∑' g : G, ∫⁻ x in 
... = _ : _

end is_fundamental_domain

end measure_theory
