/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.action
import measure_theory.integral.set_integral

/-!
# Fundamental domain of a group action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.

## Main declarations

* `measure_theory.is_fundamental_domain`: Predicate for a set to be a fundamental domain of the
  action of a group
* `measure_theory.fundamental_frontier`: Fundamental frontier of a set under the action of a group.
  Elements of `s` that belong to some other translate of `s`.
* `measure_theory.fundamental_interior`: Fundamental interior of a set under the action of a group.
  Elements of `s` that do not belong to any other translate of `s`.
-/

open_locale ennreal pointwise topology nnreal ennreal measure_theory
open measure_theory measure_theory.measure set function topological_space filter

namespace measure_theory

/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
@[protect_proj] structure is_add_fundamental_domain (G : Type*) {α : Type*} [has_zero G]
  [has_vadd G α] [measurable_space α] (s : set α) (μ : measure α . volume_tac) : Prop :=
(null_measurable_set : null_measurable_set s μ)
(ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s)
(ae_disjoint : pairwise $ ae_disjoint μ on λ g : G, g +ᵥ s)

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[protect_proj, to_additive is_add_fundamental_domain]
structure is_fundamental_domain (G : Type*) {α : Type*} [has_one G] [has_smul G α]
  [measurable_space α] (s : set α) (μ : measure α . volume_tac) : Prop :=
(null_measurable_set : null_measurable_set s μ)
(ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
(ae_disjoint : pairwise $ ae_disjoint μ on λ g : G, g • s)

variables {G H α β E : Type*}

namespace is_fundamental_domain
variables [group G] [group H] [mul_action G α] [measurable_space α] [mul_action H β]
  [measurable_space β] [normed_add_comm_group E] {s t : set α} {μ : measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive "If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set
`s`, then `s` is a fundamental domain for the additive action of `G` on `α`."]
lemma mk' (h_meas : null_measurable_set s μ) (h_exists : ∀ x : α, ∃! g : G, g • x ∈ s) :
  is_fundamental_domain G s μ :=
{ null_measurable_set := h_meas,
  ae_covers := eventually_of_forall $ λ x, (h_exists x).exists,
  ae_disjoint := λ a b hab, disjoint.ae_disjoint $ disjoint_left.2 $ λ x hxa hxb,
    begin
      rw mem_smul_set_iff_inv_smul_mem at hxa hxb,
      exact hab (inv_injective $ (h_exists x).unique hxa hxb),
    end }

/-- For `s` to be a fundamental domain, it's enough to check `ae_disjoint (g • s) s` for `g ≠ 1`. -/
@[to_additive "For `s` to be a fundamental domain, it's enough to check `ae_disjoint (g +ᵥ s) s` for
`g ≠ 0`."]
lemma mk'' (h_meas : null_measurable_set s μ) (h_ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
  (h_ae_disjoint : ∀ g ≠ (1 : G), ae_disjoint μ (g • s) s)
  (h_qmp : ∀ (g : G), quasi_measure_preserving ((•) g : α → α) μ μ) :
  is_fundamental_domain G s μ :=
{ null_measurable_set := h_meas,
  ae_covers := h_ae_covers,
  ae_disjoint := pairwise_ae_disjoint_of_ae_disjoint_forall_ne_one h_ae_disjoint h_qmp }

/-- If a measurable space has a finite measure `μ` and a countable group `G` acts
quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
to check that its translates `g • s` are (almost) disjoint and that the sum `∑' g, μ (g • s)` is
sufficiently large. -/
@[to_additive measure_theory.is_add_fundamental_domain.mk_of_measure_univ_le "
If a measurable space has a finite measure `μ` and a countable additive group `G` acts
quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
to check that its translates `g +ᵥ s` are (almost) disjoint and that the sum `∑' g, μ (g +ᵥ s)` is
sufficiently large."]
lemma mk_of_measure_univ_le [is_finite_measure μ] [countable G]
  (h_meas : null_measurable_set s μ)
  (h_ae_disjoint : ∀ g ≠ (1 : G), ae_disjoint μ (g • s) s)
  (h_qmp : ∀ (g : G), quasi_measure_preserving ((•) g : α → α) μ μ)
  (h_measure_univ_le : μ (univ : set α) ≤ ∑' (g : G), μ (g • s)) :
  is_fundamental_domain G s μ :=
have ae_disjoint : pairwise (ae_disjoint μ on (λ (g : G), g • s)) :=
  pairwise_ae_disjoint_of_ae_disjoint_forall_ne_one h_ae_disjoint h_qmp,
{ null_measurable_set := h_meas,
  ae_disjoint := ae_disjoint,
  ae_covers :=
  begin
    replace h_meas : ∀ (g : G), null_measurable_set (g • s) μ :=
      λ g, by { rw [← inv_inv g, ← preimage_smul], exact h_meas.preimage (h_qmp g⁻¹), },
    have h_meas' : null_measurable_set {a | ∃ (g : G), g • a ∈ s} μ,
    { rw ← Union_smul_eq_set_of_exists, exact null_measurable_set.Union h_meas, },
    rw [ae_iff_measure_eq h_meas', ← Union_smul_eq_set_of_exists],
    refine le_antisymm (measure_mono $ subset_univ _) _,
    rw measure_Union₀ ae_disjoint h_meas,
    exact h_measure_univ_le,
  end }

@[to_additive] lemma Union_smul_ae_eq (h : is_fundamental_domain G s μ) :
  (⋃ g : G, g • s) =ᵐ[μ] univ :=
eventually_eq_univ.2 $ h.ae_covers.mono $ λ x ⟨g, hg⟩, mem_Union.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive] lemma mono (h : is_fundamental_domain G s μ) {ν : measure α} (hle : ν ≪ μ) :
  is_fundamental_domain G s ν :=
⟨h.1.mono_ac hle, hle h.2, h.ae_disjoint.mono $ λ a b hab, hle hab⟩

@[to_additive] lemma preimage_of_equiv {ν : measure β} (h : is_fundamental_domain G s μ) {f : β → α}
  (hf : quasi_measure_preserving f ν μ) {e : G → H} (he : bijective e)
  (hef : ∀ g, semiconj f ((•) (e g)) ((•) g)) :
  is_fundamental_domain H (f ⁻¹' s) ν :=
{ null_measurable_set := h.null_measurable_set.preimage hf,
  ae_covers := (hf.ae h.ae_covers).mono $ λ x ⟨g, hg⟩, ⟨e g, by rwa [mem_preimage, hef g x]⟩,
  ae_disjoint := λ a b hab,
    begin
      lift e to G ≃ H using he,
      have : (e.symm a⁻¹)⁻¹ ≠ (e.symm b⁻¹)⁻¹, by simp [hab],
      convert (h.ae_disjoint this).preimage hf using 1,
      simp only [←preimage_smul_inv, preimage_preimage, ←hef _ _, e.apply_symm_apply, inv_inv],
    end }

@[to_additive] lemma image_of_equiv {ν : measure β} (h : is_fundamental_domain G s μ)
  (f : α ≃ β) (hf : quasi_measure_preserving f.symm ν μ)
  (e : H ≃ G) (hef : ∀ g, semiconj f ((•) (e g)) ((•) g)) :
  is_fundamental_domain H (f '' s) ν :=
begin
  rw f.image_eq_preimage,
  refine h.preimage_of_equiv hf e.symm.bijective (λ g x, _),
  rcases f.surjective x with ⟨x, rfl⟩,
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]
end

@[to_additive] lemma pairwise_ae_disjoint_of_ac {ν} (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) :
  pairwise (λ g₁ g₂ : G, ae_disjoint ν (g₁ • s) (g₂ • s)) :=
h.ae_disjoint.mono $ λ g₁ g₂ H, hν H

@[to_additive] lemma smul_of_comm {G' : Type*} [group G'] [mul_action G' α] [measurable_space G']
  [has_measurable_smul G' α] [smul_invariant_measure G' α μ] [smul_comm_class G' G α]
  (h : is_fundamental_domain G s μ) (g : G') :
  is_fundamental_domain G (g • s) μ :=
h.image_of_equiv (mul_action.to_perm g) (measure_preserving_smul _ _).quasi_measure_preserving
  (equiv.refl _) $ smul_comm g

variables [measurable_space G] [has_measurable_smul G α] [smul_invariant_measure G α μ]

@[to_additive] lemma null_measurable_set_smul (h : is_fundamental_domain G s μ) (g : G) :
  null_measurable_set (g • s) μ :=
h.null_measurable_set.smul g

@[to_additive] lemma restrict_restrict (h : is_fundamental_domain G s μ) (g : G) (t : set α) :
  (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
restrict_restrict₀ ((h.null_measurable_set_smul g).mono restrict_le_self)

@[to_additive] lemma smul (h : is_fundamental_domain G s μ) (g : G) :
  is_fundamental_domain G (g • s) μ :=
h.image_of_equiv (mul_action.to_perm g) (measure_preserving_smul _ _).quasi_measure_preserving
  ⟨λ g', g⁻¹ * g' * g, λ g', g * g' * g⁻¹, λ g', by simp [mul_assoc], λ g', by simp [mul_assoc]⟩ $
  λ g' x, by simp [smul_smul, mul_assoc]

variables [countable G] {ν : measure α}

@[to_additive] lemma sum_restrict_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) :
  sum (λ g : G, ν.restrict (g • s)) = ν :=
by rw [← restrict_Union_ae (h.ae_disjoint.mono $ λ i j h, hν h)
    (λ g, (h.null_measurable_set_smul g).mono_ac hν),
  restrict_congr_set (hν h.Union_smul_ae_eq), restrict_univ]

@[to_additive] lemma lintegral_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ)
  (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν :=
by rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[to_additive] lemma sum_restrict (h : is_fundamental_domain G s μ) :
  sum (λ g : G, μ.restrict (g • s)) = μ :=
h.sum_restrict_of_ac (refl _)

@[to_additive] lemma lintegral_eq_tsum (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞) :
  ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive] lemma lintegral_eq_tsum' (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞) :
  ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ :=
calc ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ : h.lintegral_eq_tsum f
... = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ : ((equiv.inv G).tsum_eq _).symm
... = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ :
  tsum_congr $ λ g, ((measure_preserving_smul g⁻¹ μ).set_lintegral_comp_emb
    (measurable_embedding_const_smul _) _ _).symm

@[to_additive] lemma set_lintegral_eq_tsum (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞)
  (t : set α) : ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
calc ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂(μ.restrict t) :
  h.lintegral_eq_tsum_of_ac restrict_le_self.absolutely_continuous _
... = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :
  by simp only [h.restrict_restrict, inter_comm]

@[to_additive] lemma set_lintegral_eq_tsum' (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞)
  (t : set α) :
  ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
calc ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :
  h.set_lintegral_eq_tsum f t
... = ∑' g : G, ∫⁻ x in t ∩ g⁻¹ • s, f x ∂μ : ((equiv.inv G).tsum_eq _).symm
... = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t ∩ s), f (x) ∂μ :
  by simp only [smul_set_inter, inv_smul_smul]
... = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :
  tsum_congr $ λ g, ((measure_preserving_smul g⁻¹ μ).set_lintegral_comp_emb
    (measurable_embedding_const_smul _) _ _).symm

@[to_additive] lemma measure_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ)
  (t : set α) :
  ν t = ∑' g : G, ν (t ∩ g • s) :=
have H : ν.restrict t ≪ μ, from measure.restrict_le_self.absolutely_continuous.trans hν,
by simpa only [set_lintegral_one, pi.one_def,
    measure.restrict_apply₀ ((h.null_measurable_set_smul _).mono_ac H), inter_comm]
  using h.lintegral_eq_tsum_of_ac H 1

@[to_additive] lemma measure_eq_tsum' (h : is_fundamental_domain G s μ) (t : set α) :
  μ t = ∑' g : G, μ (t ∩ g • s) :=
h.measure_eq_tsum_of_ac absolutely_continuous.rfl t

@[to_additive] lemma measure_eq_tsum (h : is_fundamental_domain G s μ) (t : set α) :
  μ t = ∑' g : G, μ (g • t ∩ s) :=
by simpa only [set_lintegral_one] using h.set_lintegral_eq_tsum' (λ _, 1) t

@[to_additive] lemma measure_zero_of_invariant (h : is_fundamental_domain G s μ) (t : set α)
  (ht : ∀ g : G, g • t = t) (hts : μ (t ∩ s) = 0) :
  μ t = 0 :=
by simp [measure_eq_tsum h, ht, hts]

/-- Given a measure space with an action of a finite group `G`, the measure of any `G`-invariant set
is determined by the measure of its intersection with a fundamental domain for the action of `G`. -/
@[to_additive measure_eq_card_smul_of_vadd_ae_eq_self "Given a measure space with an action of a
finite additive group `G`, the measure of any `G`-invariant set is determined by the measure of its
intersection with a fundamental domain for the action of `G`."]
lemma measure_eq_card_smul_of_smul_ae_eq_self [finite G]
  (h : is_fundamental_domain G s μ) (t : set α) (ht : ∀ g : G, (g • t : set α) =ᵐ[μ] t) :
  μ t = nat.card G • μ (t ∩ s) :=
begin
  haveI : fintype G := fintype.of_finite G,
  rw h.measure_eq_tsum,
  replace ht : ∀ g : G, ((g • t) ∩ s : set α) =ᵐ[μ] (t ∩ s : set α) :=
    λ g, ae_eq_set_inter (ht g) (ae_eq_refl s),
  simp_rw [measure_congr (ht _), tsum_fintype, finset.sum_const, nat.card_eq_fintype_card,
    finset.card_univ],
end

@[to_additive] protected lemma set_lintegral_eq (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) (f : α → ℝ≥0∞) (hf : ∀ (g : G) x, f (g • x) = f x) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
calc ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ : ht.set_lintegral_eq_tsum _ _
... = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ            : by simp only [hf, inter_comm]
... = ∫⁻ x in t, f x ∂μ                                      : (hs.set_lintegral_eq_tsum' _ _).symm

@[to_additive] lemma measure_set_eq (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) {A : set α} (hA₀ : measurable_set A)
  (hA : ∀ (g : G), (λ x, g • x) ⁻¹' A = A) :
  μ (A ∩ s) = μ (A ∩ t) :=
begin
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ,
  { refine hs.set_lintegral_eq ht (set.indicator A (λ _, 1)) _,
    intros g x,
    convert (set.indicator_comp_right (λ x : α, g • x)).symm,
    rw hA g },
  simpa [measure.restrict_apply hA₀, lintegral_indicator _ hA₀] using this
end

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive "If `s` and `t` are two fundamental domains of the same action, then their measures
are equal."]
protected lemma measure_eq (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) : μ s = μ t :=
by simpa only [set_lintegral_one] using hs.set_lintegral_eq ht (λ _, 1) (λ _ _, rfl)

@[to_additive] protected lemma ae_strongly_measurable_on_iff
  {β : Type*} [topological_space β] [pseudo_metrizable_space β]
  (hs : is_fundamental_domain G s μ) (ht : is_fundamental_domain G t μ) {f : α → β}
  (hf : ∀ (g : G) x, f (g • x) = f x) :
  ae_strongly_measurable f (μ.restrict s) ↔ ae_strongly_measurable f (μ.restrict t) :=
calc ae_strongly_measurable f (μ.restrict s)
    ↔ ae_strongly_measurable f (measure.sum $ λ g : G, (μ.restrict (g • t ∩ s))) :
  by simp only [← ht.restrict_restrict,
    ht.sum_restrict_of_ac restrict_le_self.absolutely_continuous]
... ↔ ∀ g : G, ae_strongly_measurable f (μ.restrict (g • (g⁻¹ • s ∩ t))) :
  by simp only [smul_set_inter, inter_comm, smul_inv_smul, ae_strongly_measurable_sum_measure_iff]
... ↔ ∀ g : G, ae_strongly_measurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s ∩ t))) : inv_surjective.forall
... ↔ ∀ g : G, ae_strongly_measurable f (μ.restrict (g⁻¹ • (g • s ∩ t))) : by simp only [inv_inv]
... ↔ ∀ g : G, ae_strongly_measurable f (μ.restrict (g • s ∩ t)) :
  begin
    refine forall_congr (λ g, _),
    have he : measurable_embedding ((•) g⁻¹ : α → α) := measurable_embedding_const_smul _,
    rw [← image_smul,
    ← ((measure_preserving_smul g⁻¹ μ).restrict_image_emb he _).ae_strongly_measurable_comp_iff he],
    simp only [(∘), hf]
  end
... ↔ ae_strongly_measurable f (μ.restrict t) :
  by simp only [← ae_strongly_measurable_sum_measure_iff, ← hs.restrict_restrict,
    hs.sum_restrict_of_ac restrict_le_self.absolutely_continuous]

@[to_additive] protected lemma has_finite_integral_on_iff (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) {f : α → E} (hf : ∀ (g : G) x, f (g • x) = f x) :
  has_finite_integral f (μ.restrict s) ↔ has_finite_integral f (μ.restrict t) :=
begin
  dunfold has_finite_integral,
  rw hs.set_lintegral_eq ht,
  intros g x, rw hf
end

@[to_additive] protected lemma integrable_on_iff (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) {f : α → E} (hf : ∀ (g : G) x, f (g • x) = f x) :
  integrable_on f s μ ↔ integrable_on f t μ :=
and_congr (hs.ae_strongly_measurable_on_iff ht hf) (hs.has_finite_integral_on_iff ht hf)

variables [normed_space ℝ E] [complete_space E]

@[to_additive] lemma integral_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ)
  (f : α → E) (hf : integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν :=
begin
  rw [← measure_theory.integral_sum_measure, h.sum_restrict_of_ac hν],
  rw h.sum_restrict_of_ac hν, -- Weirdly, these rewrites seem not to be combinable
  exact hf,
end

@[to_additive] lemma integral_eq_tsum (h : is_fundamental_domain G s μ)
  (f : α → E) (hf : integrable f μ) : ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ :=
integral_eq_tsum_of_ac h (by refl) f hf

@[to_additive] lemma integral_eq_tsum' (h : is_fundamental_domain G s μ)
  (f : α → E) (hf : integrable f μ) : ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ :=
calc ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ : h.integral_eq_tsum f hf
... = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ : ((equiv.inv G).tsum_eq _).symm
... = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ :
  tsum_congr $ λ g, (measure_preserving_smul g⁻¹ μ).set_integral_image_emb
    (measurable_embedding_const_smul _) _ _

@[to_additive] lemma set_integral_eq_tsum (h : is_fundamental_domain G s μ) {f : α → E}
  {t : set α} (hf : integrable_on f t μ) :
  ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :=
calc ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂(μ.restrict t) :
  h.integral_eq_tsum_of_ac restrict_le_self.absolutely_continuous f hf
... = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :
  by simp only [h.restrict_restrict, measure_smul, inter_comm]

@[to_additive] lemma set_integral_eq_tsum' (h : is_fundamental_domain G s μ) {f : α → E}
  {t : set α} (hf : integrable_on f t μ) :
  ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
calc ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :
  h.set_integral_eq_tsum hf
... = ∑' g : G, ∫ x in t ∩ g⁻¹ • s, f x ∂μ : ((equiv.inv G).tsum_eq _).symm
... = ∑' g : G, ∫ x in g⁻¹ • (g • t ∩ s), f (x) ∂μ :
  by simp only [smul_set_inter, inv_smul_smul]
... = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :
  tsum_congr $ λ g, (measure_preserving_smul g⁻¹ μ).set_integral_image_emb
    (measurable_embedding_const_smul _) _ _

@[to_additive] protected lemma set_integral_eq (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) {f : α → E} (hf : ∀ (g : G) x, f (g • x) = f x) :
  ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ :=
begin
  by_cases hfs : integrable_on f s μ,
  { have hft : integrable_on f t μ, by rwa ht.integrable_on_iff hs hf,
    calc ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ : ht.set_integral_eq_tsum hfs
    ... = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ : by simp only [hf, inter_comm]
    ... = ∫ x in t, f x ∂μ : (hs.set_integral_eq_tsum' hft).symm, },
  { rw [integral_undef hfs, integral_undef],
    rwa [hs.integrable_on_iff ht hf] at hfs }
end

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` such that the sets `g • t ∩ s` are pairwise a.e.-disjoint
has measure at most `μ s`. -/
@[to_additive "If the additive action of a countable group `G` admits an invariant measure `μ` with
a fundamental domain `s`, then every null-measurable set `t` such that the sets `g +ᵥ t ∩ s` are
pairwise a.e.-disjoint has measure at most `μ s`."]
 lemma measure_le_of_pairwise_disjoint (hs : is_fundamental_domain G s μ)
  (ht : null_measurable_set t μ) (hd : pairwise (ae_disjoint μ on (λ g : G, g • t ∩ s))) :
  μ t ≤ μ s :=
calc μ t = ∑' g : G, μ (g • t ∩ s) : hs.measure_eq_tsum t
... = μ (⋃ g : G, g • t ∩ s) : eq.symm $ measure_Union₀ hd $
  λ g, (ht.smul _).inter hs.null_measurable_set
... ≤ μ s : measure_mono (Union_subset $ λ g, inter_subset_right _ _)

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` of measure strictly greater than `μ s` contains two
points `x y` such that `g • x = y` for some `g ≠ 1`. -/
@[to_additive "If the additive action of a countable group `G` admits an invariant measure `μ` with
a fundamental domain `s`, then every null-measurable set `t` of measure strictly greater than `μ s`
contains two points `x y` such that `g +ᵥ x = y` for some `g ≠ 0`."]
lemma exists_ne_one_smul_eq (hs : is_fundamental_domain G s μ) (htm : null_measurable_set t μ)
  (ht : μ s < μ t) : ∃ (x y ∈ t) (g ≠ (1 : G)), g • x = y :=
begin
  contrapose! ht,
  refine hs.measure_le_of_pairwise_disjoint htm (pairwise.ae_disjoint $ λ g₁ g₂ hne, _),
  dsimp [function.on_fun],
  refine (disjoint.inf_left _ _).inf_right _,
  rw set.disjoint_left,
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩,
  refine ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) _,
  rw [mul_smul, ← hxy, inv_smul_smul]
end

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive "If `f` is invariant under the action of a countable additive group `G`, and `μ` is a
`G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is
the same as that of `f` on all of its domain."]
lemma ess_sup_measure_restrict (hs : is_fundamental_domain G s μ)
  {f : α → ℝ≥0∞} (hf : ∀ γ : G, ∀ x: α, f (γ • x) =  f x) :
  ess_sup f (μ.restrict s) = ess_sup f μ :=
begin
  refine le_antisymm (ess_sup_mono_measure' measure.restrict_le_self) _,
  rw [ess_sup_eq_Inf (μ.restrict s) f, ess_sup_eq_Inf μ f],
  refine Inf_le_Inf _,
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0),
  rw measure.restrict_apply₀' hs.null_measurable_set at ha,
  refine measure_zero_of_invariant hs _ _ ha,
  intros γ,
  ext x,
  rw mem_smul_set_iff_inv_smul_mem,
  simp only [mem_set_of_eq, hf (γ⁻¹) x],
end

end is_fundamental_domain

/-! ### Interior/frontier of a fundamental domain -/

section measurable_space
variables (G) [group G] [mul_action G α] (s : set α) {x : α}

/-- The boundary of a fundamental domain, those points of the domain that also lie in a nontrivial
translate. -/
@[to_additive measure_theory.add_fundamental_frontier "The boundary of a fundamental domain, those
points of the domain that also lie in a nontrivial translate."]
def fundamental_frontier : set α := s ∩ ⋃ (g : G) (hg : g ≠ 1), g • s

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[to_additive measure_theory.add_fundamental_interior "The interior of a fundamental domain, those
points of the domain not lying in any translate."]
def fundamental_interior : set α := s \ ⋃ (g : G) (hg : g ≠ 1), g • s

variables {G s}

@[simp, to_additive measure_theory.mem_add_fundamental_frontier]
lemma mem_fundamental_frontier :
  x ∈ fundamental_frontier G s ↔ x ∈ s ∧ ∃ (g : G) (hg : g ≠ 1), x ∈ g • s :=
by simp [fundamental_frontier]

@[simp, to_additive measure_theory.mem_add_fundamental_interior]
lemma mem_fundamental_interior :
  x ∈ fundamental_interior G s ↔ x ∈ s ∧ ∀ (g : G) (hg : g ≠ 1), x ∉ g • s :=
by simp [fundamental_interior]

@[to_additive measure_theory.add_fundamental_frontier_subset]
lemma fundamental_frontier_subset : fundamental_frontier G s ⊆ s := inter_subset_left _ _

@[to_additive measure_theory.add_fundamental_interior_subset]
lemma fundamental_interior_subset : fundamental_interior G s ⊆ s := diff_subset _ _

variables (G s)

@[to_additive measure_theory.disjoint_add_fundamental_interior_add_fundamental_frontier]
lemma disjoint_fundamental_interior_fundamental_frontier :
  disjoint (fundamental_interior G s) (fundamental_frontier G s) :=
disjoint_sdiff_self_left.mono_right inf_le_right

@[simp, to_additive measure_theory.add_fundamental_interior_union_add_fundamental_frontier]
lemma fundamental_interior_union_fundamental_frontier :
  fundamental_interior G s ∪ fundamental_frontier G s = s :=
diff_union_inter _ _

@[simp, to_additive measure_theory.add_fundamental_interior_union_add_fundamental_frontier]
lemma fundamental_frontier_union_fundamental_interior :
  fundamental_frontier G s ∪ fundamental_interior G s = s :=
inter_union_diff _ _

@[simp, to_additive measure_theory.sdiff_add_fundamental_interior]
lemma sdiff_fundamental_interior : s \ fundamental_interior G s = fundamental_frontier G s :=
sdiff_sdiff_right_self

@[simp, to_additive measure_theory.sdiff_add_fundamental_frontier]
lemma sdiff_fundamental_frontier : s \ fundamental_frontier G s = fundamental_interior G s :=
diff_self_inter

@[simp, to_additive measure_theory.add_fundamental_frontier_vadd]
lemma fundamental_frontier_smul [group H] [mul_action H α] [smul_comm_class H G α] (g : H) :
  fundamental_frontier G (g • s) = g • fundamental_frontier G s :=
by simp_rw [fundamental_frontier, smul_set_inter, smul_set_Union, smul_comm g]

@[simp, to_additive measure_theory.add_fundamental_interior_vadd]
lemma fundamental_interior_smul [group H] [mul_action H α] [smul_comm_class H G α] (g : H) :
  fundamental_interior G (g • s) = g • fundamental_interior G s :=
by simp_rw [fundamental_interior, smul_set_sdiff, smul_set_Union, smul_comm g]

@[to_additive measure_theory.pairwise_disjoint_add_fundamental_interior]
lemma pairwise_disjoint_fundamental_interior :
  pairwise (disjoint on λ g : G, g • fundamental_interior G s) :=
begin
  refine λ a b hab, disjoint_left.2 _,
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩,
  rw mem_fundamental_interior at hx hy,
  refine hx.2 (a⁻¹ * b) _ _,
  rwa [ne.def, inv_mul_eq_iff_eq_mul, mul_one, eq_comm],
  simpa [mul_smul, ←hxy, mem_inv_smul_set_iff] using hy.1,
end

variables [countable G] [measurable_space G] [measurable_space α] [has_measurable_smul G α]
  {μ : measure α} [smul_invariant_measure G α μ]

@[to_additive measure_theory.null_measurable_set.add_fundamental_frontier]
protected lemma null_measurable_set.fundamental_frontier (hs : null_measurable_set s μ) :
  null_measurable_set (fundamental_frontier G s) μ :=
hs.inter $ null_measurable_set.Union $ λ g, null_measurable_set.Union $ λ hg, hs.smul _

@[to_additive measure_theory.null_measurable_set.add_fundamental_interior]
protected lemma null_measurable_set.fundamental_interior (hs : null_measurable_set s μ) :
  null_measurable_set (fundamental_interior G s) μ :=
hs.diff $ null_measurable_set.Union $ λ g, null_measurable_set.Union $ λ hg, hs.smul _

end measurable_space

namespace is_fundamental_domain
section group
variables [countable G] [group G] [mul_action G α] [measurable_space α] {μ : measure α} {s : set α}
  (hs : is_fundamental_domain G s μ)
include hs

@[to_additive measure_theory.is_add_fundamental_domain.measure_add_fundamental_frontier]
lemma measure_fundamental_frontier : μ (fundamental_frontier G s) = 0 :=
by simpa only [fundamental_frontier, Union₂_inter, measure_Union_null_iff', one_smul,
  measure_Union_null_iff, inter_comm s, function.on_fun] using λ g (hg : g ≠ 1), hs.ae_disjoint hg

@[to_additive measure_theory.is_add_fundamental_domain.measure_add_fundamental_interior]
lemma measure_fundamental_interior : μ (fundamental_interior G s) = μ s :=
measure_diff_null' hs.measure_fundamental_frontier

end group

variables [countable G] [group G] [mul_action G α] [measurable_space α] {μ : measure α} {s : set α}
  (hs : is_fundamental_domain G s μ) [measurable_space G] [has_measurable_smul G α]
  [smul_invariant_measure G α μ]
include hs

protected lemma fundamental_interior : is_fundamental_domain G (fundamental_interior G s) μ :=
{ null_measurable_set := hs.null_measurable_set.fundamental_interior _ _,
  ae_covers := begin
    simp_rw [ae_iff, not_exists, ←mem_inv_smul_set_iff, set_of_forall, ←compl_set_of, set_of_mem_eq,
      ←compl_Union],
    have : (⋃ g : G, g⁻¹ • s) \ (⋃ g : G, g⁻¹ • fundamental_frontier G s) ⊆
      ⋃ g : G, g⁻¹ • fundamental_interior G s,
    { simp_rw [diff_subset_iff, ←Union_union_distrib, ←smul_set_union,
        fundamental_frontier_union_fundamental_interior] },
    refine eq_bot_mono (μ.mono $ compl_subset_compl.2 this) _,
    simp only [Union_inv_smul, outer_measure.measure_of_eq_coe, coe_to_outer_measure, compl_sdiff,
      ennreal.bot_eq_zero, himp_eq, sup_eq_union, @Union_smul_eq_set_of_exists _ _ _ _ s],
    exact measure_union_null
      (measure_Union_null $ λ _, measure_smul_null hs.measure_fundamental_frontier _) hs.ae_covers,
  end,
  ae_disjoint := (pairwise_disjoint_fundamental_interior _ _).mono $ λ _ _, disjoint.ae_disjoint }

end is_fundamental_domain
end measure_theory
