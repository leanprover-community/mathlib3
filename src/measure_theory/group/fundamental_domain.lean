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
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.
-/

open_locale ennreal pointwise topological_space nnreal ennreal measure_theory
open measure_theory measure_theory.measure set function topological_space filter

namespace measure_theory

/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
@[protect_proj] structure is_add_fundamental_domain (G : Type*) {α : Type*} [has_zero G]
  [has_vadd G α] [measurable_space α] (s : set α) (μ : measure α . volume_tac) : Prop :=
(null_measurable_set : null_measurable_set s μ)
(ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s)
(ae_disjoint : ∀ g ≠ (0 : G), ae_disjoint μ (g +ᵥ s) s)

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[protect_proj, to_additive is_add_fundamental_domain]
structure is_fundamental_domain (G : Type*) {α : Type*} [has_one G] [has_scalar G α]
  [measurable_space α] (s : set α) (μ : measure α . volume_tac) : Prop :=
(null_measurable_set : null_measurable_set s μ)
(ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
(ae_disjoint : ∀ g ≠ (1 : G), ae_disjoint μ (g • s) s)

namespace is_fundamental_domain

variables {G α E : Type*} [group G] [mul_action G α] [measurable_space α]
  [normed_group E] {s t : set α} {μ : measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive "If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set
`s`, then `s` is a fundamental domain for the additive action of `G` on `α`."]
lemma mk' (h_meas : null_measurable_set s μ) (h_exists : ∀ x : α, ∃! g : G, g • x ∈ s) :
  is_fundamental_domain G s μ :=
{ null_measurable_set := h_meas,
  ae_covers := eventually_of_forall $ λ x, (h_exists x).exists,
  ae_disjoint := λ g hne, disjoint.ae_disjoint $ disjoint_left.2
    begin
      rintro _ ⟨x, hx, rfl⟩ hgx,
      rw ← one_smul G x at hx,
      exact hne ((h_exists x).unique hgx hx)
    end }

@[to_additive] lemma Union_smul_ae_eq (h : is_fundamental_domain G s μ) :
  (⋃ g : G, g • s) =ᵐ[μ] univ :=
eventually_eq_univ.2 $ h.ae_covers.mono $ λ x ⟨g, hg⟩, mem_Union.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive] lemma mono (h : is_fundamental_domain G s μ) {ν : measure α} (hle : ν ≪ μ) :
  is_fundamental_domain G s ν :=
⟨h.1.mono_ac hle, hle h.2, λ g hg, hle (h.3 g hg)⟩

variables [measurable_space G] [has_measurable_smul G α] [smul_invariant_measure G α μ]

@[to_additive] lemma null_measurable_set_smul (h : is_fundamental_domain G s μ) (g : G) :
  null_measurable_set (g • s) μ :=
h.null_measurable_set.smul g

@[to_additive] lemma restrict_restrict (h : is_fundamental_domain G s μ) (g : G) (t : set α) :
  (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
restrict_restrict₀ ((h.null_measurable_set_smul g).mono restrict_le_self)

@[to_additive] lemma pairwise_ae_disjoint (h : is_fundamental_domain G s μ) :
  pairwise (λ g₁ g₂ : G, ae_disjoint μ (g₁ • s) (g₂ • s)) :=
λ g₁ g₂ hne,
calc μ (g₁ • s ∩ g₂ • s) = μ (g₂ • ((g₂⁻¹ * g₁) • s ∩ s)) :
  by rw [smul_set_inter, smul_smul, mul_inv_cancel_left]
... = μ ((g₂⁻¹ * g₁) • s ∩ s) : measure_smul_set _ _ _
... = 0 : h.ae_disjoint _ $ mt inv_mul_eq_one.1 hne.symm

@[to_additive] lemma pairwise_ae_disjoint_of_ac {ν} (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) :
  pairwise (λ g₁ g₂ : G, ae_disjoint ν (g₁ • s) (g₂ • s)) :=
h.pairwise_ae_disjoint.mono $ λ g₁ g₂ H, hν H

@[to_additive] lemma preimage_of_equiv (h : is_fundamental_domain G s μ) {f : α → α}
  (hf : quasi_measure_preserving f μ μ) {e : G → G} (he : bijective e)
  (hef : ∀ g, semiconj f ((•) (e g)) ((•) g)) :
  is_fundamental_domain G (f ⁻¹' s) μ :=
{ null_measurable_set := h.null_measurable_set.preimage hf,
  ae_covers := (hf.ae h.ae_covers).mono $ λ x ⟨g, hg⟩, ⟨e g, by rwa [mem_preimage, hef g x]⟩,
  ae_disjoint := λ g hg,
    begin
      lift e to G ≃ G using he,
      have : (e.symm g⁻¹)⁻¹ ≠ (e.symm 1)⁻¹, by simp [hg],
      convert (h.pairwise_ae_disjoint _ _ this).preimage hf using 1,
      { simp only [← preimage_smul_inv, preimage_preimage, ← hef _ _, e.apply_symm_apply,
          inv_inv] },
      { ext1 x,
        simp only [mem_preimage, ← preimage_smul, ← hef _ _, e.apply_symm_apply, one_smul] }
    end }

@[to_additive] lemma image_of_equiv (h : is_fundamental_domain G s μ)
  (f : measurable_equiv α α) (hfμ : measure_preserving f μ μ)
  (e : equiv.perm G) (hef : ∀ g, semiconj f ((•) (e g)) ((•) g)) :
  is_fundamental_domain G (f '' s) μ :=
begin
  rw f.image_eq_preimage,
  refine h.preimage_of_equiv hfμ.symm.quasi_measure_preserving e.symm.bijective (λ g x, _),
  rcases f.surjective x with ⟨x, rfl⟩,
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]
end

@[to_additive] lemma smul (h : is_fundamental_domain G s μ) (g : G) :
  is_fundamental_domain G (g • s) μ :=
h.image_of_equiv (measurable_equiv.smul g) (measure_preserving_smul _ _)
  ⟨λ g', g⁻¹ * g' * g, λ g', g * g' * g⁻¹, λ g', by simp [mul_assoc], λ g', by simp [mul_assoc]⟩ $
  λ g' x, by simp [smul_smul, mul_assoc]

@[to_additive] lemma smul_of_comm {G' : Type*} [group G'] [mul_action G' α] [measurable_space G']
  [has_measurable_smul G' α] [smul_invariant_measure G' α μ] [smul_comm_class G' G α]
  (h : is_fundamental_domain G s μ) (g : G') :
  is_fundamental_domain G (g • s) μ :=
h.image_of_equiv (measurable_equiv.smul g) (measure_preserving_smul _ _) (equiv.refl _) $
  smul_comm g

variables [encodable G] {ν : measure α}

@[to_additive] lemma sum_restrict_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) :
  sum (λ g : G, ν.restrict (g • s)) = ν :=
by rw [← restrict_Union_ae (h.pairwise_ae_disjoint.mono $ λ i j h, hν h)
    (λ g, (h.null_measurable_set_smul g).mono_ac hν),
  restrict_congr_set (hν h.Union_smul_ae_eq), restrict_univ]

@[to_additive] lemma lintegral_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ)
  (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν :=
by rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[to_additive] lemma sum_restrict (h : is_fundamental_domain G s μ) :
  sum (λ g : G, μ.restrict (g • s)) = μ :=
h.sum_restrict_of_ac (refl _)

lemma measure_zero_of_invariant (h : is_fundamental_domain G s μ) {t : set α}
  (ht : ∀ g : G, ∀ x ∈ t, g • x ∈ t)
  (ht' : μ.restrict s t = 0) :
  μ t = 0 :=
begin
  sorry,
/-  set π : G → G ⧸ Γ := quotient_group.mk,
  intros s hs,
  rw map_apply at hs ⊢,
  set pre_s := π ⁻¹' s,
  rw ← h𝓕.sum_restrict_of_ac (_ : μ ≪ μ),
  --change (μ.restrict 𝓕) pre_s = 0 at hs,
  -/
end

@[to_additive] lemma lintegral_eq_tsum (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞) :
  ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive] lemma set_lintegral_eq_tsum' (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞)
  (t : set α) : ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
calc ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂(μ.restrict t) :
  h.lintegral_eq_tsum_of_ac restrict_le_self.absolutely_continuous _
... = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :
  by simp only [h.restrict_restrict, inter_comm]

@[to_additive] lemma set_lintegral_eq_tsum (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞)
  (t : set α) :
  ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
calc ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :
  h.set_lintegral_eq_tsum' f t
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
by simpa only [set_lintegral_one] using h.set_lintegral_eq_tsum (λ _, 1) t

@[to_additive] lemma measure_zero_of_invariant (h : is_fundamental_domain G s μ) (t : set α)
  (ht : ∀ g : G, g • t = t) (hts : μ (t ∩ s) = 0) :
  μ t = 0 :=
by simp [measure_eq_tsum h, ht, hts]

@[to_additive] protected lemma set_lintegral_eq (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) (f : α → ℝ≥0∞) (hf : ∀ (g : G) x, f (g • x) = f x) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
calc ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ : ht.set_lintegral_eq_tsum' _ _
... = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ            : by simp only [hf, inter_comm]
... = ∫⁻ x in t, f x ∂μ                                      : (hs.set_lintegral_eq_tsum _ _).symm

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
  {β : Type*} [topological_space β] [metrizable_space β]
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

@[to_additive] protected lemma set_integral_eq (hs : is_fundamental_domain G s μ)
  (ht : is_fundamental_domain G t μ) {f : α → E} (hf : ∀ (g : G) x, f (g • x) = f x) :
  ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ :=
begin
  by_cases hfs : integrable_on f s μ,
  { have hft : integrable_on f t μ, by rwa ht.integrable_on_iff hs hf,
    have hac : ∀ {u}, μ.restrict u ≪ μ := λ u, restrict_le_self.absolutely_continuous,
    calc ∫ x in s, f x ∂μ = ∫ x in ⋃ g : G, g • t, f x ∂(μ.restrict s) :
      by rw [restrict_congr_set (hac ht.Union_smul_ae_eq), restrict_univ]
    ... = ∑' g : G, ∫ x in g • t, f x ∂(μ.restrict s) :
      integral_Union_ae (λ g, (ht.null_measurable_set_smul g).mono_ac hac)
        (ht.pairwise_ae_disjoint_of_ac hac) hfs.integrable.integrable_on
    ... = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ :
      by simp only [ht.restrict_restrict, inter_comm]
    ... = ∑' g : G, ∫ x in s ∩ g⁻¹ • t, f x ∂μ : ((equiv.inv G).tsum_eq _).symm
    ... = ∑' g : G, ∫ x in g⁻¹ • (g • s ∩ t), f x ∂μ :
      by simp only [smul_set_inter, inv_smul_smul]
    ... = ∑' g : G, ∫ x in g • s ∩ t, f (g⁻¹ • x) ∂μ :
      tsum_congr $ λ g, (measure_preserving_smul g⁻¹ μ).set_integral_image_emb
        (measurable_embedding_const_smul _) _ _
    ... = ∑' g : G, ∫ x in g • s, f x ∂(μ.restrict t) :
      by simp only [hf, hs.restrict_restrict]
    ... = ∫ x in ⋃ g : G, g • s, f x ∂(μ.restrict t) :
      (integral_Union_ae (λ g, (hs.null_measurable_set_smul g).mono_ac hac)
        (hs.pairwise_ae_disjoint.mono $ λ i j h, hac h) hft.integrable.integrable_on).symm
    ... = ∫ x in t, f x ∂μ :
      by rw [restrict_congr_set (hac hs.Union_smul_ae_eq), restrict_univ] },
  { rw [integral_undef hfs, integral_undef],
    rwa [hs.integrable_on_iff ht hf] at hfs }
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

@[to_additive] lemma integral_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ)
  (f : α → E) (hf : integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν :=
begin
  rw ← measure_theory.integral_sum_measure,
  rw h.sum_restrict_of_ac hν,
  rw h.sum_restrict_of_ac hν,
  exact hf,
end

@[to_additive] lemma set_integral_eq_tsum' (h : is_fundamental_domain G s μ) (f : α → E)
  (t : set α) (hf : integrable f (μ.restrict t)) :
  ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :=
calc ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂(μ.restrict t) :
  h.integral_eq_tsum_of_ac restrict_le_self.absolutely_continuous f hf
... = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :
  by simp only [h.restrict_restrict, measure_smul_set, inter_comm]


@[to_additive] lemma set_integral_eq_tsum (h : is_fundamental_domain G s μ) (f : α → E)
  (t : set α) (hf : integrable f (μ.restrict t)) :
  ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
calc ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :
  h.set_integral_eq_tsum' f t hf
... = ∑' g : G, ∫ x in t ∩ g⁻¹ • s, f x ∂μ : ((equiv.inv G).tsum_eq _).symm
... = ∑' g : G, ∫ x in g⁻¹ • (g • t ∩ s), f (x) ∂μ :
  by simp only [smul_set_inter, inv_smul_smul]
... = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :
  tsum_congr $ λ g, (measure_preserving_smul g⁻¹ μ).set_integral_image_emb
    (measurable_embedding_const_smul _) _ _

end is_fundamental_domain

end measure_theory
