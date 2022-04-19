/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import probability.variance

/-!
# Identically distributed random variables

-/

open measure_theory filter finset

noncomputable theory

open_locale topological_space big_operators measure_theory ennreal nnreal

variables {α β γ δ : Type*} [measurable_space α] [measurable_space β]
  [measurable_space γ] [measurable_space δ]

namespace probability_theory

/-- Two functions defined on two (possibly different) measure spaces are identically distributed if
their image measures coincide. This only makes sense when the functions are ae measurable
(as otherwise the image measures are not defined), so we require this as well in the definition. -/
structure ident_distrib
  (f : α → γ) (g : β → γ) (μ : measure α . volume_tac)  (ν : measure β . volume_tac) : Prop :=
(ae_measurable_fst : ae_measurable f μ)
(ae_measurable_snd : ae_measurable g ν)
(map_eq : measure.map f μ = measure.map g ν)

namespace ident_distrib

open topological_space

variables {μ : measure α} {ν : measure β} {f : α → γ} {g : β → γ}

protected lemma ae_measurable (h : ident_distrib f g μ ν) :
  ae_measurable f μ := h.ae_measurable_fst

protected lemma refl (hf : ae_measurable f μ) :
  ident_distrib f f μ μ :=
{ ae_measurable_fst := hf,
  ae_measurable_snd := hf,
  map_eq := rfl }

protected lemma symm (h : ident_distrib f g μ ν) : ident_distrib g f ν μ :=
{ ae_measurable_fst := h.ae_measurable_snd,
  ae_measurable_snd := h.ae_measurable_fst,
  map_eq := h.map_eq.symm }

protected lemma trans {ρ : measure δ} {h : δ → γ}
  (h₁ : ident_distrib f g μ ν) (h₂ : ident_distrib g h ν ρ) : ident_distrib f h μ ρ :=
{ ae_measurable_fst := h₁.ae_measurable_fst,
  ae_measurable_snd := h₂.ae_measurable_snd,
  map_eq := h₁.map_eq.trans h₂.map_eq }

protected lemma comp_of_ae_measurable {u : γ → δ} (h : ident_distrib f g μ ν)
  (hu : ae_measurable u (measure.map f μ)) :
  ident_distrib (u ∘ f) (u ∘ g) μ ν :=
{ ae_measurable_fst := hu.comp_ae_measurable h.ae_measurable,
  ae_measurable_snd :=
    by { rw h.map_eq at hu, exact hu.comp_ae_measurable h.symm.ae_measurable },
  map_eq :=
  begin
    rw [← ae_measurable.map_map_of_ae_measurable hu h.ae_measurable,
      ← ae_measurable.map_map_of_ae_measurable _ h.symm.ae_measurable, h.map_eq],
    rwa ← h.map_eq,
  end }

protected lemma comp {u : γ → δ} (h : ident_distrib f g μ ν) (hu : measurable u) :
  ident_distrib (u ∘ f) (u ∘ g) μ ν :=
h.comp_of_ae_measurable hu.ae_measurable

lemma ae_mem_snd (h : ident_distrib f g μ ν) {t : set γ}
  (tmeas : measurable_set t) (ht : ∀ᵐ x ∂μ, f x ∈ t) :
   ∀ᵐ x ∂ν, g x ∈ t :=
begin
  apply (ae_map_iff h.symm.ae_measurable tmeas).1,
  rw ← h.map_eq,
  exact (ae_map_iff h.ae_measurable tmeas).2 ht,
end

protected lemma ae_strongly_measurable [topological_space γ]
  [metrizable_space γ] [opens_measurable_space γ] [second_countable_topology γ]
  (h : ident_distrib f g μ ν) :
  ae_strongly_measurable f μ :=
h.ae_measurable.ae_strongly_measurable

lemma ae_strongly_measurable_snd [topological_space γ] [metrizable_space γ] [borel_space γ]
  (h : ident_distrib f g μ ν) (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable g ν :=
begin
  refine ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨h.symm.ae_measurable, _⟩,
  rcases (ae_strongly_measurable_iff_ae_measurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩,
  refine ⟨closure t, t_sep.closure, _⟩,
  apply h.ae_mem_snd is_closed_closure.measurable_set,
  filter_upwards [ht] with x hx using subset_closure hx,
end

lemma ae_strongly_measurable_iff [topological_space γ] [metrizable_space γ] [borel_space γ]
  (h : ident_distrib f g μ ν) :
  ae_strongly_measurable f μ ↔ ae_strongly_measurable g ν :=
⟨λ hf, h.ae_strongly_measurable_snd hf, λ hg, h.symm.ae_strongly_measurable_snd hg⟩

lemma ess_sup_eq [conditionally_complete_linear_order γ] [topological_space γ]
  [opens_measurable_space γ] [order_closed_topology γ] (h : ident_distrib f g μ ν) :
  ess_sup f μ = ess_sup g ν :=
begin
  have I : ∀ a, ν {x : β | a < g x} = μ {x : α | a < f x},
  { assume a,
    have A : ν {x : β | a < g x} = (measure.map g ν) {x | a < x},
    { rw measure.map_apply_of_ae_measurable h.symm.ae_measurable,
      refl,
      exact measurable_set_Ioi },
    have B : μ {x : α | a < f x} = (measure.map f μ) {x | a < x},
    { rw measure.map_apply_of_ae_measurable h.ae_measurable,
      refl,
      exact measurable_set_Ioi },
    rw [A, B, h.map_eq] },
  simp_rw [ess_sup_eq_Inf, I],
end

lemma lintegral_eq {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (h : ident_distrib f g μ ν) :
  ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂ν :=
begin
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν,
  rw [← lintegral_map' ae_measurable_id h.ae_measurable,
      ← lintegral_map' ae_measurable_id h.symm.ae_measurable, h.map_eq],
end

lemma integral_eq [normed_group γ] [normed_space ℝ γ] [complete_space γ] [borel_space γ]
  (h : ident_distrib f g μ ν) : ∫ x, f x ∂μ = ∫ x, g x ∂ν :=
begin
  by_cases hf : ae_strongly_measurable f μ,
  { have A : ae_strongly_measurable id (measure.map f μ),
    { rw ae_strongly_measurable_iff_ae_measurable_separable,
      rcases (ae_strongly_measurable_iff_ae_measurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩,
      refine ⟨ae_measurable_id, ⟨closure t, t_sep.closure, _⟩⟩,
      rw ae_map_iff h.ae_measurable,
      { filter_upwards [ht] with x hx using subset_closure hx },
      { exact is_closed_closure.measurable_set } },
    change ∫ x, id (f x) ∂μ = ∫ x, id (g x) ∂ν,
    rw [← integral_map h.ae_measurable A],
    rw h.map_eq at A,
    rw [← integral_map h.symm.ae_measurable A, h.map_eq] },
  { rw integral_non_ae_strongly_measurable hf,
    rw h.ae_strongly_measurable_iff at hf,
    rw integral_non_ae_strongly_measurable hf }
end

lemma snorm_eq [normed_group γ] [opens_measurable_space γ] (h : ident_distrib f g μ ν) (p : ℝ≥0∞) :
  snorm f p μ = snorm g p ν :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp only [h_top, snorm, snorm_ess_sup, ennreal.top_ne_zero, eq_self_iff_true, if_true,
      if_false],
    apply ess_sup_eq,
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurable_nnnorm) },
  simp only [snorm_eq_snorm' h0 h_top, snorm', one_div],
  congr' 1,
  apply lintegral_eq,
  exact h.comp
    (measurable.pow_const (measurable_coe_nnreal_ennreal.comp measurable_nnnorm) p.to_real),
end

lemma mem_ℒp_snd [normed_group γ] [borel_space γ]
  {p : ℝ≥0∞} (h : ident_distrib f g μ ν) (hf : mem_ℒp f p μ) :
  mem_ℒp g p ν :=
begin
  refine ⟨h.ae_strongly_measurable_snd hf.ae_strongly_measurable, _⟩,
  rw ← h.snorm_eq,
  exact hf.2
end

lemma mem_ℒp_iff [normed_group γ] [borel_space γ] {p : ℝ≥0∞} (h : ident_distrib f g μ ν) :
  mem_ℒp f p μ ↔ mem_ℒp g p ν :=
⟨λ hf, h.mem_ℒp_snd hf, λ hg, h.symm.mem_ℒp_snd hg⟩

lemma integrable_snd [normed_group γ] [borel_space γ] (h : ident_distrib f g μ ν)
  (hf : integrable f μ) : integrable g ν :=
begin
  rw ← mem_ℒp_one_iff_integrable at hf ⊢,
  exact h.mem_ℒp_snd hf
end

lemma integrable_iff [normed_group γ] [borel_space γ] (h : ident_distrib f g μ ν) :
  integrable f μ ↔ integrable g ν :=
⟨λ hf, h.integrable_snd hf, λ hg, h.symm.integrable_snd hg⟩

protected lemma norm [normed_group γ] [borel_space γ] (h : ident_distrib f g μ ν) :
  ident_distrib (λ x, ∥f x∥) (λ x, ∥g x∥) μ ν :=
h.comp measurable_norm

protected lemma nnnorm [normed_group γ] [borel_space γ] (h : ident_distrib f g μ ν) :
  ident_distrib (λ x, ∥f x∥₊) (λ x, ∥g x∥₊) μ ν :=
h.comp measurable_nnnorm

protected lemma pow [has_pow γ ℕ] [has_measurable_pow γ ℕ] (h : ident_distrib f g μ ν) {n : ℕ} :
  ident_distrib (λ x, (f x) ^ n) (λ x, (g x) ^ n) μ ν :=
h.comp (measurable_id.pow_const n)

protected lemma sq [has_pow γ ℕ] [has_measurable_pow γ ℕ] (h : ident_distrib f g μ ν) :
  ident_distrib (λ x, (f x) ^ 2) (λ x, (g x) ^ 2) μ ν :=
h.comp (measurable_id.pow_const 2)

protected lemma coe_nnreal_ennreal {f : α → ℝ≥0} {g : β → ℝ≥0} (h : ident_distrib f g μ ν) :
  ident_distrib (λ x, (f x : ℝ≥0∞)) (λ x, (g x : ℝ≥0∞)) μ ν :=
h.comp measurable_coe_nnreal_ennreal

@[to_additive]
lemma mul_const [has_mul γ] [has_measurable_mul γ] (h : ident_distrib f g μ ν) (c : γ) :
  ident_distrib (λ x, f x * c) (λ x, g x * c) μ ν :=
h.comp (measurable_mul_const c)

@[to_additive]
lemma const_mul [has_mul γ] [has_measurable_mul γ] (h : ident_distrib f g μ ν) (c : γ) :
  ident_distrib (λ x, c * f x) (λ x, c * g x) μ ν :=
h.comp (measurable_const_mul c)

@[to_additive]
lemma div_const [has_div γ] [has_measurable_div γ] (h : ident_distrib f g μ ν) (c : γ) :
  ident_distrib (λ x, f x / c) (λ x, g x / c) μ ν :=
h.comp (has_measurable_div.measurable_div_const c)

@[to_additive]
lemma const_div [has_div γ] [has_measurable_div γ] (h : ident_distrib f g μ ν) (c : γ) :
  ident_distrib (λ x, c / f x) (λ x, c / g x) μ ν :=
h.comp (has_measurable_div.measurable_const_div c)

lemma variance_eq {f : α → ℝ} {g : β → ℝ} (h : ident_distrib f g μ ν) :
  variance f μ = variance g ν :=
begin
  convert (h.sub_const (∫ x, f x ∂μ)).sq.integral_eq,
  rw h.integral_eq,
  refl
end

end ident_distrib

end probability_theory
