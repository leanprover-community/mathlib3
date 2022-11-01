/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.constructions.prod

/-!
# Markov Kernel

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

-/

open measure_theory

open_locale measure_theory ennreal

namespace measure_theory

variables {α β γ E : Type*}
  {mα : measurable_space α} {μα : measure α}
  {mβ : measurable_space β} {μβ : measure β}
  {mγ : measurable_space γ} {μγ : measure γ}

/-
localized "notation P `[` X `;` s `]` := ∫ x in s, X x ∂P" in measure_theory

noncomputable
def cond_meas {m₀ : measurable_space α} (μ : measure α) (s : set α) (m : measurable_space α) :
  α → ℝ :=
  μ[s.indicator (λ _, (1 : ℝ)) | m]

lemma cond_meas_def : cond_meas μ s m = μ[s.indicator (λ _, (1 : ℝ)) | m] := rfl

lemma set_integral_cond_meas {hm : m ≤ m₀} [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (ht : measurable_set[m] t)  :
  μ[cond_meas μ s m; t] = (μ (s ∩ t)).to_real :=
by rw [cond_meas_def, set_integral_condexp hm
    ((integrable_indicator_iff hs).mpr (integrable_on_const.mpr (or.inr hμs.lt_top))) ht,
  integral_indicator_const _ hs, measure.restrict_apply hs, smul_eq_mul, mul_one]
-/

instance measure.has_measurable_add₂ {m : measurable_space β} : has_measurable_add₂ (measure β) :=
begin
  refine ⟨measure.measurable_of_measurable_coe _ (λ s hs, _)⟩,
  simp_rw [measure.coe_add, pi.add_apply],
  refine measurable.add _ _,
  { exact (measure.measurable_coe hs).comp measurable_fst, },
  { exact (measure.measurable_coe hs).comp measurable_snd, },
end

def transition_kernel (mα : measurable_space α) (mβ : measurable_space β) :
  add_submonoid (α → measure β) :=
{ carrier := measurable, -- ∀ s : set β, measurable_set[mβ] s → measurable[mα] (λ a, κ a s)
  zero_mem' := measurable_zero,
  add_mem' := λ f g hf hg, measurable.add hf hg, }

instance : has_coe_to_fun (transition_kernel mα mβ) (λ _, α → measure β) := ⟨λ κ, κ.val⟩

@[ext] lemma ext {κ : transition_kernel mα mβ} {η : transition_kernel mα mβ} (h : ∀ a, κ a = η a) :
  κ = η :=
by { ext1, ext1 a, exact h a, }

class is_markov_kernel (κ : transition_kernel mα mβ) : Prop :=
(is_probability_measure : ∀ a, is_probability_measure (κ a))

class is_finite_kernel (κ : transition_kernel mα mβ) : Prop :=
(exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a set.univ ≤ C)

def singular (κ : ℕ → transition_kernel mα mβ) : Prop :=
∃ s : ℕ → set (α × β), ∀ i a, κ i a {b | (a,b) ∈ s i}ᶜ = 0

class is_sigma_finite_kernel (κ : transition_kernel mα mβ) : Prop :=
(tsum_singular : ∃ κs : ℕ → transition_kernel mα mβ,
  (∀ n, is_finite_kernel (κs n)) ∧ (∀ a s, κ a s = ∑' n, κs n a s) ∧ singular κs)

class is_s_finite_kernel (κ : transition_kernel mα mβ) : Prop :=
(tsum_finite : ∃ κs : ℕ → transition_kernel mα mβ,
  (∀ n, is_finite_kernel (κs n)) ∧ ∀ a s, κ a s = ∑' n, κs n a s)

variables {κ : transition_kernel mα mβ}

instance todo [h : is_markov_kernel κ] (a : α) : is_probability_measure (κ a) :=
is_markov_kernel.is_probability_measure a

instance todo' [h : is_finite_kernel κ] (a : α) : is_finite_measure (κ a) :=
⟨(h.exists_univ_le.some_spec.2 a).trans_lt h.exists_univ_le.some_spec.1⟩

instance is_markov_kernel.is_finite_kernel [h : is_markov_kernel κ] : is_finite_kernel κ :=
⟨⟨1, ennreal.one_lt_top, λ a, prob_le_one⟩⟩

instance is_finite_kernel.is_sigma_finite_kernel [h : is_finite_kernel κ] :
  is_sigma_finite_kernel κ :=
⟨⟨λ n, if n = 0 then κ else 0, sorry, sorry, sorry⟩⟩

instance is_sigma_finite_kernel.is_s_finite_kernel [h : is_sigma_finite_kernel κ] :
  is_s_finite_kernel κ :=
⟨⟨h.tsum_singular.some, h.tsum_singular.some_spec.1, h.tsum_singular.some_spec.2.1⟩⟩

namespace transition_kernel

noncomputable
def seq (κ : transition_kernel mα mβ) [h : is_s_finite_kernel κ]
  [decidable (is_sigma_finite_kernel κ)] :
  ℕ → transition_kernel mα mβ :=
if hσ : is_sigma_finite_kernel κ then hσ.tsum_singular.some else h.tsum_finite.some

lemma tsum_seq (κ : transition_kernel mα mβ) [h : is_s_finite_kernel κ]
  [decidable (is_sigma_finite_kernel κ)] (a : α) (s : set β) :
  ∑' n, transition_kernel.seq κ n a s = κ a s :=
begin
  simp_rw seq,
  split_ifs with hσ hσ,
  { exact (hσ.tsum_singular.some_spec.2.1 a s).symm, },
  { exact (h.tsum_finite.some_spec.2 a s).symm, },
end

lemma singular_seq (κ : transition_kernel mα mβ) [h : is_sigma_finite_kernel κ]
  [decidable (is_sigma_finite_kernel κ)] :
  singular (transition_kernel.seq κ) :=
by { rw [seq, dif_pos h], exact h.tsum_singular.some_spec.2.2, }

end transition_kernel


/- Regular conditional distribution -/
--def is_reg_cond_distribution (κ : transition_kernel mα mβ) (Y : α → β) : Prop :=
--∀ᵐ ω ∂μ, ∀ s : set β, κ ω s = ennreal.of_real (cond_meas μ (Y ⁻¹' s) mα ω)

-- ∀ᵐ ω ∂μ, ∀ s : set β, κ ω s = μ[(Y ⁻¹' s).indicator (λ _, 1) | mα] ω
-- ∀ᵐ ω ∂μ, ∀ s : set β, κ ω s = μ[Y ∈ s | mα] ω

namespace transition_kernel

protected lemma measurable (κ : transition_kernel mα mβ) : measurable κ := κ.prop

protected lemma measurable_coe (κ : transition_kernel mα mβ)
  {s : set β} (hs : measurable_set[mβ] s) :
  measurable[mα] (λ a, κ a s) :=
(measure.measurable_coe hs).comp (transition_kernel.measurable κ)

/-- Constant kernel, which always returns the same measure. -/
def const (mα : measurable_space α) (mβ : measurable_space β) (μβ : measure β) :
  transition_kernel mα mβ :=
{ val := λ _, μβ,
  property := measure.measurable_of_measurable_coe _ (λ s hs, measurable_const), }

/-- Kernel which to `a` associates the dirac measure at `f a`. -/
noncomputable
def deterministic {mα : measurable_space α} {mβ : measurable_space β} {f : α → β}
  (hf : measurable f) :
  transition_kernel mα mβ :=
{ val := λ a, measure.dirac (f a),
  property :=
    begin
      refine measure.measurable_of_measurable_coe _ (λ s hs, _),
      simp_rw measure.dirac_apply' _ hs,
      refine measurable.indicator _ (hf hs),
      simp only [pi.one_apply, measurable_const],
    end, }

lemma deterministic_apply {mα : measurable_space α} {mβ : measurable_space β} {f : α → β}
  (hf : measurable f) (a : α) {s : set β} (hs : measurable_set s) :
  deterministic hf a s = s.indicator (λ _, 1) (f a) :=
begin
  rw [deterministic],
  change measure.dirac (f a) s = s.indicator 1 (f a),
  simp_rw measure.dirac_apply' _ hs,
end

lemma is_finite_measure_deterministic {mα : measurable_space α} {mβ : measurable_space β}
  {f : α → β} (hf : measurable f) (a : α) :
  is_finite_measure (deterministic hf a) :=
by { simp_rw [deterministic], apply_instance, }

lemma is_finite_kernel_const [hμβ : is_finite_measure μβ] : is_finite_kernel (const mα mβ μβ) :=
⟨⟨μβ set.univ, measure_lt_top _ _, λ a, le_rfl⟩⟩

lemma is_markov_kernel_const [hμβ : is_probability_measure μβ] :
  is_markov_kernel (const mα mβ μβ) :=
⟨λ a, hμβ⟩

def of_fun_of_countable (mα : measurable_space α) (mβ : measurable_space β)
  [countable α] [measurable_singleton_class α] (f : α → measure β) :
  transition_kernel mα mβ :=
{ val := f,
  property := measurable_of_countable f }

lemma aux (κ : transition_kernel mα mβ) {s : set β} {t : set (α × β)} (hs : measurable_set s)
  (ht : measurable_set t) (hκs : ∀ a, κ a s ≠ ∞) :
  measurable (λ a, κ a (s ∩ {b | (a, b) ∈ t})) :=
begin
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ ht,
  { simp only [set.mem_empty_iff_false, set.set_of_false, set.inter_empty, measure_empty,
      measurable_const], },
  { intros t' ht',
    simp only [set.mem_image2, set.mem_set_of_eq, exists_and_distrib_left] at ht',
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht',
    simp only [set.prod_mk_mem_set_prod_eq],
    classical,
    have h_eq_ite : ∀ a, s ∩ {b : β | a ∈ t₁ ∧ b ∈ t₂} = ite (a ∈ t₁) (s ∩ t₂) ∅,
    { intros a,
      ext1 b,
      split_ifs; simp [h], },
    simp_rw h_eq_ite,
    have : (λ a, (κ a) (ite (a ∈ t₁) (s ∩ t₂) ∅)) = (λ a, ite (a ∈ t₁) (κ a (s ∩ t₂)) 0),
    { ext1 a,
      split_ifs,
      { refl, },
      { exact measure_empty, }, },
    rw this,
    exact measurable.ite ht₁ (transition_kernel.measurable_coe κ (hs.inter ht₂)) measurable_const },
  { intros t' ht' h_meas,
    have h_eq_sdiff : ∀ a, s ∩ {b : β | (a, b) ∈ t'ᶜ} = s \ {b : β | (a, b) ∈ t'},
    { intro a,
      ext1 b,
      simp only [set.mem_compl_iff, set.mem_inter_iff, set.mem_set_of_eq, set.mem_diff], },
    simp_rw h_eq_sdiff,
    have : (λ a, κ a (s \ {b : β | (a, b) ∈ t'}))
      = (λ a, (κ a s - κ a (s ∩ {b : β | (a, b) ∈ t'}))),
    { ext1 a,
      rw [← set.diff_inter_self_eq_diff, measure_diff],
      { rw set.inter_comm, },
      { exact set.inter_subset_right _ _, },
      { exact ((@measurable_prod_mk_left α β mα mβ a) t' ht').inter hs, },
      { exact (lt_of_le_of_lt (measure_mono (set.inter_subset_right _ _)) (hκs a).lt_top).ne, }, },
    rw this,
    exact measurable.sub (transition_kernel.measurable_coe κ hs) h_meas, },
  { intros f h_disj hf_meas hf,
    have h_Union : (λ a, κ a (s ∩ {b : β | (a, b) ∈ ⋃ i, f i}))
      = (λ a, κ a (⋃ i, s ∩ {b : β | (a, b) ∈ f i})),
    { ext1 a,
      congr' with b,
      simp only [set.mem_Union, set.mem_inter_iff, set.mem_set_of_eq, exists_and_distrib_left], },
    rw h_Union,
    have h_tsum : (λ a, κ a (⋃ i, s ∩ {b : β | (a, b) ∈ f i}))
      = (λ a, ∑' i, κ a (s ∩ {b : β | (a, b) ∈ f i})),
    { ext1 a,
      rw measure_Union,
      { intros i j hij b hb,
        simp only [set.inf_eq_inter, set.mem_inter_iff, set.mem_set_of_eq] at hb,
        specialize h_disj i j hij ⟨hb.1.2, hb.2.2⟩,
        simpa using h_disj, },
      { exact λ i, hs.inter ((@measurable_prod_mk_left α β mα mβ a) _ (hf_meas i)), }, },
    rw h_tsum,
    exact measurable.ennreal_tsum hf, },
end

lemma aux' (κ : transition_kernel mα mβ) {t : set (α × β)}
  (ht : measurable_set t) (hκs : ∀ a, is_finite_measure (κ a)) :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
by { convert aux κ measurable_set.univ ht (λ a, measure_ne_top _ _), ext1 a, rw set.univ_inter, }

lemma lintegral_indicator' {mβ : measurable_space β} {f : α → β} {s : set β}
  (hf : measurable f) (hs : measurable_set s) (c : ℝ≥0∞) :
  ∫⁻ a, s.indicator (λ _, c) (f a) ∂μα = c * μα (f ⁻¹' s) :=
begin
  rw ← lintegral_add_compl _ (hf hs),
  rw ← add_zero (c * μα (f ⁻¹' s)),
  classical,
  simp_rw [set.indicator_apply],
  congr,
  { have h_eq_1 : ∀ x ∈ f ⁻¹' s, ite (f x ∈ s) c 0 = c := λ _ hx, if_pos hx,
    rw set_lintegral_congr_fun (hf hs) (filter.eventually_of_forall h_eq_1),
    simp only,
    rw [lintegral_const, measure.restrict_apply measurable_set.univ, set.univ_inter], },
  { have h_eq_zero : ∀ x ∈ (f ⁻¹' s)ᶜ, ite (f x ∈ s) c 0 = 0,
      from λ _ hx, if_neg hx,
    rw set_lintegral_congr_fun (hf hs).compl (filter.eventually_of_forall h_eq_zero),
    simp only [lintegral_const, zero_mul], },
end

lemma measurable_set_lintegral (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f a b ∂κ a) :=
begin
  have h := simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw ← h,
  have : ∀ a, ∫⁻ b in s, (⨆ n, (simple_func.eapprox (function.uncurry f) n) (a, b)) ∂κ a
    = ⨆ n, ∫⁻ b in s, (simple_func.eapprox (function.uncurry f) n) (a, b) ∂κ a,
  { intro a,
    rw lintegral_supr,
    { exact λ n, (simple_func.eapprox (function.uncurry f) n).measurable.comp
        measurable_prod_mk_left, },
    { intros i j hij b,
      have h_mono := simple_func.monotone_eapprox (function.uncurry f) hij,
      rw ← simple_func.coe_le at h_mono,
      exact h_mono _, }, },
  simp_rw this,
  refine measurable_supr (λ n, _),
  refine simple_func.induction _ _ (simple_func.eapprox (function.uncurry f) n),
  { intros c t ht,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator],
    have : (λ a, ∫⁻ b in s, t.indicator (function.const (α × β) c) (a, b) ∂κ a)
      = (λ a, c * κ a (s ∩ {b | (a, b) ∈ t})),
    { ext1 a,
      rw lintegral_indicator' measurable_prod_mk_left ht,
      rw measure.restrict_apply,
      { rw set.inter_comm,
        refl, },
      { exact measurable_prod_mk_left ht, }, },
    rw this,
    refine measurable.const_mul _ c,
    exact aux _ hs ht (λ a, measure_ne_top (κ a) s), },
  { intros g₁ g₂ h_disj hm₁ hm₂,
    simp only [simple_func.coe_add, pi.add_apply],
    have h_add : (λ a, ∫⁻ b in s, g₁ (a, b) + g₂ (a, b) ∂κ a)
      = (λ a, ∫⁻ b in s, g₁ (a, b) ∂κ a) + (λ a, ∫⁻ b in s, g₂ (a, b) ∂κ a),
    { ext1 a,
      rw [pi.add_apply, lintegral_add_left],
      exact g₁.measurable.comp measurable_prod_mk_left, },
    rw h_add,
    exact measurable.add hm₁ hm₂, },
end

lemma measurable_lintegral (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  measurable (λ a, ∫⁻ b, f a b ∂κ a) :=
begin
  convert measurable_set_lintegral κ hκ f hf measurable_set.univ,
  simp only [measure.restrict_univ],
end

noncomputable
def of_density (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  transition_kernel mα mβ :=
{ val := λ a, (κ a).with_density (f a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, (κ a).with_density (f a) s) = (λ a, ∫⁻ b in s, f a b ∂κ a),
    { ext1 a, exact with_density_apply (f a) hs, },
    rw this,
    exact measurable_set_lintegral κ hκ f hf hs,
  end, }

noncomputable
def comp_fun (κ : transition_kernel mα mβ) (η : transition_kernel (mα.prod mβ) mγ) (a : α)
  (s : set (β × γ)) :
  ℝ≥0∞ :=
∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a

lemma comp_fun_empty (κ : transition_kernel mα mβ) (η : transition_kernel (mα.prod mβ) mγ) (a : α) :
  comp_fun κ η a ∅ = 0 :=
by simp only [comp_fun, set.mem_empty_iff_false, set.set_of_false, measure_empty, lintegral_const,
  zero_mul]

lemma comp_fun_Union (κ : transition_kernel mα mβ) (η : transition_kernel (mα.prod mβ) mγ)
  (hη : ∀ ab, is_finite_measure (η ab)) (a : α)
  (f : ℕ → set (β × γ)) (hf_meas : ∀ i, measurable_set (f i)) (hf_disj : pairwise (disjoint on f)) :
  comp_fun κ η a (⋃ i, f i) = ∑' i, comp_fun κ η a (f i) :=
begin
  have h_Union : (λ b, η (a, b) {c : γ | (b, c) ∈ ⋃ i, f i})
    = λ b, η (a,b) (⋃ i, {c : γ | (b, c) ∈ f i}),
  { ext b,
    congr' with c,
    simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
    refl, },
  rw [comp_fun, h_Union],
  have h_tsum : (λ b, η (a, b) (⋃ i, {c : γ | (b, c) ∈ f i}))
    = λ b, ∑' i, η (a, b) {c : γ | (b, c) ∈ f i},
  { ext1 b,
    rw measure_Union,
    { intros i j hij c hc,
      simp only [set.inf_eq_inter, set.mem_inter_iff, set.mem_set_of_eq] at hc,
      specialize hf_disj i j hij hc,
      simpa using hf_disj, },
    { exact λ i, (@measurable_prod_mk_left β γ mβ mγ b) _ (hf_meas i), }, },
  rw [h_tsum, lintegral_tsum],
  { refl, },
  intros i,
  have hm : measurable_set {p : (α × β) × γ | (p.1.2, p.2) ∈ f i},
    from (measurable_fst.snd.prod_mk measurable_snd) (hf_meas i),
  exact (aux' η hm hη).comp measurable_prod_mk_left,
end

noncomputable
def comp (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (η : transition_kernel (mα.prod mβ) mγ) (hη : ∀ ab, is_finite_measure (η ab)) :
  transition_kernel mα (mβ.prod mγ) :=
{ val := λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η hη a),
  property :=
    begin
      refine measure.measurable_of_measurable_coe _ (λ s hs, _),
      have : (λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
          (comp_fun_Union κ η hη a) s) = λ a, comp_fun κ η a s,
      { ext1 a, rwa measure.of_measurable_apply, },
      rw this,
      simp only [comp_fun],
      have h_meas : measurable (function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})),
      { have : function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})
          = λ p, η p {c : γ | (p.2, c) ∈ s},
        { ext1 p,
          have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
          rw [hp_eq_mk, function.uncurry_apply_pair], },
        rw this,
        exact aux' η ((measurable_fst.snd.prod_mk measurable_snd) hs) hη, },
      exact measurable_lintegral κ hκ (λ a b, η (a, b) {c : γ | (b, c) ∈ s}) h_meas,
    end, }

lemma comp_apply (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (η : transition_kernel (mα.prod mβ) mγ) (hη : ∀ ab, is_finite_measure (η ab)) (a : α)
  {s : set (β × γ)} (hs : measurable_set s) :
  comp κ hκ η hη a s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a :=
begin
  rw [comp],
  change measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η hη a) s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a,
  rw measure.of_measurable_apply _ hs,
  refl,
end

noncomputable
def map (κ : transition_kernel mα mβ) (f : β → γ) (hf : measurable f) :
  transition_kernel mα mγ :=
{ val := λ a, (κ a).map f,
  property := (measure.measurable_map _ hf).comp (transition_kernel.measurable κ) }

lemma map_apply {mγ : measurable_space γ} (κ : transition_kernel mα mβ) {f : β → γ}
  (hf : measurable f) (a : α) {s : set γ} (hs : measurable_set s) :
  map κ f hf a s = κ a (f ⁻¹' s) :=
begin
  rw [map],
  change (κ a).map f s = κ a (f ⁻¹' s),
  exact measure.map_apply hf hs,
end

def comap (κ : transition_kernel mα mβ) (f : γ → α) (hf : measurable f) :
  transition_kernel mγ mβ :=
{ val := λ a, κ (f a),
  property := (transition_kernel.measurable κ).comp hf }

lemma comap_apply {mγ : measurable_space γ} (κ : transition_kernel mα mβ) {f : γ → α}
  (hf : measurable f) (c : γ) {s : set β} (hs : measurable_set s) :
  comap κ f hf c s = κ (f c) s :=
rfl

def todo_name (κ : transition_kernel mα mβ) (mγ : measurable_space γ) :
  transition_kernel (mγ.prod mα) mβ :=
comap κ (λ a, a.2) measurable_snd

lemma todo_name_apply (κ : transition_kernel mα mβ) (mγ : measurable_space γ) (ca : γ × α)
  {s : set β} (hs : measurable_set s) :
  todo_name κ mγ ca s = (κ ca.snd) s :=
by rw [todo_name, comap_apply _ _ _ hs]

noncomputable
def todo_name2 (κ : transition_kernel mα (mβ.prod mγ)) : transition_kernel mα mγ :=
map κ (λ p, p.2) measurable_snd

lemma todo_name2_apply (κ : transition_kernel mα (mβ.prod mγ)) (a : α) {s : set γ}
  (hs : measurable_set s) :
  todo_name2 κ a s = κ a {p | p.2 ∈ s} :=
by { rw [todo_name2, map_apply _ _ _ hs], refl, }

lemma is_finite_measure_todo_name (κ : transition_kernel mα mβ) (mγ : measurable_space γ)
  (hκ : ∀ a, is_finite_measure (κ a)) (ca : γ × α) :
  is_finite_measure (todo_name κ mγ ca) :=
begin
  rw [todo_name],
  sorry,
end

noncomputable
def comp2 (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (η : transition_kernel mβ mγ) (hη : ∀ b, is_finite_measure (η b)) :
  transition_kernel mα mγ :=
todo_name2 (comp κ hκ (todo_name η mα) (λ ab, is_finite_measure_todo_name _ _ hη _))

lemma comp2_apply (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (η : transition_kernel mβ mγ) (hη : ∀ b, is_finite_measure (η b)) (a : α) {s : set γ}
  (hs : measurable_set s) :
  comp2 κ hκ η hη a s = ∫⁻ b, η b s ∂κ a :=
begin
  rw [comp2, todo_name2_apply _ _ hs, comp_apply],
  swap, { exact measurable_snd hs, },
  simp only [set.mem_set_of_eq, set.set_of_mem_eq],
  simp_rw todo_name_apply _ _ _ hs,
end

lemma comp2_deterministic_eq_map {mγ : measurable_space γ}
  (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  {f : β → γ} (hf : measurable f) :
  comp2 κ hκ (deterministic hf) (λ b, is_finite_measure_deterministic hf b) = map κ f hf :=
begin
  ext a s hs,
  simp_rw [map_apply _ _ _ hs, comp2_apply _ _ _ _ _ hs, deterministic_apply hf _ hs,
    lintegral_indicator' hf hs, one_mul],
end

end transition_kernel

section real

def reg_cond_distribution (mα : measurable_space α) (Y : α → ℝ) :
  transition_kernel mα (borel ℝ) :=
sorry

end real

end measure_theory
