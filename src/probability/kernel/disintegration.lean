/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.cond_cdf
import measure_theory.constructions.polish

/-!
# Disintegration of measures on product spaces

Let `ρ` be a finite measure on `α × Ω`, where `Ω` is a standard Borel space. In mathlib terms, `Ω`
verifies `[topological_space Ω] [polish_space Ω] [measurable_space Ω] [borel_space Ω]`.

For any measurable space `γ`, there exists a kernel `cond_kernel ρ : kernel α Ω` such that we
have a disintegration of the constant kernel from `γ` with value `ρ`:
`kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) γ)`,
where `ρ.fst` is the marginal measure of `ρ` on `α`. In particular,
`ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) unit)) ()`.

In order to obtain a disintegration for any standard Borel space, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`. In the real case,
we define a conditional kernel for each `a : α` by taking the measure associated to the Stieltjes
function `cond_cdf ρ a` (the conditional cumulative distribution function) and we show that this
defines a measurable map.

## Main definitions

* `probability_theory.cond_kernel ρ : kernel α Ω`: conditional kernel described above.

## Main statements

* `probability_theory.kernel.const_eq_comp_prod`:
  `kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) γ)`
* `probability_theory.measure_eq_comp_prod`:
  `ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) unit)) ()`
* `probability_theory.lintegral_cond_kernel`:
  `∫⁻ a, ∫⁻ ω, f (a, ω) ∂(cond_kernel ρ a) ∂ρ.fst = ∫⁻ x, f x ∂ρ`

## TODO

* The finite measure hypothesis can be weakened to σ-finite. The proof uses the finite case.
* Beyond measures, we can find a disintegration for a kernel `α → Ω × Ω'` by applying the
  construction used here for all `a : α` and showing additional measurability properties of the map
  we obtain.

-/

section todo_move
namespace measure_theory

lemma measurable_embedding.prod_mk {α β γ δ : Type*} {mα : measurable_space α}
  {mβ : measurable_space β} {mγ : measurable_space γ} {mδ : measurable_space δ}
  {f : α → β} {g : γ → δ} (hg : measurable_embedding g) (hf : measurable_embedding f) :
  measurable_embedding (λ x : γ × α, (g x.1, f x.2)) :=
begin
  have h_inj : function.injective (λ x : γ × α, (g x.fst, f x.snd)),
  { intros x y hxy,
    rw [← @prod.mk.eta _ _ x, ← @prod.mk.eta _ _ y],
    simp only [prod.mk.inj_iff] at hxy ⊢,
    exact ⟨hg.injective hxy.1, hf.injective hxy.2⟩, },
  refine ⟨h_inj, _, _⟩,
  { exact (hg.measurable.comp measurable_fst).prod_mk (hf.measurable.comp measurable_snd), },
  { refine λ s hs, @measurable_space.induction_on_inter _
      (λ s, measurable_set ((λ (x : γ × α), (g x.fst, f x.snd)) '' s)) _ _ generate_from_prod.symm
      is_pi_system_prod _ _ _ _ _ hs,
    { simp only [set.image_empty, measurable_set.empty], },
    { rintros t ⟨t₁, t₂, ht₁, ht₂, rfl⟩,
      rw ← set.prod_image_image_eq,
      exact (hg.measurable_set_image.mpr ht₁).prod (hf.measurable_set_image.mpr ht₂), },
    { intros t ht ht_m,
      rw [← set.range_diff_image h_inj, ← set.prod_range_range_eq],
      exact measurable_set.diff
        (measurable_set.prod hg.measurable_set_range hf.measurable_set_range) ht_m, },
    { intros g hg_disj hg_meas hg,
      simp_rw set.image_Union,
      exact measurable_set.Union hg, }, },
end

end measure_theory
end todo_move

open measure_theory set filter

open_locale ennreal measure_theory topology probability_theory

namespace probability_theory

variables {α : Type*} {mα : measurable_space α}

include mα

section real

/-! ### Disintegration of measures on `α × ℝ` -/

lemma measure_cond_cdf_Iic (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  (cond_cdf ρ a).measure (Iic x) = ennreal.of_real (cond_cdf ρ a x) :=
begin
  rw [← sub_zero (cond_cdf ρ a x)],
  exact (cond_cdf ρ a).measure_Iic (tendsto_cond_cdf_at_bot ρ a) _,
end

lemma measure_cond_cdf_univ (ρ : measure (α × ℝ)) (a : α) :
  (cond_cdf ρ a).measure univ = 1 :=
begin
  rw [← ennreal.of_real_one, ← sub_zero (1 : ℝ)],
  exact stieltjes_function.measure_univ _ (tendsto_cond_cdf_at_bot ρ a)
    (tendsto_cond_cdf_at_top ρ a),
end

instance (ρ : measure (α × ℝ)) (a : α) : is_probability_measure ((cond_cdf ρ a).measure) :=
⟨measure_cond_cdf_univ ρ a⟩

/-- The function `a ↦ (cond_cdf ρ a).measure` is measurable. This allows us to build a kernel from
these measures. -/
lemma measurable_measure_cond_cdf (ρ : measure (α × ℝ)) :
  measurable (λ a, (cond_cdf ρ a).measure) :=
begin
  rw measure.measurable_measure,
  refine λ s hs, measurable_space.induction_on_inter
    real.borel_eq_generate_from_Iic real.is_pi_system_Iic _ _ _ _ hs,
  { simp only [measure_empty, measurable_const], },
  { rintros S ⟨u, rfl⟩,
    simp_rw measure_cond_cdf_Iic ρ _ u,
    exact (measurable_cond_cdf ρ u).ennreal_of_real, },
  { intros t ht ht_cd_meas,
    have : (λ a, (cond_cdf ρ a).measure tᶜ)
      = (λ a, (cond_cdf ρ a).measure univ) - (λ a, (cond_cdf ρ a).measure t),
    { ext1 a,
      rw [measure_compl ht (measure_ne_top (cond_cdf ρ a).measure _), pi.sub_apply], },
    simp_rw [this, measure_cond_cdf_univ ρ],
    exact measurable.sub measurable_const ht_cd_meas, },
  { intros f hf_disj hf_meas hf_cd_meas,
    simp_rw measure_Union hf_disj hf_meas,
    exact measurable.ennreal_tsum hf_cd_meas, },
end

/-- Conditional measure on the second space of the product given the value on the first, as a
kernel. -/
noncomputable
def cond_kernel_real (ρ : measure (α × ℝ)) : kernel α ℝ :=
{ val := λ a, (cond_cdf ρ a).measure,
  property := measurable_measure_cond_cdf ρ }

instance (ρ : measure (α × ℝ)) : is_markov_kernel (cond_kernel_real ρ) :=
⟨λ a, by { rw cond_kernel_real, apply_instance, } ⟩

lemma cond_kernel_real_Iic (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  cond_kernel_real ρ a (Iic x) = ennreal.of_real (cond_cdf ρ a x) :=
measure_cond_cdf_Iic ρ a x

lemma set_lintegral_cond_kernel_real_Iic (ρ : measure (α × ℝ)) [is_finite_measure ρ] (x : ℝ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, cond_kernel_real ρ a (Iic x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
by { simp_rw [cond_kernel_real_Iic], exact set_lintegral_cond_cdf ρ x hs, }

lemma set_lintegral_cond_kernel_real_univ (ρ : measure (α × ℝ))
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, cond_kernel_real ρ a univ ∂ρ.fst = ρ (s ×ˢ univ) :=
by simp only [measure_univ, lintegral_const, measure.restrict_apply, measurable_set.univ,
  univ_inter, one_mul, measure.fst_apply hs, ← prod_univ]

lemma lintegral_cond_kernel_real_univ (ρ : measure (α × ℝ)) :
  ∫⁻ a, cond_kernel_real ρ a univ ∂ρ.fst = ρ univ :=
by rw [← set_lintegral_univ, set_lintegral_cond_kernel_real_univ ρ measurable_set.univ,
  univ_prod_univ]

lemma set_lintegral_cond_kernel_real_prod (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) {t : set ℝ} (ht : measurable_set t) :
  ∫⁻ a in s, cond_kernel_real ρ a t ∂ρ.fst = ρ (s ×ˢ t) :=
begin
  -- `set_lintegral_cond_kernel_real_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generate the borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  refine measurable_space.induction_on_inter real.borel_eq_generate_from_Iic
    real.is_pi_system_Iic _ _ _ _ ht,
  { simp only [measure_empty, lintegral_const, zero_mul, prod_empty], },
  { rintros t ⟨q, rfl⟩,
    exact set_lintegral_cond_kernel_real_Iic ρ q hs, },
  { intros t ht ht_lintegral,
    calc ∫⁻ a in s, cond_kernel_real ρ a tᶜ ∂ρ.fst
        = ∫⁻ a in s, (cond_kernel_real ρ a univ) - cond_kernel_real ρ a t ∂ρ.fst :
      by { congr' with a, rw measure_compl ht (measure_ne_top (cond_kernel_real ρ a) _), }
    ... = ∫⁻ a in s, (cond_kernel_real ρ a univ) ∂ρ.fst - ∫⁻ a in s, cond_kernel_real ρ a t ∂ρ.fst :
      begin
        rw lintegral_sub (kernel.measurable_coe (cond_kernel_real ρ) ht),
        { rw ht_lintegral,
          exact measure_ne_top ρ _, },
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
      end
    ... = ρ (s ×ˢ univ) - ρ (s ×ˢ t) :
      by rw [set_lintegral_cond_kernel_real_univ ρ hs, ht_lintegral]
    ... = ρ (s ×ˢ tᶜ) :
      begin
        rw ← measure_diff _ (hs.prod ht) (measure_ne_top ρ _),
        { rw [prod_diff_prod, compl_eq_univ_diff],
          simp only [diff_self, empty_prod, union_empty], },
        { rw prod_subset_prod_iff,
          exact or.inl ⟨subset_rfl, subset_univ t⟩, },
      end, },
  { intros f hf_disj hf_meas hf_eq,
    simp_rw measure_Union hf_disj hf_meas,
    rw [lintegral_tsum (λ i, (kernel.measurable_coe _ (hf_meas i)).ae_measurable.restrict),
      prod_Union, measure_Union],
    { simp_rw hf_eq, },
    { intros i j hij,
      rw [function.on_fun, disjoint_prod],
      exact or.inr (hf_disj hij), },
    { exact λ i, measurable_set.prod hs (hf_meas i), }, },
end

lemma lintegral_cond_kernel_real_mem (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set (α × ℝ)} (hs : measurable_set s) :
  ∫⁻ a, cond_kernel_real ρ a {x | (a, x) ∈ s} ∂ρ.fst = ρ s :=
begin
  -- `set_lintegral_cond_kernel_real_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generate the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp only [mem_empty_iff_false, set_of_false, measure_empty, lintegral_const, zero_mul], },
  { intros t ht,
    rw mem_image2 at ht,
    obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := ht,
    have h_prod_eq_snd : ∀ a ∈ t₁, {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = t₂,
    { intros a ha,
      simp only [ha, prod_mk_mem_set_prod_eq, true_and, set_of_mem_eq], },
    cases eq_empty_or_nonempty t₂ with h h,
    { simp only [h, prod_empty, mem_empty_iff_false, set_of_false, measure_empty, lintegral_const,
        zero_mul], },
    rw ← lintegral_add_compl _ ht₁,
    have h_eq1 : ∫⁻ a in t₁, cond_kernel_real ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst
      = ∫⁻ a in t₁, cond_kernel_real ρ a t₂ ∂ρ.fst,
    { refine set_lintegral_congr_fun ht₁ (eventually_of_forall (λ a ha, _)),
      rw h_prod_eq_snd a ha, },
    have h_eq2 : ∫⁻ a in t₁ᶜ, cond_kernel_real ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst = 0,
    { suffices h_eq_zero : ∀ a ∈ t₁ᶜ, cond_kernel_real ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = 0,
      { rw set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero),
        simp only [lintegral_const, zero_mul], },
      intros a hat₁,
      rw mem_compl_iff at hat₁,
      simp only [hat₁, prod_mk_mem_set_prod_eq, false_and, set_of_false, measure_empty], },
    rw [h_eq1, h_eq2, add_zero],
    exact set_lintegral_cond_kernel_real_prod ρ ht₁ ht₂, },
  { intros t ht ht_eq,
    calc ∫⁻ a, cond_kernel_real ρ a {x : ℝ | (a, x) ∈ tᶜ} ∂ρ.fst
        = ∫⁻ a, cond_kernel_real ρ a {x : ℝ | (a, x) ∈ t}ᶜ ∂ρ.fst : rfl
    ... = ∫⁻ a, cond_kernel_real ρ a univ - cond_kernel_real ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst :
      begin
        congr' with a : 1,
        exact measure_compl (measurable_prod_mk_left ht) (measure_ne_top (cond_kernel_real ρ a) _),
      end
    ... = ∫⁻ a, cond_kernel_real ρ a univ ∂ρ.fst
          - ∫⁻ a, cond_kernel_real ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst :
      begin
        have h_le : (λ a, cond_kernel_real ρ a {x : ℝ | (a, x) ∈ t})
          ≤ᵐ[ρ.fst] λ a, cond_kernel_real ρ a univ,
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
        rw lintegral_sub (kernel.measurable_prod_mk_mem _ ht) _ h_le,
        refine ((lintegral_mono_ae h_le).trans_lt _).ne,
        rw lintegral_cond_kernel_real_univ,
        exact measure_lt_top ρ univ,
      end
    ... = ρ univ - ρ t : by rw [ht_eq, lintegral_cond_kernel_real_univ]
    ... = ρ tᶜ : (measure_compl ht (measure_ne_top _ _)).symm, },
  { intros f hf_disj hf_meas hf_eq,
    have h_eq : ∀ a, {x | (a, x) ∈ ⋃ i, f i} = ⋃ i, {x | (a, x) ∈ f i},
    { intros a,
      ext1 x,
      simp only [mem_Union, mem_set_of_eq], },
    simp_rw h_eq,
    have h_disj : ∀ a, pairwise (disjoint on (λ i, {x | (a, x) ∈ f i})),
    { intros a i j hij,
      have h_disj := hf_disj hij,
      rw [function.on_fun, disjoint_iff_inter_eq_empty] at h_disj ⊢,
      ext1 x,
      simp only [mem_inter_iff, mem_set_of_eq, mem_empty_iff_false, iff_false],
      intros h_mem_both,
      suffices : (a, x) ∈ ∅, by rwa mem_empty_iff_false at this,
      rwa [← h_disj, mem_inter_iff], },
    calc ∫⁻ a, cond_kernel_real ρ a (⋃ i, {x | (a, x) ∈ f i}) ∂ρ.fst
        = ∫⁻ a, ∑' i, cond_kernel_real ρ a {x | (a, x) ∈ f i} ∂ρ.fst :
          by { congr' with a : 1,
            rw measure_Union (h_disj a) (λ i, measurable_prod_mk_left (hf_meas i)), }
    ... = ∑' i, ∫⁻ a, cond_kernel_real ρ a {x | (a, x) ∈ f i} ∂ρ.fst : lintegral_tsum
          (λ i, (kernel.measurable_prod_mk_mem (cond_kernel_real ρ) (hf_meas i)).ae_measurable)
    ... = ∑' i, ρ (f i) : by simp_rw hf_eq
    ... = ρ (Union f) : (measure_Union hf_disj hf_meas).symm, },
end

theorem kernel.const_eq_comp_prod_real (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  (γ : Type*) [measurable_space γ] :
  kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left γ (cond_kernel_real ρ)) :=
begin
  ext a s hs : 2,
  rw [kernel.comp_prod_apply _ _ _ hs, kernel.const_apply, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
  rw lintegral_cond_kernel_real_mem ρ hs,
end

theorem measure_eq_comp_prod_real (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit (cond_kernel_real ρ))) () :=
by rw [← kernel.const_eq_comp_prod_real ρ unit, kernel.const_apply]

lemma lintegral_cond_kernel_real (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {f : α × ℝ → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, ∫⁻ y, f (a, y) ∂(cond_kernel_real ρ a) ∂ρ.fst = ∫⁻ x, f x ∂ρ :=
begin
  nth_rewrite 1 measure_eq_comp_prod_real ρ,
  rw [kernel.lintegral_comp_prod _ _ _ hf, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
end

lemma ae_cond_kernel_real_eq_one (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set ℝ} (hs : measurable_set s) (hρ : ρ {x | x.snd ∈ sᶜ} = 0) :
  ∀ᵐ a ∂ρ.fst, cond_kernel_real ρ a s = 1 :=
begin
  have h : ρ {x | x.snd ∈ sᶜ}
    = (kernel.const unit ρ.fst ⊗ₖ kernel.prod_mk_left unit (cond_kernel_real ρ)) ()
      {x | x.snd ∈ sᶜ},
  { rw ← measure_eq_comp_prod_real, },
  rw [hρ, kernel.comp_prod_apply] at h,
  swap, { exact measurable_snd hs.compl, },
  rw [eq_comm, lintegral_eq_zero_iff] at h,
  swap,
  { simp_rw kernel.prod_mk_left_apply',
    simp only [mem_compl_iff, mem_set_of_eq],
    exact kernel.measurable_coe _ hs.compl, },
  rw kernel.const_apply at h,
  simp only [mem_compl_iff, mem_set_of_eq, kernel.prod_mk_left_apply'] at h,
  filter_upwards [h] with a ha,
  change cond_kernel_real ρ a sᶜ = 0 at ha,
  rwa [prob_compl_eq_zero_iff hs] at ha,
  apply_instance,
end

end real

section polish

/-! ### Disintegration of measures on Polish Borel spaces

Since every standard Borel space embeds measurably into `ℝ`, we can generalize the disintegration
property on `ℝ` to all these spaces. -/

variables {Ω : Type*} [topological_space Ω] [polish_space Ω] [measurable_space Ω] [borel_space Ω]

/-- Existence of a conditional kernel. Use the definition `cond_kernel` to get that kernel. -/
lemma exists_cond_kernel [nonempty Ω] (ρ : measure (α × Ω)) [is_finite_measure ρ] (γ : Type*)
  [measurable_space γ] :
  ∃ (η : kernel α Ω) (h : is_markov_kernel η),
  kernel.const γ ρ
    = @kernel.comp_prod γ α _ _ Ω _ (kernel.const γ ρ.fst) _ (kernel.prod_mk_left γ η)
      (by { haveI := h, apply_instance, }) :=
begin
  obtain ⟨f, hf⟩ := exists_measurable_embedding_real Ω,
  let ρ' : measure (α × ℝ) := ρ.map (prod.map id f),
  -- The general idea is to define `η = kernel.comap_right (cond_kernel_real ρ') hf`. There is
  -- however an issue: that `η` may not be a Markov kernel since its value is only a
  -- probability distribution almost everywhere with respect to `ρ.fst`, not everywhere.
  -- We modify it to obtain a Markov kernel which is almost everywhere equal.
  let ρ_set := (to_measurable ρ.fst {a | cond_kernel_real ρ' a (range f) = 1}ᶜ)ᶜ,
  have hm : measurable_set ρ_set := (measurable_set_to_measurable _ _).compl,
  have h_eq_one_of_mem : ∀ a ∈ ρ_set, cond_kernel_real ρ' a (range f) = 1,
  { intros a ha,
    rw [mem_compl_iff] at ha,
    have h_ss := subset_to_measurable ρ.fst {a : α | cond_kernel_real ρ' a (range f) = 1}ᶜ,
    suffices ha' : a ∉ {a : α | cond_kernel_real ρ' a (range f) = 1}ᶜ,
    { rwa not_mem_compl_iff at ha', },
    exact not_mem_subset h_ss ha, },
  have h_prod_embed : measurable_embedding (prod.map (id : α → α) f) :=
    (measurable_embedding.id).prod_mk hf,
  have h_fst : ρ'.fst = ρ.fst,
  { ext1 u hu,
    rw [measure.fst_apply hu, measure.fst_apply hu,
      measure.map_apply h_prod_embed.measurable (measurable_fst hu)],
    refl, },
  have h_ae : ∀ᵐ a ∂ρ.fst, a ∈ ρ_set,
  { rw ae_iff,
    simp only [not_mem_compl_iff, set_of_mem_eq, measure_to_measurable],
    change (ρ.fst) {a : α | a ∉ {a' : α | cond_kernel_real ρ' a' (range f) = 1}} = 0,
    rw [← ae_iff, ← h_fst],
    refine ae_cond_kernel_real_eq_one ρ' hf.measurable_set_range _,
    rw measure.map_apply h_prod_embed.measurable,
    swap, { exact measurable_snd hf.measurable_set_range.compl, },
    convert measure_empty,
    ext1 x,
    simp only [mem_compl_iff, mem_range, preimage_set_of_eq, prod_map, mem_set_of_eq,
      mem_empty_iff_false, iff_false, not_not, exists_apply_eq_apply], },
  classical,
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∈ range f := range_nonempty _,
  let η' := kernel.piecewise hm (cond_kernel_real ρ')
    (kernel.deterministic (λ _, x₀) measurable_const),
  -- We show that `kernel.comap_right η' hf` is a suitable Markov kernel.
  refine ⟨kernel.comap_right η' hf, _, _⟩,
  { refine kernel.is_markov_kernel.comap_right _ _ (λ a, _),
    rw kernel.piecewise_apply',
    split_ifs with h_mem h_not_mem,
    { exact h_eq_one_of_mem _ h_mem, },
    { rw [kernel.deterministic_apply' _ _ hf.measurable_set_range, set.indicator_apply,
        if_pos hx₀], }, },
  have : kernel.const γ ρ = kernel.comap_right (kernel.const γ ρ') h_prod_embed,
  { ext c t ht : 2,
    rw [kernel.const_apply, kernel.comap_right_apply' _ _ _ ht, kernel.const_apply,
      measure.map_apply h_prod_embed.measurable (h_prod_embed.measurable_set_image.mpr ht)],
    congr' with x : 1,
    rw ← @prod.mk.eta _ _ x,
    simp only [id.def, mem_preimage, prod.map_mk, mem_image, prod.mk.inj_iff, prod.exists],
    refine ⟨λ h, ⟨x.1, x.2, h, rfl, rfl⟩, _⟩,
    rintros ⟨a, b, h_mem, rfl, hf_eq⟩,
    rwa hf.injective hf_eq at h_mem, },
  rw [this, kernel.const_eq_comp_prod_real ρ'],
  ext c t ht : 2,
  rw [kernel.comap_right_apply' _ _ _ ht,
    kernel.comp_prod_apply _ _ _ (h_prod_embed.measurable_set_image.mpr ht), kernel.const_apply,
    h_fst, kernel.comp_prod_apply _ _ _ ht, kernel.const_apply],
  refine lintegral_congr_ae _,
  filter_upwards [h_ae] with a ha,
  rw [kernel.prod_mk_left_apply', kernel.prod_mk_left_apply', kernel.comap_right_apply'],
  swap, { exact measurable_prod_mk_left ht, },
  have h1 : {c : ℝ | (a, c) ∈ prod.map id f '' t} = f '' {c : Ω | (a, c) ∈ t},
  { ext1 x,
    simp only [prod_map, id.def, mem_image, prod.mk.inj_iff, prod.exists, mem_set_of_eq],
    split,
    { rintros ⟨a', b, h_mem, rfl, hf_eq⟩,
      exact ⟨b, h_mem, hf_eq⟩, },
    { rintros ⟨b, h_mem, hf_eq⟩,
      exact ⟨a, b, h_mem, rfl, hf_eq⟩, }, },
  have h2 : cond_kernel_real ρ' (c, a).snd = η' (c, a).snd,
  { rw [kernel.piecewise_apply, if_pos ha], },
  rw [h1, h2],
end

variables [nonempty Ω]

/-- **Regular conditional probability distribution**, or conditional kernel: a Markov kernel such
that `ρ : measure (α × Ω) = (ρ.fst : measure α) ⊗ₖ (cond_kernel ρ : kernel α Ω)` (up to
augmentations of the spaces to make that expression valid: see `measure_eq_comp_prod`). -/
noncomputable
def cond_kernel (ρ : measure (α × Ω)) [is_finite_measure ρ] : kernel α Ω :=
(exists_cond_kernel ρ unit).some

instance (ρ : measure (α × Ω)) [is_finite_measure ρ] : is_markov_kernel (cond_kernel ρ) :=
(exists_cond_kernel ρ unit).some_spec.some

lemma kernel.const_unit_eq_comp_prod (ρ : measure (α × Ω)) [is_finite_measure ρ] :
  kernel.const unit ρ
    = (kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit (cond_kernel ρ)) :=
(exists_cond_kernel ρ unit).some_spec.some_spec

/-- **Disintegration** of finite product measures on `α × Ω`, where `Ω` is Polish Borel. Such a
measure can be written as the composition-product of the constant kernel with value `ρ.fst`
(marginal measure over `α`) and a Markov kernel from `α` to `Ω`. We call that Markov kernel
`cond_kernel ρ`. -/
theorem measure_eq_comp_prod (ρ : measure (α × Ω)) [is_finite_measure ρ] :
  ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit (cond_kernel ρ))) () :=
by rw [← kernel.const_unit_eq_comp_prod, kernel.const_apply]

/-- **Disintegration** of constant kernels. A constant kernel on a product space `α × Ω`, where `Ω`
is Polish Borel, can be written as the composition-product of the constant kernel with value `ρ.fst`
(marginal measure over `α`) and a Markov kernel from `α` to `Ω`. We call that Markov kernel
`cond_kernel ρ`. -/
theorem kernel.const_eq_comp_prod (ρ : measure (α × Ω)) [is_finite_measure ρ]
  (γ : Type*) [measurable_space γ] :
  kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left γ (cond_kernel ρ)) :=
begin
  ext a s hs : 2,
  simpa only [kernel.const_apply, kernel.comp_prod_apply _ _ _ hs, kernel.prod_mk_left_apply']
    using kernel.ext_iff'.mp (kernel.const_unit_eq_comp_prod ρ) () s hs,
end

lemma lintegral_cond_kernel (ρ : measure (α × Ω)) [is_finite_measure ρ]
  {f : α × Ω → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, ∫⁻ ω, f (a, ω) ∂(cond_kernel ρ a) ∂ρ.fst = ∫⁻ x, f x ∂ρ :=
begin
  conv_rhs { rw measure_eq_comp_prod ρ, },
  rw [kernel.lintegral_comp_prod _ _ _ hf, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
end

end polish

end probability_theory
