/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.cond_cdf
import measure_theory.constructions.polish
import probability.kernel.integral_comp_prod

/-!
# Disintegration of measures on product spaces

Let `ρ` be a finite measure on `α × Ω`, where `Ω` is a standard Borel space. In mathlib terms, `Ω`
verifies `[nonempty Ω] [topological_space Ω] [polish_space Ω] [measurable_space Ω] [borel_space Ω]`.
Then there exists a kernel `ρ.cond_kernel : kernel α Ω` such that for any measurable set
`s : set (α × Ω)`, `ρ s = ∫⁻ a, ρ.cond_kernel a {x | (a, x) ∈ s} ∂ρ.fst`.

In terms of kernels, `ρ.cond_kernel` is such that for any measurable space `γ`, we
have a disintegration of the constant kernel from `γ` with value `ρ`:
`kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left γ (cond_kernel ρ))`,
where `ρ.fst` is the marginal measure of `ρ` on `α`. In particular,
`ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit (cond_kernel ρ))) ()`.

In order to obtain a disintegration for any standard Borel space, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`. In the real case,
we define a conditional kernel by taking for each `a : α` the measure associated to the Stieltjes
function `cond_cdf ρ a` (the conditional cumulative distribution function).

## Main definitions

* `measure_theory.measure.cond_kernel ρ : kernel α Ω`: conditional kernel described above.

## Main statements

* `probability_theory.lintegral_cond_kernel`:
  `∫⁻ a, ∫⁻ ω, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫⁻ x, f x ∂ρ`
* `probability_theory.lintegral_cond_kernel_mem`:
  `∫⁻ a, ρ.cond_kernel a {x | (a, x) ∈ s} ∂ρ.fst = ρ s`
* `probability_theory.kernel.const_eq_comp_prod`:
  `kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left γ ρ.cond_kernel)`
* `probability_theory.measure_eq_comp_prod`:
  `ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit ρ.cond_kernel)) ()`

-/

open measure_theory set filter

open_locale ennreal measure_theory topology probability_theory

namespace probability_theory

variables {α : Type*} {mα : measurable_space α}

include mα

section real

/-! ### Disintegration of measures on `α × ℝ` -/

/-- Conditional measure on the second space of the product given the value on the first, as a
kernel. Use the more general `cond_kernel`. -/
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

variables (ρ : measure (α × ℝ)) [is_finite_measure ρ]

lemma set_lintegral_cond_kernel_real_prod
  {s : set α} (hs : measurable_set s) {t : set ℝ} (ht : measurable_set t) :
  ∫⁻ a in s, cond_kernel_real ρ a t ∂ρ.fst = ρ (s ×ˢ t) :=
begin
  -- `set_lintegral_cond_kernel_real_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generate the borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  refine measurable_space.induction_on_inter (borel_eq_generate_from_Iic ℝ)
    is_pi_system_Iic _ _ _ _ ht,
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

lemma lintegral_cond_kernel_real_mem {s : set (α × ℝ)} (hs : measurable_set s) :
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
        rw lintegral_sub _ _ h_le,
        { exact kernel.measurable_kernel_prod_mk_left ht, },
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
          (λ i, (kernel.measurable_kernel_prod_mk_left (hf_meas i)).ae_measurable)
    ... = ∑' i, ρ (f i) : by simp_rw hf_eq
    ... = ρ (Union f) : (measure_Union hf_disj hf_meas).symm, },
end

theorem kernel.const_eq_comp_prod_real (γ : Type*) [measurable_space γ]
  (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left γ (cond_kernel_real ρ)) :=
begin
  ext a s hs : 2,
  rw [kernel.comp_prod_apply _ _ _ hs, kernel.const_apply, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
  rw lintegral_cond_kernel_real_mem ρ hs,
end

theorem measure_eq_comp_prod_real :
  ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit (cond_kernel_real ρ))) () :=
by rw [← kernel.const_eq_comp_prod_real unit ρ, kernel.const_apply]

lemma lintegral_cond_kernel_real {f : α × ℝ → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, ∫⁻ y, f (a, y) ∂(cond_kernel_real ρ a) ∂ρ.fst = ∫⁻ x, f x ∂ρ :=
begin
  nth_rewrite 1 measure_eq_comp_prod_real ρ,
  rw [kernel.lintegral_comp_prod _ _ _ hf, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
end

lemma ae_cond_kernel_real_eq_one {s : set ℝ} (hs : measurable_set s) (hρ : ρ {x | x.snd ∈ sᶜ} = 0) :
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
  [nonempty Ω]
  (ρ : measure (α × Ω)) [is_finite_measure ρ]

/-- Existence of a conditional kernel. Use the definition `cond_kernel` to get that kernel. -/
lemma exists_cond_kernel (γ : Type*) [measurable_space γ] :
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
  rw [this, kernel.const_eq_comp_prod_real _ ρ'],
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

/-- Conditional kernel of a measure on a product space: a Markov kernel such that
`ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit ρ.cond_kernel)) ()`
(see `probability_theory.measure_eq_comp_prod`). -/
@[irreducible] noncomputable
def _root_.measure_theory.measure.cond_kernel : kernel α Ω :=
(exists_cond_kernel ρ unit).some

lemma cond_kernel_def : ρ.cond_kernel = (exists_cond_kernel ρ unit).some :=
by rw measure_theory.measure.cond_kernel

instance : is_markov_kernel ρ.cond_kernel :=
by { rw cond_kernel_def, exact (exists_cond_kernel ρ unit).some_spec.some, }

lemma kernel.const_unit_eq_comp_prod :
  kernel.const unit ρ
    = (kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit ρ.cond_kernel) :=
by { simp_rw cond_kernel_def, exact (exists_cond_kernel ρ unit).some_spec.some_spec, }

/-- **Disintegration** of finite product measures on `α × Ω`, where `Ω` is Polish Borel. Such a
measure can be written as the composition-product of the constant kernel with value `ρ.fst`
(marginal measure over `α`) and a Markov kernel from `α` to `Ω`. We call that Markov kernel
`probability_theory.cond_kernel ρ`. -/
theorem measure_eq_comp_prod :
  ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left unit ρ.cond_kernel)) () :=
by rw [← kernel.const_unit_eq_comp_prod, kernel.const_apply]

/-- **Disintegration** of constant kernels. A constant kernel on a product space `α × Ω`, where `Ω`
is Polish Borel, can be written as the composition-product of the constant kernel with value `ρ.fst`
(marginal measure over `α`) and a Markov kernel from `α` to `Ω`. We call that Markov kernel
`probability_theory.cond_kernel ρ`. -/
theorem kernel.const_eq_comp_prod (γ : Type*) [measurable_space γ]
  (ρ : measure (α × Ω)) [is_finite_measure ρ] :
  kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left γ ρ.cond_kernel) :=
begin
  ext a s hs : 2,
  simpa only [kernel.const_apply, kernel.comp_prod_apply _ _ _ hs, kernel.prod_mk_left_apply']
    using kernel.ext_iff'.mp (kernel.const_unit_eq_comp_prod ρ) () s hs,
end

lemma lintegral_cond_kernel_mem {s : set (α × Ω)} (hs : measurable_set s) :
  ∫⁻ a, ρ.cond_kernel a {x | (a, x) ∈ s} ∂ρ.fst = ρ s :=
begin
  conv_rhs { rw measure_eq_comp_prod ρ, },
  simp_rw [kernel.comp_prod_apply _ _ _ hs, kernel.const_apply, kernel.prod_mk_left_apply],
end

lemma set_lintegral_cond_kernel_eq_measure_prod {s : set α} (hs : measurable_set s)
  {t : set Ω} (ht : measurable_set t) :
  ∫⁻ a in s, ρ.cond_kernel a t ∂ρ.fst = ρ (s ×ˢ t) :=
begin
  have : ρ (s ×ˢ t) = ((kernel.const unit ρ.fst ⊗ₖ kernel.prod_mk_left unit ρ.cond_kernel) ())
    (s ×ˢ t),
  { congr, exact measure_eq_comp_prod ρ, },
  rw [this, kernel.comp_prod_apply _ _ _ (hs.prod ht)],
  simp only [prod_mk_mem_set_prod_eq, kernel.lintegral_const, kernel.prod_mk_left_apply],
  rw ← lintegral_indicator _ hs,
  congr,
  ext1 x,
  classical,
  rw indicator_apply,
  split_ifs with hx,
  { simp only [hx, if_true, true_and, set_of_mem_eq], },
  { simp only [hx, if_false, false_and, set_of_false, measure_empty], },
end

lemma lintegral_cond_kernel {f : α × Ω → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, ∫⁻ ω, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫⁻ x, f x ∂ρ :=
begin
  conv_rhs { rw measure_eq_comp_prod ρ, },
  rw [kernel.lintegral_comp_prod _ _ _ hf, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
end

lemma set_lintegral_cond_kernel {f : α × Ω → ℝ≥0∞} (hf : measurable f)
  {s : set α} (hs : measurable_set s) {t : set Ω} (ht : measurable_set t) :
  ∫⁻ a in s, ∫⁻ ω in t, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫⁻ x in s ×ˢ t, f x ∂ρ :=
begin
  conv_rhs { rw measure_eq_comp_prod ρ, },
  simp_rw [← kernel.restrict_apply _ (hs.prod ht), ← kernel.comp_prod_restrict,
    kernel.lintegral_comp_prod _ _ _ hf, kernel.restrict_apply, kernel.const_apply,
    kernel.prod_mk_left_apply],
end

lemma set_lintegral_cond_kernel_univ_right {f : α × Ω → ℝ≥0∞} (hf : measurable f)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, ∫⁻ ω, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫⁻ x in s ×ˢ univ, f x ∂ρ :=
by { rw ← set_lintegral_cond_kernel ρ hf hs measurable_set.univ, simp_rw measure.restrict_univ, }

lemma set_lintegral_cond_kernel_univ_left {f : α × Ω → ℝ≥0∞} (hf : measurable f)
  {t : set Ω} (ht : measurable_set t) :
  ∫⁻ a, ∫⁻ ω in t, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫⁻ x in univ ×ˢ t, f x ∂ρ :=
by { rw ← set_lintegral_cond_kernel ρ hf measurable_set.univ ht, simp_rw measure.restrict_univ, }

section integral_cond_kernel

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

lemma _root_.measure_theory.ae_strongly_measurable.integral_cond_kernel
  {ρ : measure (α × Ω)} [is_finite_measure ρ] {f : α × Ω → E} (hf : ae_strongly_measurable f ρ) :
  ae_strongly_measurable (λ x, ∫ y, f (x, y) ∂(ρ.cond_kernel x)) ρ.fst :=
begin
  rw measure_eq_comp_prod ρ at hf,
  exact ae_strongly_measurable.integral_kernel_comp_prod hf,
end

lemma integral_cond_kernel {ρ : measure (α × Ω)} [is_finite_measure ρ]
  {f : α × Ω → E} (hf : integrable f ρ) :
  ∫ a, ∫ x, f (a, x) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫ ω, f ω ∂ρ :=
begin
  conv_rhs { rw measure_eq_comp_prod ρ, },
  have hf' : integrable f ((kernel.const unit ρ.fst ⊗ₖ kernel.prod_mk_left unit ρ.cond_kernel) ()),
  { rwa measure_eq_comp_prod ρ at hf, },
  rw [integral_comp_prod hf', kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
end

lemma set_integral_cond_kernel {ρ : measure (α × Ω)} [is_finite_measure ρ]
  {f : α × Ω → E} {s : set α} (hs : measurable_set s)
  {t : set Ω} (ht : measurable_set t) (hf : integrable_on f (s ×ˢ t) ρ) :
  ∫ a in s, ∫ ω in t, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ :=
begin
  conv_rhs { rw measure_eq_comp_prod ρ, },
  rw set_integral_comp_prod hs ht,
  { simp_rw [kernel.prod_mk_left_apply, kernel.const_apply], },
  { rwa measure_eq_comp_prod ρ at hf, },
end

lemma set_integral_cond_kernel_univ_right {ρ : measure (α × Ω)} [is_finite_measure ρ]
  {f : α × Ω → E} {s : set α} (hs : measurable_set s)
  (hf : integrable_on f (s ×ˢ univ) ρ) :
  ∫ a in s, ∫ ω, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫ x in s ×ˢ univ, f x ∂ρ :=
by { rw ← set_integral_cond_kernel hs measurable_set.univ hf, simp_rw measure.restrict_univ, }

lemma set_integral_cond_kernel_univ_left {ρ : measure (α × Ω)} [is_finite_measure ρ]
  {f : α × Ω → E} {t : set Ω} (ht : measurable_set t)
  (hf : integrable_on f (univ ×ˢ t) ρ) :
  ∫ a, ∫ ω in t, f (a, ω) ∂(ρ.cond_kernel a) ∂ρ.fst = ∫ x in univ ×ˢ t, f x ∂ρ :=
by { rw ← set_integral_cond_kernel measurable_set.univ ht hf, simp_rw measure.restrict_univ, }

end integral_cond_kernel

end polish

end probability_theory

namespace measure_theory
/-! ### Integrability

We place these lemmas in the `measure_theory` namespace to enable dot notation. -/

open probability_theory

variables {α Ω E F : Type*} {mα : measurable_space α} [measurable_space Ω] [topological_space Ω]
  [borel_space Ω] [polish_space Ω] [nonempty Ω]
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [normed_add_comm_group F]
  {ρ : measure (α × Ω)} [is_finite_measure ρ]

include mα

lemma ae_strongly_measurable.ae_integrable_cond_kernel_iff
  {f : α × Ω → F} (hf : ae_strongly_measurable f ρ) :
  (∀ᵐ a ∂ρ.fst, integrable (λ ω, f (a, ω)) (ρ.cond_kernel a))
    ∧ integrable (λ a, ∫ ω, ‖f (a, ω)‖ ∂(ρ.cond_kernel a)) ρ.fst
  ↔ integrable f ρ :=
begin
  rw measure_eq_comp_prod ρ at hf,
  conv_rhs { rw measure_eq_comp_prod ρ, },
  rw integrable_comp_prod_iff hf,
  simp_rw [kernel.prod_mk_left_apply, kernel.const_apply],
end

lemma integrable.cond_kernel_ae {f : α × Ω → F} (hf_int : integrable f ρ) :
  ∀ᵐ a ∂ρ.fst, integrable (λ ω, f (a, ω)) (ρ.cond_kernel a) :=
begin
  have hf_ae : ae_strongly_measurable f ρ := hf_int.1,
  rw ← hf_ae.ae_integrable_cond_kernel_iff at hf_int,
  exact hf_int.1,
end

lemma integrable.integral_norm_cond_kernel {f : α × Ω → F} (hf_int : integrable f ρ) :
  integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(ρ.cond_kernel x)) ρ.fst :=
begin
  have hf_ae : ae_strongly_measurable f ρ := hf_int.1,
  rw ← hf_ae.ae_integrable_cond_kernel_iff at hf_int,
  exact hf_int.2,
end

lemma integrable.norm_integral_cond_kernel {f : α × Ω → E} (hf_int : integrable f ρ) :
  integrable (λ x, ‖∫ y, f (x, y) ∂(ρ.cond_kernel x)‖) ρ.fst :=
begin
  refine hf_int.integral_norm_cond_kernel.mono hf_int.1.integral_cond_kernel.norm _,
  refine eventually_of_forall (λ x, _),
  rw norm_norm,
  refine (norm_integral_le_integral_norm _).trans_eq (real.norm_of_nonneg _).symm,
  exact integral_nonneg_of_ae (eventually_of_forall (λ y, norm_nonneg _)),
end

lemma integrable.integral_cond_kernel {f : α × Ω → E} (hf_int : integrable f ρ) :
  integrable (λ x, ∫ y, f (x, y) ∂(ρ.cond_kernel x)) ρ.fst :=
(integrable_norm_iff hf_int.1.integral_cond_kernel).mp hf_int.norm_integral_cond_kernel

end measure_theory
