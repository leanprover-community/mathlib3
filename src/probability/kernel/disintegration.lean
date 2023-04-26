/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.cond_cdf

/-!
# Disintegration of product measures

Let `ρ` be a finite measure on `α × ℝ`. For any measurable space `γ`, there exists a kernel
`cond_kernel ρ : kernel α ℝ` such that we have a disintegration of the constant kernel from `γ` with
value `ρ`: `kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) γ)`,
where `ρ.fst` is the marginal measure of `ρ` on `α`. In particular,
`ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) unit)) (unit.star)`

## Main definitions

* `probability_theory.cond_kernel ρ : kernel α ℝ`: conditional kernel described above. We define it
  as the measure associated to the Stieltjes function `cond_kernel ρ a` for all `a : α`, and show
  that this defines a measurable map.

## Main statements

* `probability_theory.kernel.const_eq_comp_prod`:
  `kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) γ)`
* `probability_theory.measure_eq_comp_prod`:
  `ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) unit)) (unit.star)`
* `probability_theory.lintegral_cond_kernel`:
  `∫⁻ a, ∫⁻ y, f (a, y) ∂(cond_kernel ρ a) ∂ρ.fst = ∫⁻ x, f x ∂ρ`

## TODO

* We can obtain a disintegration for measures on `α × Ω` for a standard Borel space `Ω` by using
  that `Ω` is measurably equivalent to `ℝ`, `ℤ` or a finite set.
* The finite measure hypothesis can be weakened to σ-finite. The proof uses the finite case.
* Beyond measures, we can find a disintegration for a kernel `α → Ω × Ω'` by applying the
  construction used here for all `a : α` and showing additional measurability properties of the map
  we obtain.

-/

open measure_theory set filter

open_locale ennreal measure_theory topology probability_theory

namespace probability_theory

variables {α : Type*} {mα : measurable_space α}

include mα

/-- Conditional measure on the second space of the product given the value on the first. This is an
auxiliary definition used to build `cond_kernel`. -/
noncomputable def cond_measure (ρ : measure (α × ℝ)) (a : α) : measure ℝ := (cond_cdf ρ a).measure

lemma cond_measure_Iic (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  cond_measure ρ a (Iic x) = ennreal.of_real (cond_cdf ρ a x) :=
begin
  rw [cond_measure, ← sub_zero (cond_cdf ρ a x)],
  exact stieltjes_function.measure_Iic _ (tendsto_cond_cdf_at_bot ρ a) _,
end

lemma cond_measure_univ (ρ : measure (α × ℝ)) (a : α) :
  cond_measure ρ a univ = 1 :=
begin
  rw [← ennreal.of_real_one, ← sub_zero (1 : ℝ)],
  exact stieltjes_function.measure_univ _ (tendsto_cond_cdf_at_bot ρ a)
    (tendsto_cond_cdf_at_top ρ a),
end

instance (ρ : measure (α × ℝ)) (a : α) : is_probability_measure (cond_measure ρ a) :=
⟨cond_measure_univ ρ a⟩

/-- The function `a ↦ cond_measure ρ a` is measurable. This allows us to build a kernel from these
measures. -/
lemma measurable_cond_measure (ρ : measure (α × ℝ)) :
  measurable (cond_measure ρ) :=
begin
  rw measure.measurable_measure,
  refine λ s hs, measurable_space.induction_on_inter
    real.borel_eq_generate_from_Iic real.is_pi_system_Iic _ _ _ _ hs,
  { simp only [measure_empty, measurable_const], },
  { rintros S ⟨u, rfl⟩,
    simp_rw cond_measure_Iic ρ _ u,
    exact (measurable_cond_cdf ρ u).ennreal_of_real, },
  { intros t ht ht_cd_meas,
    have : (λ a, cond_measure ρ a tᶜ) = (λ a, cond_measure ρ a univ) - (λ a, cond_measure ρ a t),
    { ext1 a,
      rw [measure_compl ht (measure_ne_top (cond_measure ρ a) _), pi.sub_apply], },
    simp_rw [this, cond_measure_univ ρ],
    exact measurable.sub measurable_const ht_cd_meas, },
  { intros f hf_disj hf_meas hf_cd_meas,
    simp_rw measure_Union hf_disj hf_meas,
    exact measurable.ennreal_tsum hf_cd_meas, },
end

/-- Conditional measure on the second space of the product given the value on the first, as a
kernel. -/
noncomputable
def cond_kernel (ρ : measure (α × ℝ)) : kernel α ℝ :=
{ val := λ a, cond_measure ρ a,
  property := measurable_cond_measure ρ }

instance (ρ : measure (α × ℝ)) : is_markov_kernel (cond_kernel ρ) :=
⟨λ a, by { rw cond_kernel, apply_instance, } ⟩

lemma cond_kernel_Iic (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  cond_kernel ρ a (Iic x) = ennreal.of_real (cond_cdf ρ a x) :=
cond_measure_Iic ρ a x

lemma set_lintegral_cond_kernel_Iic (ρ : measure (α × ℝ)) [is_finite_measure ρ] (x : ℝ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, cond_kernel ρ a (Iic x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
by { simp_rw [cond_kernel_Iic], exact set_lintegral_cond_cdf_Iic ρ x hs, }

lemma set_lintegral_cond_kernel_univ (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, cond_kernel ρ a univ ∂ρ.fst = ρ (s ×ˢ univ) :=
begin
  rw ← real.Union_Iic_rat,
  have h_tendsto1 : tendsto (λ n : ℚ, ∫⁻ a in s, cond_kernel ρ a (Iic n) ∂ρ.fst) at_top
    (𝓝 (∫⁻ a in s, cond_kernel ρ a (⋃ r : ℚ, Iic r) ∂ρ.fst)),
  { refine tendsto_lintegral_filter_of_dominated_convergence (λ _, 1) _ _ _ _,
    { exact eventually_of_forall (λ n, kernel.measurable_coe _ measurable_set_Iic), },
    { refine eventually_of_forall (λ n, eventually_of_forall (λ a, _)),
      refine (measure_mono (subset_univ _)).trans_eq measure_univ, },
    { simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter, ne.def],
      exact measure_ne_top _ _, },
    { refine eventually_of_forall (λ a, tendsto_measure_Union (λ n m hnm x, _)),
      simp only [mem_Iic],
      refine λ hxn, hxn.trans _,
      exact_mod_cast hnm, }, },
  have h_tendsto2 : tendsto (λ n : ℚ, ∫⁻ a in s, cond_kernel ρ a (Iic n) ∂ρ.fst) at_top
    (𝓝 (ρ (s ×ˢ ⋃ r : ℚ, Iic r))),
  { simp_rw [set_lintegral_cond_kernel_Iic _ _ hs, prod_Union],
    refine tendsto_measure_Union (λ n m hnm x, _),
    simp only [rat.cast_coe_nat, mem_prod, mem_Iic, and_imp],
    refine λ hxs hxn, ⟨hxs, hxn.trans _⟩,
    exact_mod_cast hnm, },
  exact tendsto_nhds_unique h_tendsto1 h_tendsto2,
end

lemma lintegral_cond_kernel_univ (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∫⁻ a, cond_kernel ρ a univ ∂ρ.fst = ρ univ :=
by rw [← set_lintegral_univ, set_lintegral_cond_kernel_univ ρ measurable_set.univ, univ_prod_univ]

lemma set_lintegral_cond_kernel_prod (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) {t : set ℝ} (ht : measurable_set t) :
  ∫⁻ a in s, cond_kernel ρ a t ∂ρ.fst = ρ (s ×ˢ t) :=
begin
  -- `set_lintegral_cond_kernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generate the borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  refine measurable_space.induction_on_inter real.borel_eq_generate_from_Iic
    real.is_pi_system_Iic _ _ _ _ ht,
  { simp only [measure_empty, lintegral_const, zero_mul, prod_empty], },
  { rintros t ⟨q, rfl⟩,
    exact set_lintegral_cond_kernel_Iic ρ q hs, },
  { intros t ht ht_lintegral,
    calc ∫⁻ a in s, cond_kernel ρ a tᶜ ∂ρ.fst
        = ∫⁻ a in s, (cond_kernel ρ a univ) - cond_kernel ρ a t ∂ρ.fst :
      by { congr' with a, rw measure_compl ht (measure_ne_top (cond_kernel ρ a) _), }
    ... = ∫⁻ a in s, (cond_kernel ρ a univ) ∂ρ.fst - ∫⁻ a in s, cond_kernel ρ a t ∂ρ.fst :
      begin
        rw lintegral_sub (kernel.measurable_coe (cond_kernel ρ) ht),
        { rw ht_lintegral,
          exact measure_ne_top ρ _, },
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
      end
    ... = ρ (s ×ˢ univ) - ρ (s ×ˢ t) : by rw [set_lintegral_cond_kernel_univ ρ hs, ht_lintegral]
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
    { congr' with i : 1,
      exact hf_eq i, },
    { intros i j hij,
      rw [function.on_fun, disjoint_prod],
      exact or.inr (hf_disj hij), },
    { exact λ i, measurable_set.prod hs (hf_meas i), }, },
end

lemma lintegral_cond_kernel_mem (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set (α × ℝ)} (hs : measurable_set s) :
  ∫⁻ a, cond_kernel ρ a {x | (a, x) ∈ s} ∂ρ.fst = ρ s :=
begin
  -- `set_lintegral_cond_kernel_prod` gives the result for sets of the form `t₁ × t₂`. These sets
  -- form a π-system that generate the product σ-algebra, hence we can get the same equality for any
  -- measurable set `s`.
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
    have h_int_eq : ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst
      = ∫⁻ a in t₁, cond_kernel ρ a t₂ ∂ρ.fst,
    { rw ← lintegral_add_compl _ ht₁,
      have h_eq1 : ∫⁻ a in t₁, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst
        = ∫⁻ a in t₁, cond_kernel ρ a t₂ ∂ρ.fst,
      { refine set_lintegral_congr_fun ht₁ (eventually_of_forall (λ a ha, _)),
        rw h_prod_eq_snd a ha, },
      have h_eq2 : ∫⁻ a in t₁ᶜ, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst = 0,
      { suffices h_eq_zero : ∀ a ∈ t₁ᶜ, cond_kernel ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = 0,
        { rw set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero),
          simp only [lintegral_const, zero_mul], },
        intros a hat₁,
        suffices : {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = ∅, by rw [this, measure_empty],
        ext1 x,
        simp only [prod_mk_mem_set_prod_eq, mem_set_of_eq, mem_empty_iff_false, iff_false, not_and],
        exact λ ha, absurd ha hat₁, },
      rw [h_eq1, h_eq2, add_zero], },
    rw h_int_eq,
    exact set_lintegral_cond_kernel_prod ρ ht₁ ht₂, },
  { intros t ht ht_eq,
    calc ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ tᶜ} ∂ρ.fst
        = ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t}ᶜ ∂ρ.fst : rfl
    ... = ∫⁻ a, cond_kernel ρ a univ - cond_kernel ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst :
      begin
        congr' with a : 1,
        rw measure_compl _ (measure_ne_top (cond_kernel ρ a) _),
        exact measurable_prod_mk_left ht,
      end
    ... = ∫⁻ a, cond_kernel ρ a univ ∂ρ.fst - ∫⁻ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst :
      begin
        have h_le : (λ a, cond_kernel ρ a {x : ℝ | (a, x) ∈ t}) ≤ᵐ[ρ.fst] λ a, cond_kernel ρ a univ,
        { exact eventually_of_forall (λ a, measure_mono (subset_univ _)), },
        rw lintegral_sub _ _ h_le,
        { exact kernel.measurable_prod_mk_mem _ ht, },
        { refine ((lintegral_mono_ae h_le).trans_lt _).ne,
          rw lintegral_cond_kernel_univ,
          exact measure_lt_top ρ univ, },
      end
    ... = ρ univ - ρ t : by rw [ht_eq, lintegral_cond_kernel_univ]
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
    have h_meas : ∀ a i, measurable_set {x | (a, x) ∈ f i},
    { exact λ a i, measurable_prod_mk_left (hf_meas i), },
    calc ∫⁻ a, cond_kernel ρ a (⋃ i, {x | (a, x) ∈ f i}) ∂ρ.fst
        = ∫⁻ a, ∑' i, cond_kernel ρ a {x | (a, x) ∈ f i} ∂ρ.fst :
          by { congr' with a : 1, rw measure_Union (h_disj a) (h_meas a), }
    ... = ∑' i, ∫⁻ a, cond_kernel ρ a {x | (a, x) ∈ f i} ∂ρ.fst :
          begin
            rw lintegral_tsum (λ i : ℕ, measurable.ae_measurable _),
            exact kernel.measurable_prod_mk_mem _ (hf_meas i),
          end
    ... = ∑' i, ρ (f i) : by { congr' with i : 1, exact hf_eq i, }
    ... = ρ (Union f) : (measure_Union hf_disj hf_meas).symm, },
end

/-- **Disintegration** of constant kernels. A constant kernel on a product space `α × ℝ` can be
written as the composition-product of the constant kernel with value `ρ.fst` (marginal measure over
`α`) and a Markov kernel from `α` to `ℝ`. We call that Markov kernel `cond_kernel ρ`.
-/
theorem kernel.const_eq_comp_prod (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  (γ : Type*) [measurable_space γ] :
  kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) γ) :=
begin
  ext a s hs : 2,
  rw [kernel.comp_prod_apply _ _ _ hs, kernel.const_apply, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
  rw lintegral_cond_kernel_mem ρ hs,
end

/-- **Disintegration** of finite product measures on `α × ℝ`. Such a measure can be written as the
composition-product of the constant kernel with value `ρ.fst` (marginal measure over `α`) and a
Markov kernel from `α` to `ℝ`. We call that Markov kernel `cond_kernel ρ`. -/
theorem measure_eq_comp_prod (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ρ = ((kernel.const unit ρ.fst) ⊗ₖ (kernel.prod_mk_left (cond_kernel ρ) unit)) (unit.star) :=
by rw [← kernel.const_eq_comp_prod ρ unit, kernel.const_apply]

lemma lintegral_cond_kernel (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {f : α × ℝ → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, ∫⁻ y, f (a, y) ∂(cond_kernel ρ a) ∂ρ.fst = ∫⁻ x, f x ∂ρ :=
begin
  nth_rewrite 1 measure_eq_comp_prod ρ,
  rw [kernel.lintegral_comp_prod _ _ _ hf, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
end

section subset

/-! ### Disintegration of measures on subsets of the reals

Since every standard Borel space is measurably equivalent to a subset of `ℝ`, we can generalize a
disintegration result on those subsets to all these spaces. -/

/-- Restriction of kernel to a subtype of the target space. -/
noncomputable
def kernel.restrict_subtype {β : Type*} {mβ : measurable_space β} (κ : kernel α β) {s : set β}
  (hs : measurable_set s) :
  kernel α s :=
{ val := λ a, measure.comap coe (κ a),
  property :=
  begin
    refine measure.measurable_measure.mpr (λ t ht, _),
    have : (λ a, measure.comap coe (κ a) t) = λ a, κ a (coe '' t),
    { ext1 a,
      rw measure.comap_apply _ subtype.coe_injective (λ s' hs', _) _ ht,
      exact measurable_set.subtype_image hs hs', },
    rw this,
    exact kernel.measurable_coe _
      ((measurable_embedding.subtype_coe hs).measurable_set_image.mpr ht),
  end }

lemma kernel.restrict_subtype_apply {β : Type*} {mβ : measurable_space β} (κ : kernel α β)
  {s : set β} (hs : measurable_set s) (a : α)  :
  kernel.restrict_subtype κ hs a = measure.comap coe (κ a) := rfl

lemma kernel.restrict_subtype_apply' {β : Type*} {mβ : measurable_space β} (κ : kernel α β)
  {s : set β} (hs : measurable_set s) (a : α) {t : set s} (ht : measurable_set t) :
  kernel.restrict_subtype κ hs a t = κ a (coe '' t) :=
by rw [kernel.restrict_subtype_apply,
    measure.comap_apply _ subtype.coe_injective (λ s', measurable_set.subtype_image hs) _ ht]

instance is_finite_kernel.restrict_subtype {β : Type*} {mβ : measurable_space β} (κ : kernel α β)
  [is_finite_kernel κ] {s : set β} (hs : measurable_set s) :
  is_finite_kernel (kernel.restrict_subtype κ hs) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw kernel.restrict_subtype_apply' κ hs a measurable_set.univ,
  exact kernel.measure_le_bound κ a _,
end

instance is_s_finite_kernel.restrict_subtype {β : Type*} {mβ : measurable_space β} (κ : kernel α β)
  [is_finite_kernel κ] {s : set β} (hs : measurable_set s) :
  kernel.is_s_finite_kernel (kernel.restrict_subtype κ hs) :=
begin
  refine ⟨⟨λ n, kernel.restrict_subtype (kernel.seq κ n) hs, infer_instance, _⟩⟩,
  ext1 a,
  rw kernel.sum_apply,
  simp_rw kernel.restrict_subtype_apply _ hs,
  have : measure.sum (λ n, measure.comap (coe : s → β) (kernel.seq κ n a))
    = measure.comap coe (measure.sum (λ n, kernel.seq κ n a)),
  { ext1 t ht,
    rw [measure.comap_apply _ subtype.coe_injective (λ s', measurable_set.subtype_image hs) _ ht,
      measure.sum_apply _ ht, measure.sum_apply _ (measurable_set.subtype_image hs ht)],
    congr' with n : 1,
    rw measure.comap_apply _ subtype.coe_injective (λ s', measurable_set.subtype_image hs) _ ht, },
  rw [this, kernel.measure_sum_seq],
end

lemma measurable_embedding.prod_mk {β γ δ : Type*} {mβ : measurable_space β}
  {mγ : measurable_space γ} {mδ : measurable_space δ}
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
    { simp only [image_empty, measurable_set.empty], },
    { rintros t ⟨t₁, t₂, ht₁, ht₂, rfl⟩,
      rw ← prod_image_image_eq,
      exact (hg.measurable_set_image.mpr ht₁).prod (hf.measurable_set_image.mpr ht₂), },
    { intros t ht ht_m,
      rw [← range_diff_image h_inj, ← prod_range_range_eq],
      exact measurable_set.diff
        (measurable_set.prod hg.measurable_set_range hf.measurable_set_range) ht_m, },
    { intros g hg_disj hg_meas hg,
      simp_rw image_Union,
      exact measurable_set.Union hg, }, },
end

theorem kernel.const_eq_comp_prod' {s : set ℝ} (ρ : measure (α × s)) [is_finite_measure ρ]
  (γ : Type*) [measurable_space γ] (hs : measurable_set s) :
  kernel.const γ ρ = (kernel.const γ ρ.fst)
    ⊗ₖ (kernel.prod_mk_left
      (kernel.restrict_subtype (cond_kernel (ρ.map (coe : α × s → α × ℝ))) hs) γ) :=
begin
  have h_coe_eq : (coe : α × s → α × ℝ) = λ x, (x.1, ↑x.2),
  { ext1 x,
    nth_rewrite 0 ← @prod.mk.eta _ _ x,
    refl, },
  have h_coe_apply : ∀ a b, (coe : α × s → α × ℝ) (a, b) = (a, ↑b) := λ a b, rfl,
  ext a t ht : 2,
  have h_emb : measurable_embedding (coe : α × s → α × ℝ),
  { rw h_coe_eq,
    exact measurable_embedding.prod_mk measurable_embedding.id
      (measurable_embedding.subtype_coe hs), },
  rw [kernel.comp_prod_apply _ _ _ ht, kernel.const_apply, kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
  have : ∫⁻ b, kernel.restrict_subtype
      (cond_kernel (measure.map coe ρ)) hs b {c : ↥s | (b, c) ∈ t} ∂ρ.fst
    = ∫⁻ b, (cond_kernel (measure.map coe ρ)) b (coe '' {c : ↥s | (b, c) ∈ t}) ∂ρ.fst,
  { congr,
    ext1 a,
    rw kernel.restrict_subtype_apply' (cond_kernel (ρ.map (coe : α × s → α × ℝ))) hs,
    exact measurable_prod_mk_left ht, },
  have h_fst : (ρ.map (coe : α × s → α × ℝ)).fst = ρ.fst,
  { ext1 t ht,
    simp_rw measure.fst_apply _ ht,
    rw measure.map_apply h_emb.measurable (measurable_fst ht),
    congr' 1 with x,
    simp only [mem_preimage],
    rw [← @prod.mk.eta _ _ x, h_coe_apply],  },
  rw [this, ← h_fst],
  have h_set_eq : ∀ b, (coe : s → ℝ) '' {c : ↥s | (b, c) ∈ t}
    = {c : ℝ | (b, c) ∈ (coe : α × s → α × ℝ) '' t},
  { intro a,
    rw h_coe_eq,
    ext1 x,
    simp only [mem_image, mem_set_of_eq, set_coe.exists, subtype.coe_mk, exists_and_distrib_right,
      exists_eq_right, prod.mk.inj_iff, prod.exists, exists_eq_right_right], },
  simp_rw h_set_eq,
  rw [lintegral_cond_kernel_mem (measure.map coe ρ) (h_emb.measurable_set_image.mpr ht),
    measure.map_apply h_emb.measurable (h_emb.measurable_set_image.mpr ht),
    preimage_image_eq _ h_emb.injective],
end

end subset

end probability_theory
