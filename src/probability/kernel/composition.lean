/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.kernel.basic

/-!
# Product and composition of kernels

Given s-finite kernels `κ : kernel α β` and `η : kernel (α × β) γ`, we define their product
`κ ⊗ₖ η`, a kernel from `α` to `β × γ`.
We define the map and comap of a kernel along a measurable function.
Finally, we define the composition `η ∘ₖ κ` of s-finite kernels `κ : kernel α β` and
`η : kernel β γ`,  a kernel from `α` to `γ`.

A note on names: [kallenberg2021] calls composition and denotes by `κ ⊗ η` the map
`kernel α β → kernel (α × β) γ → kernel α (β × γ)`, which we call product and denote by `⊗ₖ`.
On the other hand, most papers studying categories of kernels call composition the map we call
composition. We adopt that convention because it fits better with the use of the name `comp`
elsewhere in mathlib.

## Main definitions

Kernels built from other kernels:
* `prod (κ : kernel α β) (η : kernel (α × β) γ) : kernel α (β × γ)`: product of 2 s-finite kernels.
  We define a notation `κ ⊗ₖ η = prod κ η`.
  `∫⁻ bc, f bc.1 bc.2 ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a)`
* `map (κ : kernel α β) (f : β → γ) (hf : measurable f) : kernel α mγ`
  `∫⁻ b, g b ∂(map κ f hf a) = ∫⁻ a, g (f a) ∂(κ a)`
* `comap (κ : kernel α β) (f : γ → α) (hf : measurable f) : kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`
* `comp (η : kernel β γ) (κ : kernel α β) : kernel α γ`: composition of 2 s-finite kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`

## Main statements

* `lintegral_prod`, `lintegral_map`, `lintegral_comap`, `lintegral_comp`: Lebesgue integral of a
  function against a product/map/comap/composition of kernels.
* `is_markov_kernel.prod`, `is_finite_kernel.prod`, `is_s_finite_kernel.prod`: if two kernels are
  Markov/finite/s-finite then their product is as well.
* `is_markov_kernel.map`, `is_finite_kernel.map`, `is_s_finite_kernel.map`: if a kernel is
  Markov/finite/s-finite then its map along a measurable function is as well.
* `is_markov_kernel.comap`, `is_finite_kernel.comap`, `is_s_finite_kernel.comap`: if a kernel is
  Markov/finite/s-finite then its comap along a measurable function is as well.
* `is_markov_kernel.comp`, `is_finite_kernel.comp`, `is_s_finite_kernel.comp`: if two kernels are
  Markov/finite/s-finite then their composition is as well.

## Notations

* `κ ⊗ₖ η = probability_theory.kernel.prod κ η`
* `η ∘ₖ κ = probability_theory.kernel.comp η κ`

-/

open measure_theory

open_locale ennreal

namespace probability_theory

namespace kernel

variables {α β ι : Type*} {mα : measurable_space α} {mβ : measurable_space β}

include mα mβ

section product

/-!
### Product of kernels

We define a kernel product `prod : kernel α β → kernel (α × β) γ → kernel α (β × γ)`.
-/

variables {γ : Type*} {mγ : measurable_space γ} {s : set (β × γ)}

include mγ

/-- Auxiliary function for the definition of the product of two kernels. For all `a : α`,
`prod_fun κ η a` is a countably additive function with value zero on the empty set, and the
product of kernels is defined in `kernel.prod` through `measure.of_measurable`. -/
noncomputable
def prod_fun (κ : kernel α β) (η : kernel (α × β) γ) (a : α) (s : set (β × γ)) : ℝ≥0∞ :=
∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂(κ a)

lemma prod_fun_empty (κ : kernel α β) (η : kernel (α × β) γ) (a : α) :
  prod_fun κ η a ∅ = 0 :=
by simp only [prod_fun, set.mem_empty_iff_false, set.set_of_false, measure_empty, lintegral_const,
  zero_mul]

lemma prod_fun_Union (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel η] (a : α)
  (f : ℕ → set (β × γ)) (hf_meas : ∀ i, measurable_set (f i)) (hf_disj : pairwise (disjoint on f)) :
  prod_fun κ η a (⋃ i, f i) = ∑' i, prod_fun κ η a (f i) :=
begin
  have h_Union : (λ b, η (a, b) {c : γ | (b, c) ∈ ⋃ i, f i})
    = λ b, η (a,b) (⋃ i, {c : γ | (b, c) ∈ f i}),
  { ext1 b,
    congr' with c,
    simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
    refl, },
  rw [prod_fun, h_Union],
  have h_tsum : (λ b, η (a, b) (⋃ i, {c : γ | (b, c) ∈ f i}))
    = λ b, ∑' i, η (a, b) {c : γ | (b, c) ∈ f i},
  { ext1 b,
    rw measure_Union,
    { intros i j hij s hsi hsj c hcs,
      have hbci : {(b, c)} ⊆ f i, by { rw set.singleton_subset_iff, exact hsi hcs, },
      have hbcj : {(b, c)} ⊆ f j, by { rw set.singleton_subset_iff, exact hsj hcs, },
      simpa only [set.bot_eq_empty, set.le_eq_subset, set.singleton_subset_iff,
        set.mem_empty_iff_false] using hf_disj hij hbci hbcj, },
    { exact λ i, (@measurable_prod_mk_left β γ _ _ b) _ (hf_meas i), }, },
  rw [h_tsum, lintegral_tsum],
  { refl, },
  { intros i,
    have hm : measurable_set {p : (α × β) × γ | (p.1.2, p.2) ∈ f i},
      from measurable_fst.snd.prod_mk measurable_snd (hf_meas i),
    exact ((measurable_prod_mk_mem η hm).comp measurable_prod_mk_left).ae_measurable, },
end

lemma prod_fun_tsum_right (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel η]
  (a : α) (hs : measurable_set s) :
  prod_fun κ η a s = ∑' n, prod_fun κ (seq η n) a s :=
begin
  simp_rw [prod_fun, (measure_sum_seq η _).symm],
  have : ∫⁻ b, measure.sum (λ n, seq η n (a, b)) {c : γ | (b, c) ∈ s} ∂(κ a)
    = ∫⁻ b, ∑' n, seq η n (a, b) {c : γ | (b, c) ∈ s} ∂(κ a),
  { congr',
    ext1 b,
    rw measure.sum_apply,
    exact measurable_prod_mk_left hs, },
  rw [this, lintegral_tsum (λ n : ℕ, _)],
  exact ((measurable_prod_mk_mem (seq η n) ((measurable_fst.snd.prod_mk measurable_snd) hs)).comp
    measurable_prod_mk_left).ae_measurable,
end

lemma prod_fun_tsum_left (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel κ]
  (a : α) (s : set (β × γ)) :
  prod_fun κ η a s = ∑' n, prod_fun (seq κ n) η a s :=
by simp_rw [prod_fun, (measure_sum_seq κ _).symm, lintegral_sum_measure]

lemma prod_fun_eq_tsum (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  prod_fun κ η a s = ∑' n m, prod_fun (seq κ n) (seq η m) a s :=
by simp_rw [prod_fun_tsum_left κ η a s, prod_fun_tsum_right _ η a hs]

/-- Auxiliary lemma for `measurable_prod_fun`. -/
lemma measurable_prod_fun_of_finite (κ : kernel α β) [is_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] (hs : measurable_set s) :
  measurable (λ a, prod_fun κ η a s) :=
begin
  simp only [prod_fun],
  have h_meas : measurable (function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})),
  { have : function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})
      = λ p, η p {c : γ | (p.2, c) ∈ s},
    { ext1 p,
      have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
      rw [hp_eq_mk, function.uncurry_apply_pair], },
    rw this,
    exact measurable_prod_mk_mem η (measurable_fst.snd.prod_mk measurable_snd hs), },
  exact measurable_lintegral κ h_meas,
end

lemma measurable_prod_fun (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] (hs : measurable_set s) :
  measurable (λ a, prod_fun κ η a s) :=
begin
  simp_rw prod_fun_tsum_right κ η _ hs,
  refine measurable.ennreal_tsum (λ n, _),
  simp only [prod_fun],
  have h_meas : measurable (function.uncurry (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s})),
  { have : function.uncurry (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s})
      = λ p, seq η n p {c : γ | (p.2, c) ∈ s},
    { ext1 p,
      have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
      rw [hp_eq_mk, function.uncurry_apply_pair], },
    rw this,
    exact measurable_prod_mk_mem (seq η n) (measurable_fst.snd.prod_mk measurable_snd hs), },
  exact measurable_lintegral κ h_meas,
end

/-- Product of kernels. It verifies
`∫⁻ bc, f bc.1 bc.2 ∂(prod κ η a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a)` (see `lintegral_prod`). -/
noncomputable
def prod (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  kernel α (β × γ) :=
{ val := λ a, measure.of_measurable (λ s hs, prod_fun κ η a s) (prod_fun_empty κ η a)
    (prod_fun_Union κ η a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, measure.of_measurable (λ s hs, prod_fun κ η a s) (prod_fun_empty κ η a)
        (prod_fun_Union κ η a) s) = λ a, prod_fun κ η a s,
    { ext1 a, rwa measure.of_measurable_apply, },
    rw this,
    exact measurable_prod_fun κ η hs,
  end, }

localized "infix (name := kernel.prod) ` ⊗ₖ `:100 := probability_theory.kernel.prod" in
  probability_theory

lemma prod_apply_eq_prod_fun (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  (κ ⊗ₖ η) a s = prod_fun κ η a s :=
begin
  rw [prod],
  change measure.of_measurable (λ s hs, prod_fun κ η a s) (prod_fun_empty κ η a)
    (prod_fun_Union κ η a) s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂(κ a),
  rw measure.of_measurable_apply _ hs,
  refl,
end

lemma prod_apply (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  (κ ⊗ₖ η) a s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂(κ a) :=
prod_apply_eq_prod_fun κ η a hs

/-- Integral against the product of two kernels. -/
theorem lintegral_prod (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) {f : β → γ → ℝ≥0∞} (hf : measurable (function.uncurry f)) :
  ∫⁻ bc, f bc.1 bc.2 ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a) :=
begin
  let F : ℕ → simple_func (β × γ) ℝ≥0∞ := simple_func.eapprox (function.uncurry f),
  have h : ∀ a, (⨆ n, F n a) = function.uncurry f a,
    from simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw [← h, prod.mk.eta],
  have h_mono : monotone F := λ i j hij b, simple_func.monotone_eapprox (function.uncurry f) hij _,
  rw lintegral_supr (λ n, (F n).measurable) h_mono,
  have : ∀ b, ∫⁻ c, (⨆ n, F n (b, c)) ∂(η (a, b)) = ⨆ n, ∫⁻ c, F n (b, c) ∂(η (a, b)),
  { intro a,
    rw lintegral_supr,
    { exact λ n, (F n).measurable.comp measurable_prod_mk_left, },
    { exact λ i j hij b, h_mono hij _, }, },
  simp_rw this,
  have h_some_meas_integral : ∀ f' : simple_func (β × γ) ℝ≥0∞,
    measurable (λ b, ∫⁻ c, f' (b, c) ∂(η (a, b))),
  { intros f',
    have : (λ b, ∫⁻ c, f' (b, c) ∂(η (a, b)))
        = (λ ab, ∫⁻ c, f' (ab.2, c) ∂(η (ab))) ∘ (λ b, (a, b)),
      { ext1 ab, refl, },
      rw this,
      refine measurable.comp _ measurable_prod_mk_left,
      exact (measurable_lintegral η
        ((simple_func.measurable _).comp (measurable_fst.snd.prod_mk measurable_snd))), },
  rw lintegral_supr,
  rotate,
  { exact λ n, h_some_meas_integral (F n), },
  { exact λ i j hij b, lintegral_mono (λ c, h_mono hij _), },
  congr,
  ext1 n,
  refine simple_func.induction _ _ (F n),
  { intros c s hs,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator, lintegral_indicator_const hs],
    rw [prod_apply κ η _ hs, ← lintegral_const_mul c _],
    swap, { exact (measurable_prod_mk_mem η ((measurable_fst.snd.prod_mk measurable_snd) hs)).comp
      measurable_prod_mk_left, },
    congr,
    ext1 b,
    rw lintegral_indicator_const_comp measurable_prod_mk_left hs,
    refl, },
  { intros f f' h_disj hf_eq hf'_eq,
    simp_rw [simple_func.coe_add, pi.add_apply],
    change ∫⁻ x, ((f : (β × γ) → ℝ≥0∞) x + f' x) ∂((κ ⊗ₖ η) a)
      = ∫⁻ b, ∫⁻ (c : γ), f (b, c) + f' (b, c) ∂(η (a, b)) ∂(κ a),
    rw [lintegral_add_left (simple_func.measurable _), hf_eq, hf'_eq, ← lintegral_add_left],
    swap, { exact h_some_meas_integral f, },
    congr' with b,
    rw ← lintegral_add_left ((simple_func.measurable _).comp measurable_prod_mk_left), },
end

lemma prod_eq_tsum_prod (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  (κ ⊗ₖ η) a s = ∑' (n m : ℕ), (seq κ n ⊗ₖ seq η m) a s :=
by { simp_rw prod_apply_eq_prod_fun _ _ _ hs, exact prod_fun_eq_tsum κ η a hs, }

lemma prod_eq_sum_prod (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  κ ⊗ₖ η = kernel.sum (λ n, kernel.sum (λ m, seq κ n ⊗ₖ seq η m)) :=
by { ext a s hs : 2, simp_rw [kernel.sum_apply' _ a hs], rw prod_eq_tsum_prod κ η a hs, }

lemma prod_eq_sum_prod_left (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  κ ⊗ₖ η = kernel.sum (λ n, seq κ n ⊗ₖ η) :=
begin
  rw prod_eq_sum_prod,
  congr' with n a s hs,
  simp_rw [kernel.sum_apply' _ _ hs, prod_apply_eq_prod_fun _ _ _ hs,
    prod_fun_tsum_right _ η a hs],
end

lemma prod_eq_sum_prod_right (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  κ ⊗ₖ η = kernel.sum (λ n, κ ⊗ₖ seq η n) :=
by { rw prod_eq_sum_prod, simp_rw prod_eq_sum_prod_left κ _, rw kernel.sum_comm, }

instance is_markov_kernel.prod (κ : kernel α β) [is_markov_kernel κ]
  (η : kernel (α × β) γ) [is_markov_kernel η] :
  is_markov_kernel (κ ⊗ₖ η) :=
⟨λ a, ⟨
begin
  rw prod_apply κ η a measurable_set.univ,
  simp only [set.mem_univ, set.set_of_true, measure_univ, lintegral_one],
end⟩⟩

lemma prod_apply_univ_le (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] (a : α) :
  (κ ⊗ₖ η) a set.univ ≤ (κ a set.univ) * (is_finite_kernel.bound η) :=
begin
  rw prod_apply κ η a measurable_set.univ,
  simp only [set.mem_univ, set.set_of_true],
  let Cη := is_finite_kernel.bound η,
  calc ∫⁻ b, η (a, b) set.univ ∂(κ a)
      ≤ ∫⁻ b, Cη ∂(κ a) : lintegral_mono (λ b, measure_le_bound η (a, b) set.univ)
  ... = Cη * κ a set.univ : lintegral_const Cη
  ... = κ a set.univ * Cη : mul_comm _ _,
end

instance is_finite_kernel.prod (κ : kernel α β) [is_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] :
  is_finite_kernel (κ ⊗ₖ η) :=
⟨⟨is_finite_kernel.bound κ * is_finite_kernel.bound η,
  ennreal.mul_lt_top (is_finite_kernel.bound_ne_top κ) (is_finite_kernel.bound_ne_top η),
  λ a, calc (κ ⊗ₖ η) a set.univ
    ≤ (κ a set.univ) * is_finite_kernel.bound η : prod_apply_univ_le κ η a
... ≤ is_finite_kernel.bound κ * is_finite_kernel.bound η :
        mul_le_mul (measure_le_bound κ a set.univ) le_rfl (zero_le _) (zero_le _), ⟩⟩

instance is_s_finite_kernel.prod (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  is_s_finite_kernel (κ ⊗ₖ η) :=
begin
  rw prod_eq_sum_prod,
  exact kernel.is_s_finite_kernel_sum (λ n, kernel.is_s_finite_kernel_sum infer_instance),
end

end product

section map_comap
/-! ### map, comap -/

variables {γ : Type*} {mγ : measurable_space γ} {f : β → γ} {g : γ → α}

include mγ

/-- The pushforward of a kernel along a measurable function. -/
noncomputable
def map (κ : kernel α β) (f : β → γ) (hf : measurable f) : kernel α γ :=
{ val := λ a, (κ a).map f,
  property := (measure.measurable_map _ hf).comp (kernel.measurable κ) }

lemma map_apply (κ : kernel α β) (hf : measurable f) (a : α) :
  map κ f hf a = (κ a).map f := rfl

lemma map_apply' (κ : kernel α β) (hf : measurable f) (a : α) {s : set γ} (hs : measurable_set s) :
  map κ f hf a s = κ a (f ⁻¹' s) :=
by rw [map_apply, measure.map_apply hf hs]

lemma lintegral_map (κ : kernel α β) (hf : measurable f) (a : α)
  {g' : γ → ℝ≥0∞} (hg : measurable g') :
  ∫⁻ b, g' b ∂(map κ f hf a) = ∫⁻ a, g' (f a) ∂(κ a) :=
by rw [map_apply _ hf, lintegral_map hg hf]

lemma sum_map_seq (κ : kernel α β) [is_s_finite_kernel κ] (hf : measurable f) :
  kernel.sum (λ n, map (seq κ n) f hf) = map κ f hf :=
begin
  ext a s hs : 2,
  rw [kernel.sum_apply, map_apply' κ hf a hs, measure.sum_apply _ hs, ← measure_sum_seq κ,
    measure.sum_apply _ (hf hs)],
  simp_rw map_apply' _ hf _ hs,
end

instance is_markov_kernel.map (κ : kernel α β) [is_markov_kernel κ] (hf : measurable f) :
  is_markov_kernel (map κ f hf) :=
 ⟨λ a, ⟨by rw [map_apply' κ hf a measurable_set.univ, set.preimage_univ, measure_univ]⟩⟩

instance is_finite_kernel.map (κ : kernel α β) [is_finite_kernel κ] (hf : measurable f) :
  is_finite_kernel (map κ f hf) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw map_apply' κ hf a measurable_set.univ,
  exact measure_le_bound κ a _,
end

instance is_s_finite_kernel.map (κ : kernel α β) [is_s_finite_kernel κ] (hf : measurable f) :
  is_s_finite_kernel (map κ f hf) :=
⟨⟨λ n, map (seq κ n) f hf, infer_instance, (sum_map_seq κ hf).symm⟩⟩

/-- Pullback of a kernel, such that for each set s `comap κ g hg c s = κ (g c) s`. -/
def comap (κ : kernel α β) (g : γ → α) (hg : measurable g) : kernel γ β :=
{ val := λ a, κ (g a),
  property := (kernel.measurable κ).comp hg }

lemma comap_apply (κ : kernel α β) (hg : measurable g) (c : γ) :
  comap κ g hg c = κ (g c) := rfl

lemma comap_apply' (κ : kernel α β) (hg : measurable g) (c : γ) (s : set β) :
  comap κ g hg c s = κ (g c) s := rfl

lemma lintegral_comap (κ : kernel α β) (hg : measurable g) (c : γ) (g' : β → ℝ≥0∞) :
  ∫⁻ b, g' b ∂(comap κ g hg c) = ∫⁻ b, g' b ∂(κ (g c)) := rfl

lemma sum_comap_seq (κ : kernel α β) [is_s_finite_kernel κ] (hg : measurable g) :
  kernel.sum (λ n, comap (seq κ n) g hg) = comap κ g hg :=
begin
  ext a s hs : 2,
  rw [kernel.sum_apply, comap_apply' κ hg a s, measure.sum_apply _ hs, ← measure_sum_seq κ,
    measure.sum_apply _ hs],
  simp_rw comap_apply' _ hg _ s,
end

instance is_markov_kernel.comap (κ : kernel α β) [is_markov_kernel κ] (hg : measurable g) :
  is_markov_kernel (comap κ g hg) :=
⟨λ a, ⟨by rw [comap_apply' κ hg a set.univ, measure_univ]⟩⟩

instance is_finite_kernel.comap (κ : kernel α β) [is_finite_kernel κ] (hg : measurable g) :
  is_finite_kernel (comap κ g hg) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw comap_apply' κ hg a set.univ,
  exact measure_le_bound κ _ _,
end

instance is_s_finite_kernel.comap (κ : kernel α β) [is_s_finite_kernel κ] (hg : measurable g) :
  is_s_finite_kernel (comap κ g hg) :=
⟨⟨λ n, comap (seq κ n) g hg, infer_instance, (sum_comap_seq κ hg).symm⟩⟩

end map_comap

section comp
/-! ### Composition of two kernels -/

/-- Define a `kernel (γ × α) β` from a `kernel α β` by taking the comap of the projection. -/
def prod_mk_left (κ : kernel α β) (γ : Type*) [measurable_space γ] : kernel (γ × α) β :=
comap κ prod.snd measurable_snd

variables {γ : Type*} {mγ : measurable_space γ} {f : β → γ} {g : γ → α}

include mγ

lemma prod_mk_left_apply (κ : kernel α β) (ca : γ × α) :
  prod_mk_left κ γ ca = κ ca.snd := rfl

lemma prod_mk_left_apply' (κ : kernel α β) (ca : γ × α) (s : set β) :
  prod_mk_left κ γ ca s = κ ca.snd s := rfl

lemma lintegral_prod_mk_left (κ : kernel α β) (ca : γ × α) (g : β → ℝ≥0∞) :
  ∫⁻ b, g b ∂(prod_mk_left κ γ ca) = ∫⁻ b, g b ∂(κ ca.snd) := rfl

instance is_markov_kernel.prod_mk_left (κ : kernel α β) [is_markov_kernel κ] :
  is_markov_kernel (prod_mk_left κ γ) :=
by { rw prod_mk_left, apply_instance, }

instance is_finite_kernel.prod_mk_left (κ : kernel α β) [is_finite_kernel κ] :
  is_finite_kernel (prod_mk_left κ γ) :=
by { rw prod_mk_left, apply_instance, }

instance is_s_finite_kernel.prod_mk_left (κ : kernel α β) [is_s_finite_kernel κ] :
  is_s_finite_kernel (prod_mk_left κ γ) :=
by { rw prod_mk_left, apply_instance, }

/-- Define a `kernel α γ` from a `kernel α (β × γ)` by taking the map of the projection. -/
noncomputable
def snd_right (κ : kernel α (β × γ)) : kernel α γ :=
map κ prod.snd measurable_snd

lemma snd_right_apply (κ : kernel α (β × γ)) (a : α) :
  snd_right κ a = (κ a).map prod.snd := rfl

lemma snd_right_apply' (κ : kernel α (β × γ)) (a : α) {s : set γ} (hs : measurable_set s) :
  snd_right κ a s = κ a {p | p.2 ∈ s} :=
by { rw [snd_right_apply, measure.map_apply measurable_snd hs], refl, }

lemma lintegral_snd_right (κ : kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂(snd_right κ a) = ∫⁻ (bc : β × γ), g bc.snd ∂(κ a) :=
by rw [snd_right, lintegral_map _ measurable_snd a hg]

instance is_markov_kernel.snd_right (κ : kernel α (β × γ)) [is_markov_kernel κ] :
  is_markov_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

instance is_finite_kernel.snd_right (κ : kernel α (β × γ)) [is_finite_kernel κ] :
  is_finite_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

instance is_s_finite_kernel.snd_right (κ : kernel α (β × γ)) [is_s_finite_kernel κ] :
  is_s_finite_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

open_locale probability_theory

/-- Composition of two s-finite kernels. -/
noncomputable
def comp (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ] :
  kernel α γ :=
snd_right (κ ⊗ₖ prod_mk_left η α)

localized "infix (name := kernel.comp) ` ∘ₖ `:100 := probability_theory.kernel.comp" in
  probability_theory

lemma comp_apply (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ]
  (a : α) {s : set γ} (hs : measurable_set s) :
  (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂(κ a) :=
begin
  rw [comp, snd_right_apply' _ _ hs, prod_apply],
  swap, { exact measurable_snd hs, },
  simp only [set.mem_set_of_eq, set.set_of_mem_eq, prod_mk_left_apply' _ _ s],
end

lemma lintegral_comp (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ]
  (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a) :=
begin
  rw [comp, lintegral_snd_right _ _ hg],
  change ∫⁻ bc, (λ a b, g b) bc.fst bc.snd ∂((κ ⊗ₖ prod_mk_left η α) a)
    = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a),
  exact lintegral_prod _ _ _ (hg.comp measurable_snd),
end

instance is_markov_kernel.comp (η : kernel β γ) [is_markov_kernel η]
  (κ : kernel α β) [is_markov_kernel κ] :
  is_markov_kernel (η ∘ₖ κ) :=
by { rw comp, apply_instance, }

instance is_finite_kernel.comp (η : kernel β γ) [is_finite_kernel η]
  (κ : kernel α β) [is_finite_kernel κ] :
  is_finite_kernel (η ∘ₖ κ) :=
by { rw comp, apply_instance, }

instance is_s_finite_kernel.comp (η : kernel β γ) [is_s_finite_kernel η]
  (κ : kernel α β) [is_s_finite_kernel κ] :
  is_s_finite_kernel (η ∘ₖ κ) :=
by { rw comp, apply_instance, }

/-- Composition of kernels is associative. -/
lemma comp_assoc {δ : Type*} {mδ : measurable_space δ} (ξ : kernel γ δ) [is_s_finite_kernel ξ]
  (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ] :
  (ξ ∘ₖ η ∘ₖ κ) = ξ ∘ₖ (η ∘ₖ κ) :=
begin
  refine ext_fun (λ a f hf, _),
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ (measurable_lintegral' ξ hf)],
end

lemma deterministic_comp_eq_map (hf : measurable f) (κ : kernel α β) [is_s_finite_kernel κ] :
  (deterministic hf ∘ₖ κ) = map κ f hf :=
begin
  ext a s hs : 2,
  simp_rw [map_apply' _ _ _ hs, comp_apply _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul],
end

lemma comp_deterministic_eq_comap (κ : kernel α β) [is_s_finite_kernel κ] (hg : measurable g) :
  (κ ∘ₖ deterministic hg) = comap κ g hg :=
begin
  ext a s hs : 2,
  simp_rw [comap_apply' _ _ _ s, comp_apply _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (kernel.measurable_coe κ hs)],
end

end comp

end kernel

end probability_theory
