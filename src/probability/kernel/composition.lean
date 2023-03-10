/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.kernel.basic

/-!
# Product and composition of kernels

We define
* the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : kernel α β` and
  `η : kernel (α × β) γ`, a kernel from `α` to `β × γ`.
* the map and comap of a kernel along a measurable function.
* the composition `η ∘ₖ κ` of s-finite kernels `κ : kernel α β` and `η : kernel β γ`,
  a kernel from `α` to `γ`.
* the product `prod κ η` of s-finite kernels `κ : kernel α β` and `η : kernel α γ`,
  a kernel from `α` to `β × γ`.

A note on names:
The composition-product `kernel α β → kernel (α × β) γ → kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

Kernels built from other kernels:
* `comp_prod (κ : kernel α β) (η : kernel (α × β) γ) : kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = comp_prod κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
* `map (κ : kernel α β) (f : β → γ) (hf : measurable f) : kernel α γ`
  `∫⁻ c, g c ∂(map κ f hf a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : kernel α β) (f : γ → α) (hf : measurable f) : kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`
* `comp (η : kernel β γ) (κ : kernel α β) : kernel α γ`: composition of 2 s-finite kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`
* `prod (κ : kernel α β) (η : kernel α γ) : kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂(prod κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_comp_prod`, `lintegral_map`, `lintegral_comap`, `lintegral_comp`, `lintegral_prod`:
  Lebesgue integral of a function against a composition-product/map/comap/composition/product of
  kernels.
* Instances of the form `<class>.<operation>` where class is one of `is_markov_kernel`,
  `is_finite_kernel`, `is_s_finite_kernel` and operation is one of `comp_prod`, `map`, `comap`,
  `comp`, `prod`. These instances state that the three classes are stable by the various operations.

## Notations

* `κ ⊗ₖ η = probability_theory.kernel.comp_prod κ η`
* `η ∘ₖ κ = probability_theory.kernel.comp η κ`

-/

open measure_theory

open_locale ennreal

namespace probability_theory

namespace kernel

variables {α β ι : Type*} {mα : measurable_space α} {mβ : measurable_space β}

include mα mβ

section composition_product

/-!
### Composition-Product of kernels

We define a kernel composition-product
`comp_prod : kernel α β → kernel (α × β) γ → kernel α (β × γ)`.
-/

variables {γ : Type*} {mγ : measurable_space γ} {s : set (β × γ)}

include mγ

/-- Auxiliary function for the definition of the composition-product of two kernels.
For all `a : α`, `comp_prod_fun κ η a` is a countably additive function with value zero on the empty
set, and the composition-product of kernels is defined in `kernel.comp_prod` through
`measure.of_measurable`. -/
noncomputable
def comp_prod_fun (κ : kernel α β) (η : kernel (α × β) γ) (a : α) (s : set (β × γ)) : ℝ≥0∞ :=
∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂(κ a)

lemma comp_prod_fun_empty (κ : kernel α β) (η : kernel (α × β) γ) (a : α) :
  comp_prod_fun κ η a ∅ = 0 :=
by simp only [comp_prod_fun, set.mem_empty_iff_false, set.set_of_false, measure_empty,
  lintegral_const, zero_mul]

lemma comp_prod_fun_Union (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel η] (a : α)
  (f : ℕ → set (β × γ)) (hf_meas : ∀ i, measurable_set (f i)) (hf_disj : pairwise (disjoint on f)) :
  comp_prod_fun κ η a (⋃ i, f i) = ∑' i, comp_prod_fun κ η a (f i) :=
begin
  have h_Union : (λ b, η (a, b) {c : γ | (b, c) ∈ ⋃ i, f i})
    = λ b, η (a,b) (⋃ i, {c : γ | (b, c) ∈ f i}),
  { ext1 b,
    congr' with c,
    simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
    refl, },
  rw [comp_prod_fun, h_Union],
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

lemma comp_prod_fun_tsum_right (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel η]
  (a : α) (hs : measurable_set s) :
  comp_prod_fun κ η a s = ∑' n, comp_prod_fun κ (seq η n) a s :=
begin
  simp_rw [comp_prod_fun, (measure_sum_seq η _).symm],
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

lemma comp_prod_fun_tsum_left (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel κ]
  (a : α) (s : set (β × γ)) :
  comp_prod_fun κ η a s = ∑' n, comp_prod_fun (seq κ n) η a s :=
by simp_rw [comp_prod_fun, (measure_sum_seq κ _).symm, lintegral_sum_measure]

lemma comp_prod_fun_eq_tsum (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  comp_prod_fun κ η a s = ∑' n m, comp_prod_fun (seq κ n) (seq η m) a s :=
by simp_rw [comp_prod_fun_tsum_left κ η a s, comp_prod_fun_tsum_right _ η a hs]

/-- Auxiliary lemma for `measurable_comp_prod_fun`. -/
lemma measurable_comp_prod_fun_of_finite (κ : kernel α β) [is_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] (hs : measurable_set s) :
  measurable (λ a, comp_prod_fun κ η a s) :=
begin
  simp only [comp_prod_fun],
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

lemma measurable_comp_prod_fun (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] (hs : measurable_set s) :
  measurable (λ a, comp_prod_fun κ η a s) :=
begin
  simp_rw comp_prod_fun_tsum_right κ η _ hs,
  refine measurable.ennreal_tsum (λ n, _),
  simp only [comp_prod_fun],
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

/-- Composition-Product of kernels. It verifies
`∫⁻ bc, f bc ∂(comp_prod κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
(see `lintegral_comp_prod`). -/
noncomputable
def comp_prod (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  kernel α (β × γ) :=
{ val := λ a, measure.of_measurable (λ s hs, comp_prod_fun κ η a s) (comp_prod_fun_empty κ η a)
    (comp_prod_fun_Union κ η a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, measure.of_measurable (λ s hs, comp_prod_fun κ η a s) (comp_prod_fun_empty κ η a)
        (comp_prod_fun_Union κ η a) s) = λ a, comp_prod_fun κ η a s,
    { ext1 a, rwa measure.of_measurable_apply, },
    rw this,
    exact measurable_comp_prod_fun κ η hs,
  end, }

localized "infix (name := kernel.comp_prod) ` ⊗ₖ `:100 := probability_theory.kernel.comp_prod" in
  probability_theory

lemma comp_prod_apply_eq_comp_prod_fun (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  (κ ⊗ₖ η) a s = comp_prod_fun κ η a s :=
begin
  rw [comp_prod],
  change measure.of_measurable (λ s hs, comp_prod_fun κ η a s) (comp_prod_fun_empty κ η a)
    (comp_prod_fun_Union κ η a) s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂(κ a),
  rw measure.of_measurable_apply _ hs,
  refl,
end

lemma comp_prod_apply (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  (κ ⊗ₖ η) a s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂(κ a) :=
comp_prod_apply_eq_comp_prod_fun κ η a hs

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_comp_prod' (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
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
    rw [comp_prod_apply κ η _ hs, ← lintegral_const_mul c _],
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

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_comp_prod (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a) :=
begin
  let g := function.curry f,
  change ∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, g b c ∂(η (a, b)) ∂(κ a),
  rw ← lintegral_comp_prod',
  { simp_rw [g, function.curry_apply, prod.mk.eta], },
  { simp_rw [g, function.uncurry_curry], exact hf, },
end

lemma comp_prod_eq_tsum_comp_prod (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) (hs : measurable_set s) :
  (κ ⊗ₖ η) a s = ∑' (n m : ℕ), (seq κ n ⊗ₖ seq η m) a s :=
by { simp_rw comp_prod_apply_eq_comp_prod_fun _ _ _ hs, exact comp_prod_fun_eq_tsum κ η a hs, }

lemma comp_prod_eq_sum_comp_prod (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  κ ⊗ₖ η = kernel.sum (λ n, kernel.sum (λ m, seq κ n ⊗ₖ seq η m)) :=
by { ext a s hs : 2, simp_rw [kernel.sum_apply' _ a hs], rw comp_prod_eq_tsum_comp_prod κ η a hs, }

lemma comp_prod_eq_sum_comp_prod_left (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  κ ⊗ₖ η = kernel.sum (λ n, seq κ n ⊗ₖ η) :=
begin
  rw comp_prod_eq_sum_comp_prod,
  congr' with n a s hs,
  simp_rw [kernel.sum_apply' _ _ hs, comp_prod_apply_eq_comp_prod_fun _ _ _ hs,
    comp_prod_fun_tsum_right _ η a hs],
end

lemma comp_prod_eq_sum_comp_prod_right (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  κ ⊗ₖ η = kernel.sum (λ n, κ ⊗ₖ seq η n) :=
begin
  rw comp_prod_eq_sum_comp_prod,
  simp_rw comp_prod_eq_sum_comp_prod_left κ _,
  rw kernel.sum_comm,
end

instance is_markov_kernel.comp_prod (κ : kernel α β) [is_markov_kernel κ]
  (η : kernel (α × β) γ) [is_markov_kernel η] :
  is_markov_kernel (κ ⊗ₖ η) :=
⟨λ a, ⟨begin
  rw comp_prod_apply κ η a measurable_set.univ,
  simp only [set.mem_univ, set.set_of_true, measure_univ, lintegral_one],
end⟩⟩

lemma comp_prod_apply_univ_le (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] (a : α) :
  (κ ⊗ₖ η) a set.univ ≤ (κ a set.univ) * (is_finite_kernel.bound η) :=
begin
  rw comp_prod_apply κ η a measurable_set.univ,
  simp only [set.mem_univ, set.set_of_true],
  let Cη := is_finite_kernel.bound η,
  calc ∫⁻ b, η (a, b) set.univ ∂(κ a)
      ≤ ∫⁻ b, Cη ∂(κ a) : lintegral_mono (λ b, measure_le_bound η (a, b) set.univ)
  ... = Cη * κ a set.univ : lintegral_const Cη
  ... = κ a set.univ * Cη : mul_comm _ _,
end

instance is_finite_kernel.comp_prod (κ : kernel α β) [is_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] :
  is_finite_kernel (κ ⊗ₖ η) :=
⟨⟨is_finite_kernel.bound κ * is_finite_kernel.bound η,
  ennreal.mul_lt_top (is_finite_kernel.bound_ne_top κ) (is_finite_kernel.bound_ne_top η),
  λ a, calc (κ ⊗ₖ η) a set.univ
    ≤ (κ a set.univ) * is_finite_kernel.bound η : comp_prod_apply_univ_le κ η a
... ≤ is_finite_kernel.bound κ * is_finite_kernel.bound η :
        mul_le_mul (measure_le_bound κ a set.univ) le_rfl (zero_le _) (zero_le _), ⟩⟩

instance is_s_finite_kernel.comp_prod (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  is_s_finite_kernel (κ ⊗ₖ η) :=
begin
  rw comp_prod_eq_sum_comp_prod,
  exact kernel.is_s_finite_kernel_sum (λ n, kernel.is_s_finite_kernel_sum infer_instance),
end

end composition_product

section map_comap
/-! ### map, comap -/

variables {γ : Type*} {mγ : measurable_space γ} {f : β → γ} {g : γ → α}

include mγ

/-- The pushforward of a kernel along a measurable function. 
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `map` of a Markov kernel
is again a Markov kernel. -/
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

/-- Pullback of a kernel, such that for each set s `comap κ g hg c s = κ (g c) s`.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `comap` of a Markov kernel
is again a Markov kernel. -/
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

open_locale probability_theory

section fst_snd

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

/-- Define a `kernel (β × α) γ` from a `kernel (α × β) γ` by taking the comap of `prod.swap`. -/
def swap_left (κ : kernel (α × β) γ) : kernel (β × α) γ :=
comap κ prod.swap measurable_swap

lemma swap_left_apply (κ : kernel (α × β) γ) (a : β × α) :
  swap_left κ a = (κ a.swap) := rfl

lemma swap_left_apply' (κ : kernel (α × β) γ) (a : β × α) (s : set γ) :
  swap_left κ a s = κ a.swap s := rfl

lemma lintegral_swap_left (κ : kernel (α × β) γ) (a : β × α) (g : γ → ℝ≥0∞) :
  ∫⁻ c, g c ∂(swap_left κ a) = ∫⁻ c, g c ∂(κ a.swap) :=
by { rw [swap_left, lintegral_comap _ measurable_swap a], }

instance is_markov_kernel.swap_left (κ : kernel (α × β) γ) [is_markov_kernel κ] :
  is_markov_kernel (swap_left κ) :=
by { rw swap_left, apply_instance, }

instance is_finite_kernel.swap_left (κ : kernel (α × β) γ) [is_finite_kernel κ] :
  is_finite_kernel (swap_left κ) :=
by { rw swap_left, apply_instance, }

instance is_s_finite_kernel.swap_left (κ : kernel (α × β) γ) [is_s_finite_kernel κ] :
  is_s_finite_kernel (swap_left κ) :=
by { rw swap_left, apply_instance, }

/-- Define a `kernel α (γ × β)` from a `kernel α (β × γ)` by taking the map of `prod.swap`. -/
noncomputable
def swap_right (κ : kernel α (β × γ)) : kernel α (γ × β) :=
map κ prod.swap measurable_swap

lemma swap_right_apply (κ : kernel α (β × γ)) (a : α) :
  swap_right κ a = (κ a).map prod.swap := rfl

lemma swap_right_apply' (κ : kernel α (β × γ)) (a : α) {s : set (γ × β)} (hs : measurable_set s) :
  swap_right κ a s = κ a {p | p.swap ∈ s} :=
by { rw [swap_right_apply, measure.map_apply measurable_swap hs], refl, }

lemma lintegral_swap_right (κ : kernel α (β × γ)) (a : α) {g : γ × β → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂(swap_right κ a) = ∫⁻ (bc : β × γ), g bc.swap ∂(κ a) :=
by rw [swap_right, lintegral_map _ measurable_swap a hg]

instance is_markov_kernel.swap_right (κ : kernel α (β × γ)) [is_markov_kernel κ] :
  is_markov_kernel (swap_right κ) :=
by { rw swap_right, apply_instance, }

instance is_finite_kernel.swap_right (κ : kernel α (β × γ)) [is_finite_kernel κ] :
  is_finite_kernel (swap_right κ) :=
by { rw swap_right, apply_instance, }

instance is_s_finite_kernel.swap_right (κ : kernel α (β × γ)) [is_s_finite_kernel κ] :
  is_s_finite_kernel (swap_right κ) :=
by { rw swap_right, apply_instance, }

/-- Define a `kernel α β` from a `kernel α (β × γ)` by taking the map of the first projection. -/
noncomputable
def fst (κ : kernel α (β × γ)) : kernel α β :=
map κ prod.fst measurable_fst

lemma fst_apply (κ : kernel α (β × γ)) (a : α) :
  fst κ a = (κ a).map prod.fst := rfl

lemma fst_apply' (κ : kernel α (β × γ)) (a : α) {s : set β} (hs : measurable_set s) :
  fst κ a s = κ a {p | p.1 ∈ s} :=
by { rw [fst_apply, measure.map_apply measurable_fst hs], refl, }

lemma lintegral_fst (κ : kernel α (β × γ)) (a : α) {g : β → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂(fst κ a) = ∫⁻ (bc : β × γ), g bc.fst ∂(κ a) :=
by rw [fst, lintegral_map _ measurable_fst a hg]

instance is_markov_kernel.fst (κ : kernel α (β × γ)) [is_markov_kernel κ] :
  is_markov_kernel (fst κ) :=
by { rw fst, apply_instance, }

instance is_finite_kernel.fst (κ : kernel α (β × γ)) [is_finite_kernel κ] :
  is_finite_kernel (fst κ) :=
by { rw fst, apply_instance, }

instance is_s_finite_kernel.fst (κ : kernel α (β × γ)) [is_s_finite_kernel κ] :
  is_s_finite_kernel (fst κ) :=
by { rw fst, apply_instance, }

/-- Define a `kernel α γ` from a `kernel α (β × γ)` by taking the map of the second projection. -/
noncomputable
def snd (κ : kernel α (β × γ)) : kernel α γ :=
map κ prod.snd measurable_snd

lemma snd_apply (κ : kernel α (β × γ)) (a : α) :
  snd κ a = (κ a).map prod.snd := rfl

lemma snd_apply' (κ : kernel α (β × γ)) (a : α) {s : set γ} (hs : measurable_set s) :
  snd κ a s = κ a {p | p.2 ∈ s} :=
by { rw [snd_apply, measure.map_apply measurable_snd hs], refl, }

lemma lintegral_snd (κ : kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂(snd κ a) = ∫⁻ (bc : β × γ), g bc.snd ∂(κ a) :=
by rw [snd, lintegral_map _ measurable_snd a hg]

instance is_markov_kernel.snd (κ : kernel α (β × γ)) [is_markov_kernel κ] :
  is_markov_kernel (snd κ) :=
by { rw snd, apply_instance, }

instance is_finite_kernel.snd (κ : kernel α (β × γ)) [is_finite_kernel κ] :
  is_finite_kernel (snd κ) :=
by { rw snd, apply_instance, }

instance is_s_finite_kernel.snd (κ : kernel α (β × γ)) [is_s_finite_kernel κ] :
  is_s_finite_kernel (snd κ) :=
by { rw snd, apply_instance, }

end fst_snd

section comp
/-! ### Composition of two kernels -/

variables {γ : Type*} {mγ : measurable_space γ} {f : β → γ} {g : γ → α}

include mγ

/-- Composition of two s-finite kernels. -/
noncomputable
def comp (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ] :
  kernel α γ :=
snd (κ ⊗ₖ prod_mk_left η α)

localized "infix (name := kernel.comp) ` ∘ₖ `:100 := probability_theory.kernel.comp" in
  probability_theory

lemma comp_apply (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ]
  (a : α) {s : set γ} (hs : measurable_set s) :
  (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂(κ a) :=
begin
  rw [comp, snd_apply' _ _ hs, comp_prod_apply],
  swap, { exact measurable_snd hs, },
  simp only [set.mem_set_of_eq, set.set_of_mem_eq, prod_mk_left_apply' _ _ s],
end

lemma lintegral_comp (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ]
  (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a) :=
begin
  rw [comp, lintegral_snd _ _ hg],
  change ∫⁻ bc, (λ a b, g b) bc.fst bc.snd ∂((κ ⊗ₖ prod_mk_left η α) a)
    = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a),
  exact lintegral_comp_prod _ _ _ (hg.comp measurable_snd),
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

section prod

/-! ### Product of two kernels -/

variables {γ : Type*} {mγ : measurable_space γ}

include mγ

/-- Product of two s-finite kernels. -/
noncomputable
def prod (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel α γ) [is_s_finite_kernel η] :
  kernel α (β × γ) :=
κ ⊗ₖ (swap_left (prod_mk_left η β))

lemma prod_apply (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel α γ) [is_s_finite_kernel η]
  (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  (prod κ η) a s = ∫⁻ (b : β), (η a) {c : γ | (b, c) ∈ s} ∂(κ a) :=
by simp_rw [prod, comp_prod_apply _ _ _ hs, swap_left_apply _ _, prod_mk_left_apply,
  prod.swap_prod_mk]

lemma lintegral_prod (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel α γ) [is_s_finite_kernel η]
  (a : α) {g : (β × γ) → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂((prod κ η) a) = ∫⁻ b, ∫⁻ c, g (b, c) ∂(η a) ∂(κ a) :=
by simp_rw [prod, lintegral_comp_prod _ _ _ hg, swap_left_apply, prod_mk_left_apply,
  prod.swap_prod_mk]

instance is_markov_kernel.prod (κ : kernel α β) [is_markov_kernel κ]
  (η : kernel α γ) [is_markov_kernel η] :
  is_markov_kernel (prod κ η) :=
by { rw prod, apply_instance, }

instance is_finite_kernel.prod (κ : kernel α β) [is_finite_kernel κ]
  (η : kernel α γ) [is_finite_kernel η] :
  is_finite_kernel (prod κ η) :=
by { rw prod, apply_instance, }

instance is_s_finite_kernel.prod (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel α γ) [is_s_finite_kernel η] :
  is_s_finite_kernel (prod κ η) :=
by { rw prod, apply_instance, }

end prod

end kernel

end probability_theory
