/-
Copyright (c) 2022 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
import measure_theory.function.l1_space
import measure_theory.function.simple_func_dense

/-!
# Density of simple functions

Show that each `Lᵖ` Borel measurable function can be approximated in `Lᵖ` norm
by a sequence of simple functions.

## Main definitions

* `measure_theory.Lp.simple_func`, the type of `Lp` simple functions
* `coe_to_Lp`, the embedding of `Lp.simple_func E p μ` into `Lp E p μ`

## Main results

* `tendsto_approx_on_univ_Lp` (Lᵖ convergence): If `E` is a `normed_add_comm_group` and `f` is
  measurable and `mem_ℒp` (for `p < ∞`), then the simple functions
  `simple_func.approx_on f hf s 0 h₀ n` may be considered as elements of `Lp E p μ`, and they tend
  in Lᵖ to `f`.
* `Lp.simple_func.dense_embedding`: the embedding `coe_to_Lp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simple_func.induction`, `Lp.induction`, `mem_ℒp.induction`, `integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/

noncomputable theory
open set function filter topological_space ennreal emetric finset
open_locale classical topology ennreal measure_theory big_operators
variables {α β ι E F 𝕜 : Type*}

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

/-! ### Lp approximation by simple functions -/

section Lp
variables [measurable_space β] [measurable_space E] [normed_add_comm_group E]
  [normed_add_comm_group F] {q : ℝ} {p : ℝ≥0∞}

lemma nnnorm_approx_on_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ‖approx_on f hf s y₀ h₀ n x - f x‖₊ ≤ ‖f x - y₀‖₊ :=
begin
  have := edist_approx_on_le hf h₀ x n,
  rw edist_comm y₀ at this,
  simp only [edist_nndist, nndist_eq_nnnorm] at this,
  exact_mod_cast this
end

lemma norm_approx_on_y₀_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ‖approx_on f hf s y₀ h₀ n x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖ :=
begin
  have := edist_approx_on_y0_le hf h₀ x n,
  repeat { rw [edist_comm y₀, edist_eq_coe_nnnorm_sub] at this },
  exact_mod_cast this,
end

lemma norm_approx_on_zero_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} (h₀ : (0 : E) ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ‖approx_on f hf s 0 h₀ n x‖ ≤ ‖f x‖ + ‖f x‖ :=
begin
  have := edist_approx_on_y0_le hf h₀ x n,
  simp [edist_comm (0 : E), edist_eq_coe_nnnorm] at this,
  exact_mod_cast this,
end

lemma tendsto_approx_on_Lp_snorm [opens_measurable_space E]
  {f : β → E} (hf : measurable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s]
  (hp_ne_top : p ≠ ∞) {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s)
  (hi : snorm (λ x, f x - y₀) p μ < ∞) :
  tendsto (λ n, snorm (approx_on f hf s y₀ h₀ n - f) p μ) at_top (𝓝 0) :=
begin
  by_cases hp_zero : p = 0,
  { simpa only [hp_zero, snorm_exponent_zero] using tendsto_const_nhds },
  have hp : 0 < p.to_real := to_real_pos hp_zero hp_ne_top,
  suffices : tendsto (λ n, ∫⁻ x, ‖approx_on f hf s y₀ h₀ n x - f x‖₊ ^ p.to_real ∂μ) at_top (𝓝 0),
  { simp only [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_ne_top],
    convert continuous_rpow_const.continuous_at.tendsto.comp this;
    simp [_root_.inv_pos.mpr hp] },
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas : ∀ n, measurable (λ x, (‖approx_on f hf s y₀ h₀ n x - f x‖₊ : ℝ≥0∞) ^ p.to_real),
  { simpa only [← edist_eq_coe_nnnorm_sub] using
      λ n, (approx_on f hf s y₀ h₀ n).measurable_bind (λ y x, (edist y (f x)) ^ p.to_real)
      (λ y, (measurable_edist_right.comp hf).pow_const p.to_real) },
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `λ x, ‖f x - y₀‖ ^ p.to_real`
  have h_bound : ∀ n, (λ x, (‖approx_on f hf s y₀ h₀ n x - f x‖₊ : ℝ≥0∞) ^ p.to_real)
      ≤ᵐ[μ] (λ x, ‖f x - y₀‖₊ ^ p.to_real),
  { exact λ n, eventually_of_forall
      (λ x, rpow_le_rpow (coe_mono (nnnorm_approx_on_le hf h₀ x n)) to_real_nonneg) },
  -- (3) The bounding function `λ x, ‖f x - y₀‖ ^ p.to_real` has finite integral
  have h_fin :  ∫⁻ (a : β), ‖f a - y₀‖₊ ^ p.to_real ∂μ ≠ ⊤,
    from (lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_zero hp_ne_top hi).ne,
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim : ∀ᵐ (a : β) ∂μ,
    tendsto (λ n, (‖approx_on f hf s y₀ h₀ n a - f a‖₊ : ℝ≥0∞) ^ p.to_real) at_top (𝓝 0),
  { filter_upwards [hμ] with a ha,
    have : tendsto (λ n, (approx_on f hf s y₀ h₀ n) a - f a) at_top (𝓝 (f a - f a)),
    { exact (tendsto_approx_on hf h₀ ha).sub tendsto_const_nhds },
    convert continuous_rpow_const.continuous_at.tendsto.comp (tendsto_coe.mpr this.nnnorm),
    simp [zero_rpow_of_pos hp] },
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim,
end

lemma mem_ℒp_approx_on [borel_space E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : mem_ℒp f p μ) {s : set E} {y₀ : E}
  (h₀ : y₀ ∈ s) [separable_space s] (hi₀ : mem_ℒp (λ x, y₀) p μ) (n : ℕ) :
  mem_ℒp (approx_on f fmeas s y₀ h₀ n) p μ :=
begin
  refine ⟨(approx_on f fmeas s y₀ h₀ n).ae_strongly_measurable, _⟩,
  suffices : snorm (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) p μ < ⊤,
  { have : mem_ℒp (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approx_on f fmeas s y₀ h₀ n - const β y₀).ae_strongly_measurable, this⟩,
    convert snorm_add_lt_top this hi₀,
    ext x,
    simp },
  have hf' : mem_ℒp (λ x, ‖f x - y₀‖) p μ,
  { have h_meas : measurable (λ x, ‖f x - y₀‖),
    { simp only [← dist_eq_norm],
      exact (continuous_id.dist continuous_const).measurable.comp fmeas },
    refine ⟨h_meas.ae_measurable.ae_strongly_measurable, _⟩,
    rw snorm_norm,
    convert snorm_add_lt_top hf hi₀.neg,
    ext x,
    simp [sub_eq_add_neg] },
  have : ∀ᵐ x ∂μ, ‖approx_on f fmeas s y₀ h₀ n x - y₀‖ ≤ ‖(‖f x - y₀‖ + ‖f x - y₀‖)‖,
  { refine eventually_of_forall _,
    intros x,
    convert norm_approx_on_y₀_le fmeas h₀ x n,
    rw [real.norm_eq_abs, abs_of_nonneg],
    exact add_nonneg (norm_nonneg _) (norm_nonneg _) },
  calc snorm (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) p μ
      ≤ snorm (λ x, ‖f x - y₀‖ + ‖f x - y₀‖) p μ : snorm_mono_ae this
  ... < ⊤ : snorm_add_lt_top hf' hf',
end

lemma tendsto_approx_on_range_Lp_snorm [borel_space E]
  {f : β → E} (hp_ne_top : p ≠ ∞) {μ : measure β} (fmeas : measurable f)
  [separable_space (range f ∪ {0} : set E)]
  (hf : snorm f p μ < ∞) :
  tendsto (λ n, snorm (approx_on f fmeas (range f ∪ {0}) 0 (by simp) n - f) p μ) at_top (𝓝 0) :=
begin
  refine tendsto_approx_on_Lp_snorm fmeas _ hp_ne_top _ _,
  { apply eventually_of_forall,
    assume x,
    apply subset_closure,
    simp },
  { simpa using hf }
end

lemma mem_ℒp_approx_on_range [borel_space E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) [separable_space (range f ∪ {0} : set E)]
  (hf : mem_ℒp f p μ) (n : ℕ) :
  mem_ℒp (approx_on f fmeas (range f ∪ {0}) 0 (by simp) n) p μ :=
mem_ℒp_approx_on fmeas hf (by simp) zero_mem_ℒp n

lemma tendsto_approx_on_range_Lp [borel_space E]
  {f : β → E} [hp : fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) {μ : measure β} (fmeas : measurable f)
  [separable_space (range f ∪ {0} : set E)] (hf : mem_ℒp f p μ) :
  tendsto (λ n, (mem_ℒp_approx_on_range fmeas hf n).to_Lp
    (approx_on f fmeas (range f ∪ {0}) 0 (by simp) n))
      at_top (𝓝 (hf.to_Lp f)) :=
by simpa only [Lp.tendsto_Lp_iff_tendsto_ℒp'']
  using tendsto_approx_on_range_Lp_snorm hp_ne_top fmeas hf.2

/-- Any function in `ℒp` can be approximated by a simple function if `p < ∞`. -/
lemma _root_.measure_theory.mem_ℒp.exists_simple_func_snorm_sub_lt
  {E : Type*} [normed_add_comm_group E]
  {f : β → E} {μ : measure β} (hf : mem_ℒp f p μ) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (g : β →ₛ E), snorm (f - g) p μ < ε ∧ mem_ℒp g p μ :=
begin
  borelize E,
  let f' := hf.1.mk f,
  suffices H : ∃ (g : β →ₛ E), snorm (f' - g) p μ < ε ∧ mem_ℒp g p μ,
  { rcases H with ⟨g, hg, g_mem⟩,
    refine ⟨g, _, g_mem⟩,
    convert hg using 1,
    apply snorm_congr_ae,
    filter_upwards [hf.1.ae_eq_mk] with x hx,
    simpa only [pi.sub_apply, sub_left_inj] using hx },
  have hf' : mem_ℒp f' p μ, from hf.ae_eq hf.1.ae_eq_mk,
  have f'meas : measurable f' := hf.1.measurable_mk,
  haveI : separable_space (range f' ∪ {0} : set E),
    from strongly_measurable.separable_space_range_union_singleton hf.1.strongly_measurable_mk,
  rcases ((tendsto_order.1 (tendsto_approx_on_range_Lp_snorm hp_ne_top f'meas hf'.2)).2
    ε hε.bot_lt).exists with ⟨n, hn⟩,
  rw [← snorm_neg, neg_sub] at hn,
  exact ⟨_, hn, mem_ℒp_approx_on_range f'meas hf' _⟩,
end

end Lp

/-! ### L1 approximation by simple functions -/

section integrable
variables [measurable_space β]
variables [measurable_space E] [normed_add_comm_group E]

lemma tendsto_approx_on_L1_nnnorm [opens_measurable_space E]
  {f : β → E} (hf : measurable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s]
  {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : has_finite_integral (λ x, f x - y₀) μ) :
  tendsto (λ n, ∫⁻ x, ‖approx_on f hf s y₀ h₀ n x - f x‖₊ ∂μ) at_top (𝓝 0) :=
by simpa [snorm_one_eq_lintegral_nnnorm] using tendsto_approx_on_Lp_snorm hf h₀ one_ne_top hμ
  (by simpa [snorm_one_eq_lintegral_nnnorm] using hi)

lemma integrable_approx_on [borel_space E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ)
  {s : set E} {y₀ : E} (h₀ : y₀ ∈ s)
  [separable_space s] (hi₀ : integrable (λ x, y₀) μ) (n : ℕ) :
  integrable (approx_on f fmeas s y₀ h₀ n) μ :=
begin
  rw ← mem_ℒp_one_iff_integrable at hf hi₀ ⊢,
  exact mem_ℒp_approx_on fmeas hf h₀ hi₀ n,
end

lemma tendsto_approx_on_range_L1_nnnorm [opens_measurable_space E]
  {f : β → E} {μ : measure β} [separable_space (range f ∪ {0} : set E)]
  (fmeas : measurable f) (hf : integrable f μ) :
  tendsto (λ n, ∫⁻ x, ‖approx_on f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖₊ ∂μ)
    at_top (𝓝 0) :=
begin
  apply tendsto_approx_on_L1_nnnorm fmeas,
  { apply eventually_of_forall,
    assume x,
    apply subset_closure,
    simp },
  { simpa using hf.2 }
end

lemma integrable_approx_on_range [borel_space E]
  {f : β → E} {μ : measure β} (fmeas : measurable f)
  [separable_space (range f ∪ {0} : set E)] (hf : integrable f μ) (n : ℕ) :
  integrable (approx_on f fmeas (range f ∪ {0}) 0 (by simp) n) μ :=
integrable_approx_on fmeas hf _ (integrable_zero _ _ _) n

end integrable

section simple_func_properties

variables [measurable_space α]
variables [normed_add_comm_group E] [normed_add_comm_group F]
variables {μ : measure α} {p : ℝ≥0∞}

/-!
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `μ`:
- `mem_ℒp f 0 μ` and `mem_ℒp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `mem_ℒp f p μ ↔ integrable f μ ↔ f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞`.
-/

lemma exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
exists_forall_le (f.map (λ x, ‖x‖))

lemma mem_ℒp_zero (f : α →ₛ E) (μ : measure α) : mem_ℒp f 0 μ :=
mem_ℒp_zero_iff_ae_strongly_measurable.mpr f.ae_strongly_measurable

lemma mem_ℒp_top (f : α →ₛ E) (μ : measure α) : mem_ℒp f ∞ μ :=
let ⟨C, hfC⟩ := f.exists_forall_norm_le in
mem_ℒp_top_of_bound f.ae_strongly_measurable C $ eventually_of_forall hfC

protected lemma snorm'_eq {p : ℝ} (f : α →ₛ F) (μ : measure α) :
  snorm' f p μ = (∑ y in f.range, (‖y‖₊ : ℝ≥0∞) ^ p * μ (f ⁻¹' {y})) ^ (1/p) :=
have h_map : (λ a, (‖f a‖₊ : ℝ≥0∞) ^ p) = f.map (λ a : F, (‖a‖₊ : ℝ≥0∞) ^ p), by simp,
by rw [snorm', h_map, lintegral_eq_lintegral, map_lintegral]

lemma measure_preimage_lt_top_of_mem_ℒp (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) (f : α →ₛ E)
  (hf : mem_ℒp f p μ) (y : E) (hy_ne : y ≠ 0) :
  μ (f ⁻¹' {y}) < ∞ :=
begin
  have hp_pos_real : 0 < p.to_real, from ennreal.to_real_pos hp_pos hp_ne_top,
  have hf_snorm := mem_ℒp.snorm_lt_top hf,
  rw [snorm_eq_snorm' hp_pos hp_ne_top, f.snorm'_eq,
    ← @ennreal.lt_rpow_one_div_iff _ _ (1 / p.to_real) (by simp [hp_pos_real]),
    @ennreal.top_rpow_of_pos (1 / (1 / p.to_real)) (by simp [hp_pos_real]),
    ennreal.sum_lt_top_iff] at hf_snorm,
  by_cases hyf : y ∈ f.range,
  swap,
  { suffices h_empty : f ⁻¹' {y} = ∅,
      by { rw [h_empty, measure_empty], exact ennreal.coe_lt_top, },
    ext1 x,
    rw [set.mem_preimage, set.mem_singleton_iff, mem_empty_iff_false, iff_false],
    refine λ hxy, hyf _,
    rw [mem_range, set.mem_range],
    exact ⟨x, hxy⟩, },
  specialize hf_snorm y hyf,
  rw ennreal.mul_lt_top_iff at hf_snorm,
  cases hf_snorm,
  { exact hf_snorm.2, },
  cases hf_snorm,
  { refine absurd _ hy_ne,
    simpa [hp_pos_real] using hf_snorm, },
  { simp [hf_snorm], },
end

lemma mem_ℒp_of_finite_measure_preimage (p : ℝ≥0∞) {f : α →ₛ E} (hf : ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞) :
  mem_ℒp f p μ :=
begin
  by_cases hp0 : p = 0,
  { rw [hp0, mem_ℒp_zero_iff_ae_strongly_measurable], exact f.ae_strongly_measurable, },
  by_cases hp_top : p = ∞,
  { rw hp_top, exact mem_ℒp_top f μ, },
  refine ⟨f.ae_strongly_measurable, _⟩,
  rw [snorm_eq_snorm' hp0 hp_top, f.snorm'_eq],
  refine ennreal.rpow_lt_top_of_nonneg (by simp) (ennreal.sum_lt_top_iff.mpr (λ y hy, _)).ne,
  by_cases hy0 : y = 0,
  { simp [hy0, ennreal.to_real_pos hp0 hp_top], },
  { refine ennreal.mul_lt_top _ (hf y hy0).ne,
    exact (ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg ennreal.coe_ne_top).ne },
end

lemma mem_ℒp_iff {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
⟨λ h, measure_preimage_lt_top_of_mem_ℒp hp_pos hp_ne_top f h,
  λ h, mem_ℒp_of_finite_measure_preimage p h⟩

lemma integrable_iff {f : α →ₛ E} : integrable f μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
mem_ℒp_one_iff_integrable.symm.trans $ mem_ℒp_iff one_ne_zero ennreal.coe_ne_top

lemma mem_ℒp_iff_integrable {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ integrable f μ :=
(mem_ℒp_iff hp_pos hp_ne_top).trans integrable_iff.symm

lemma mem_ℒp_iff_fin_meas_supp {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ f.fin_meas_supp μ :=
(mem_ℒp_iff hp_pos hp_ne_top).trans fin_meas_supp_iff.symm

lemma integrable_iff_fin_meas_supp {f : α →ₛ E} : integrable f μ ↔ f.fin_meas_supp μ :=
integrable_iff.trans fin_meas_supp_iff.symm

lemma fin_meas_supp.integrable {f : α →ₛ E} (h : f.fin_meas_supp μ) : integrable f μ :=
integrable_iff_fin_meas_supp.2 h

lemma integrable_pair {f : α →ₛ E} {g : α →ₛ F} :
  integrable f μ → integrable g μ → integrable (pair f g) μ :=
by simpa only [integrable_iff_fin_meas_supp] using fin_meas_supp.pair

lemma mem_ℒp_of_is_finite_measure (f : α →ₛ E) (p : ℝ≥0∞) (μ : measure α) [is_finite_measure μ] :
  mem_ℒp f p μ :=
let ⟨C, hfC⟩ := f.exists_forall_norm_le in
mem_ℒp.of_bound f.ae_strongly_measurable C $ eventually_of_forall hfC

lemma integrable_of_is_finite_measure [is_finite_measure μ] (f : α →ₛ E) : integrable f μ :=
mem_ℒp_one_iff_integrable.mp (f.mem_ℒp_of_is_finite_measure 1 μ)

lemma measure_preimage_lt_top_of_integrable (f : α →ₛ E) (hf : integrable f μ) {x : E}
  (hx : x ≠ 0) :
  μ (f ⁻¹' {x}) < ∞ :=
integrable_iff.mp hf x hx

lemma measure_support_lt_top [has_zero β] (f : α →ₛ β) (hf : ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞) :
  μ (support f) < ∞ :=
begin
  rw support_eq,
  refine (measure_bUnion_finset_le _ _).trans_lt (ennreal.sum_lt_top_iff.mpr (λ y hy, _)),
  rw finset.mem_filter at hy,
  exact hf y hy.2,
end

lemma measure_support_lt_top_of_mem_ℒp (f : α →ₛ E) (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  μ (support f) < ∞ :=
f.measure_support_lt_top ((mem_ℒp_iff hp_ne_zero hp_ne_top).mp hf)

lemma measure_support_lt_top_of_integrable (f : α →ₛ E) (hf : integrable f μ) :
  μ (support f) < ∞ :=
f.measure_support_lt_top (integrable_iff.mp hf)

lemma measure_lt_top_of_mem_ℒp_indicator (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {c : E} (hc : c ≠ 0)
  {s : set α} (hs : measurable_set s)
  (hcs : mem_ℒp ((const α c).piecewise s hs (const α 0)) p μ) :
  μ s < ⊤ :=
begin
  have : function.support (const α c) = set.univ := function.support_const hc,
  simpa only [mem_ℒp_iff_fin_meas_supp hp_pos hp_ne_top, fin_meas_supp_iff_support,
    support_indicator, set.inter_univ, this] using hcs
end

end simple_func_properties

end simple_func

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/
namespace Lp

open ae_eq_fun

variables [measurable_space α] [normed_add_comm_group E] [normed_add_comm_group F] (p : ℝ≥0∞)
  (μ : measure α)

variables (E)

/-- `Lp.simple_func` is a subspace of Lp consisting of equivalence classes of an integrable simple
    function. -/
def simple_func : add_subgroup (Lp E p μ) :=
{ carrier := {f : Lp E p μ |
                ∃ (s : α →ₛ E), (ae_eq_fun.mk s s.ae_strongly_measurable : α →ₘ[μ] E) = f},
  zero_mem' := ⟨0, rfl⟩,
  add_mem' := λ f g ⟨s, hs⟩ ⟨t, ht⟩, ⟨s + t,
      by simp only [←hs, ←ht, ae_eq_fun.mk_add_mk, add_subgroup.coe_add, ae_eq_fun.mk_eq_mk,
        simple_func.coe_add]⟩,
  neg_mem' := λ f ⟨s, hs⟩, ⟨-s,
      by simp only [←hs, ae_eq_fun.neg_mk, simple_func.coe_neg, ae_eq_fun.mk_eq_mk,
        add_subgroup.coe_neg]⟩ }

variables {E p μ}

namespace simple_func

section instances
/-! Simple functions in Lp space form a `normed_space`. -/

@[norm_cast] lemma coe_coe (f : Lp.simple_func E p μ) : ⇑(f : Lp E p μ) = f := rfl

protected lemma eq' {f g : Lp.simple_func E p μ} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
subtype.eq ∘ subtype.eq

/-! Implementation note:  If `Lp.simple_func E p μ` were defined as a `𝕜`-submodule of `Lp E p μ`,
then the next few lemmas, putting a normed `𝕜`-group structure on `Lp.simple_func E p μ`, would be
unnecessary.  But instead, `Lp.simple_func E p μ` is defined as an `add_subgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/

variables [normed_field 𝕜] [normed_space 𝕜 E]

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a `has_smul`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def has_smul : has_smul 𝕜 (Lp.simple_func E p μ) := ⟨λ k f, ⟨k • f,
begin
  rcases f with ⟨f, ⟨s, hs⟩⟩,
  use k • s,
  apply eq.trans (ae_eq_fun.smul_mk k s s.ae_strongly_measurable).symm _,
  rw hs,
  refl,
end ⟩⟩

local attribute [instance] simple_func.has_smul

@[simp, norm_cast] lemma coe_smul (c : 𝕜) (f : Lp.simple_func E p μ) :
  ((c • f : Lp.simple_func E p μ) : Lp E p μ) = c • (f : Lp E p μ) := rfl

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a module. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def module : module 𝕜 (Lp.simple_func E p μ) :=
{ one_smul  := λf, by { ext1, exact one_smul _ _ },
  mul_smul  := λx y f, by { ext1, exact mul_smul _ _ _ },
  smul_add  := λx f g, by { ext1, exact smul_add _ _ _ },
  smul_zero := λx, by { ext1, exact smul_zero _ },
  add_smul  := λx y f, by { ext1, exact add_smul _ _ _ },
  zero_smul := λf, by { ext1, exact zero_smul _ _ } }

local attribute [instance] simple_func.module

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def normed_space [fact (1 ≤ p)] : normed_space 𝕜 (Lp.simple_func E p μ) :=
⟨ λc f, by { rw [add_subgroup.coe_norm, add_subgroup.coe_norm, coe_smul, norm_smul] } ⟩

end instances

local attribute [instance] simple_func.module simple_func.normed_space

section to_Lp

/-- Construct the equivalence class `[f]` of a simple function `f` satisfying `mem_ℒp`. -/
@[reducible] def to_Lp (f : α →ₛ E) (hf : mem_ℒp f p μ) : (Lp.simple_func E p μ) :=
⟨hf.to_Lp f, ⟨f, rfl⟩⟩

lemma to_Lp_eq_to_Lp (f : α →ₛ E) (hf : mem_ℒp f p μ) :
  (to_Lp f hf : Lp E p μ) = hf.to_Lp f := rfl

lemma to_Lp_eq_mk (f : α →ₛ E) (hf : mem_ℒp f p μ) :
  (to_Lp f hf : α →ₘ[μ] E) = ae_eq_fun.mk f f.ae_strongly_measurable := rfl

lemma to_Lp_zero : to_Lp (0 : α →ₛ E) zero_mem_ℒp = (0 : Lp.simple_func E p μ) := rfl

lemma to_Lp_add (f g : α →ₛ E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  to_Lp (f + g) (hf.add hg) = to_Lp f hf + to_Lp g hg := rfl

lemma to_Lp_neg (f : α →ₛ E) (hf : mem_ℒp f p μ) :
  to_Lp (-f) hf.neg = -to_Lp f hf := rfl

lemma to_Lp_sub (f g : α →ₛ E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  to_Lp (f - g) (hf.sub hg) = to_Lp f hf - to_Lp g hg :=
by { simp only [sub_eq_add_neg, ← to_Lp_neg, ← to_Lp_add], refl }

variables [normed_field 𝕜] [normed_space 𝕜 E]

lemma to_Lp_smul (f : α →ₛ E) (hf : mem_ℒp f p μ) (c : 𝕜) :
  to_Lp (c • f) (hf.const_smul c) = c • to_Lp f hf := rfl

lemma norm_to_Lp [fact (1 ≤ p)] (f : α →ₛ E) (hf : mem_ℒp f p μ) :
  ‖to_Lp f hf‖ = ennreal.to_real (snorm f p μ) :=
norm_to_Lp f hf

end to_Lp

section to_simple_func

/-- Find a representative of a `Lp.simple_func`. -/
def to_simple_func (f : Lp.simple_func E p μ) : α →ₛ E := classical.some f.2

/-- `(to_simple_func f)` is measurable. -/
@[measurability]
protected lemma measurable [measurable_space E] (f : Lp.simple_func E p μ) :
  measurable (to_simple_func f) :=
(to_simple_func f).measurable

protected lemma strongly_measurable (f : Lp.simple_func E p μ) :
  strongly_measurable (to_simple_func f) :=
(to_simple_func f).strongly_measurable

@[measurability]
protected lemma ae_measurable [measurable_space E] (f : Lp.simple_func E p μ) :
  ae_measurable (to_simple_func f) μ :=
(simple_func.measurable f).ae_measurable

protected lemma ae_strongly_measurable (f : Lp.simple_func E p μ) :
  ae_strongly_measurable (to_simple_func f) μ :=
(simple_func.strongly_measurable f).ae_strongly_measurable

lemma to_simple_func_eq_to_fun (f : Lp.simple_func E p μ) : to_simple_func f =ᵐ[μ] f :=
show ⇑(to_simple_func f) =ᵐ[μ] ⇑(f : α →ₘ[μ] E),
begin
  convert (ae_eq_fun.coe_fn_mk (to_simple_func f) (to_simple_func f).ae_strongly_measurable).symm
    using 2,
  exact (classical.some_spec f.2).symm,
end

/-- `to_simple_func f` satisfies the predicate `mem_ℒp`. -/
protected lemma mem_ℒp (f : Lp.simple_func E p μ) : mem_ℒp (to_simple_func f) p μ :=
mem_ℒp.ae_eq (to_simple_func_eq_to_fun f).symm $ mem_Lp_iff_mem_ℒp.mp (f : Lp E p μ).2

lemma to_Lp_to_simple_func (f : Lp.simple_func E p μ) :
  to_Lp (to_simple_func f) (simple_func.mem_ℒp f) = f :=
simple_func.eq' (classical.some_spec f.2)

lemma to_simple_func_to_Lp (f : α →ₛ E) (hfi : mem_ℒp f p μ) :
  to_simple_func (to_Lp f hfi) =ᵐ[μ] f :=
by { rw ← ae_eq_fun.mk_eq_mk, exact classical.some_spec (to_Lp f hfi).2 }

variables (E μ)

lemma zero_to_simple_func : to_simple_func (0 : Lp.simple_func E p μ) =ᵐ[μ] 0 :=
begin
  filter_upwards [to_simple_func_eq_to_fun (0 : Lp.simple_func E p μ), Lp.coe_fn_zero E 1 μ]
    with _ h₁ _,
  rwa h₁,
end

variables {E μ}

lemma add_to_simple_func (f g : Lp.simple_func E p μ) :
  to_simple_func (f + g) =ᵐ[μ] to_simple_func f + to_simple_func g :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f + g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, Lp.coe_fn_add (f :  Lp E p μ) g] with _,
  simp only [← coe_coe, add_subgroup.coe_add, pi.add_apply],
  iterate 4 { assume h, rw h, },
end

lemma neg_to_simple_func (f : Lp.simple_func E p μ) :
  to_simple_func (-f) =ᵐ[μ] - to_simple_func f :=
begin
  filter_upwards [to_simple_func_eq_to_fun (-f), to_simple_func_eq_to_fun f,
    Lp.coe_fn_neg (f : Lp E p μ)] with _,
  simp only [pi.neg_apply, add_subgroup.coe_neg, ← coe_coe],
  repeat { assume h, rw h, },
end

lemma sub_to_simple_func (f g : Lp.simple_func E p μ) :
  to_simple_func (f - g) =ᵐ[μ] to_simple_func f - to_simple_func g :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f - g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, Lp.coe_fn_sub (f : Lp E p μ) g] with _,
  simp only [add_subgroup.coe_sub, pi.sub_apply, ← coe_coe],
  repeat { assume h, rw h, },
end

variables [normed_field 𝕜] [normed_space 𝕜 E]

lemma smul_to_simple_func (k : 𝕜) (f : Lp.simple_func E p μ) :
  to_simple_func (k • f) =ᵐ[μ] k • to_simple_func f :=
begin
  filter_upwards [to_simple_func_eq_to_fun (k • f), to_simple_func_eq_to_fun f,
    Lp.coe_fn_smul k (f : Lp E p μ)] with _,
  simp only [pi.smul_apply, coe_smul, ← coe_coe],
  repeat { assume h, rw h, },
end

lemma norm_to_simple_func [fact (1 ≤ p)] (f : Lp.simple_func E p μ) :
  ‖f‖ = ennreal.to_real (snorm (to_simple_func f) p μ) :=
by simpa [to_Lp_to_simple_func] using norm_to_Lp (to_simple_func f) (simple_func.mem_ℒp f)

end to_simple_func

section induction

variables (p)

/-- The characteristic function of a finite-measure measurable set `s`, as an `Lp` simple function.
-/
def indicator_const {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E) :
  Lp.simple_func E p μ :=
to_Lp ((simple_func.const _ c).piecewise s hs (simple_func.const _ 0))
  (mem_ℒp_indicator_const p hs c (or.inr hμs))

variables {p}

@[simp] lemma coe_indicator_const {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E) :
  (↑(indicator_const p hs hμs c) : Lp E p μ) = indicator_const_Lp p hs hμs c :=
rfl

lemma to_simple_func_indicator_const {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E) :
  to_simple_func (indicator_const p hs hμs c)
    =ᵐ[μ] (simple_func.const _ c).piecewise s hs (simple_func.const _ 0) :=
Lp.simple_func.to_simple_func_to_Lp _ _

/-- To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it suffices to show
that the property holds for (multiples of) characteristic functions of finite-measure measurable
sets and is closed under addition (of functions with disjoint support). -/
@[elab_as_eliminator]
protected lemma induction (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {P : Lp.simple_func E p μ → Prop}
  (h_ind : ∀ (c : E) {s : set α} (hs : measurable_set s) (hμs : μ s < ∞),
    P (Lp.simple_func.indicator_const p hs hμs.ne c))
  (h_add : ∀ ⦃f g : α →ₛ E⦄, ∀ hf : mem_ℒp f p μ, ∀ hg : mem_ℒp g p μ,
    disjoint (support f) (support g) → P (Lp.simple_func.to_Lp f hf)
    → P (Lp.simple_func.to_Lp g hg) → P (Lp.simple_func.to_Lp f hf + Lp.simple_func.to_Lp g hg))
  (f : Lp.simple_func E p μ) : P f :=
begin
  suffices : ∀ f : α →ₛ E, ∀ hf : mem_ℒp f p μ, P (to_Lp f hf),
  { rw ← to_Lp_to_simple_func f,
    apply this }, clear f,
  refine simple_func.induction _ _,
  { intros c s hs hf,
    by_cases hc : c = 0,
    { convert h_ind 0 measurable_set.empty (by simp) using 1,
      ext1,
      simp [hc] },
    exact h_ind c hs (simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs hf) },
  { intros f g hfg hf hg hfg',
    obtain ⟨hf', hg'⟩ : mem_ℒp f p μ ∧ mem_ℒp g p μ,
    { exact (mem_ℒp_add_of_disjoint hfg f.strongly_measurable g.strongly_measurable).mp hfg' },
    exact h_add hf' hg' hfg (hf hf') (hg hg') },
end

end induction

section coe_to_Lp

variables [fact (1 ≤ p)]

protected lemma uniform_continuous :
  uniform_continuous (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
uniform_continuous_comap

protected lemma uniform_embedding :
  uniform_embedding (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
uniform_embedding_comap subtype.val_injective

protected lemma uniform_inducing : uniform_inducing (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
simple_func.uniform_embedding.to_uniform_inducing

protected lemma dense_embedding (hp_ne_top : p ≠ ∞) :
  dense_embedding (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
begin
  borelize E,
  apply simple_func.uniform_embedding.dense_embedding,
  assume f,
  rw mem_closure_iff_seq_limit,
  have hfi' : mem_ℒp f p μ := Lp.mem_ℒp f,
  haveI : separable_space (range f ∪ {0} : set E) :=
    (Lp.strongly_measurable f).separable_space_range_union_singleton,
  refine ⟨λ n, ↑(to_Lp (simple_func.approx_on f (Lp.strongly_measurable f).measurable
    (range f ∪ {0}) 0 (by simp) n)
    (simple_func.mem_ℒp_approx_on_range (Lp.strongly_measurable f).measurable hfi' n)),
    λ n, mem_range_self _, _⟩,
  convert simple_func.tendsto_approx_on_range_Lp hp_ne_top (Lp.strongly_measurable f).measurable
    hfi',
  rw to_Lp_coe_fn f (Lp.mem_ℒp f)
end

protected lemma dense_inducing (hp_ne_top : p ≠ ∞) :
  dense_inducing (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
(simple_func.dense_embedding hp_ne_top).to_dense_inducing

protected lemma dense_range (hp_ne_top : p ≠ ∞) :
  dense_range (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
(simple_func.dense_inducing hp_ne_top).dense

variables [normed_field 𝕜] [normed_space 𝕜 E]
variables (α E 𝕜)

/-- The embedding of Lp simple functions into Lp functions, as a continuous linear map. -/
def coe_to_Lp : (Lp.simple_func E p μ) →L[𝕜] (Lp E p μ) :=
{ map_smul' := λk f, rfl,
  cont := Lp.simple_func.uniform_continuous.continuous,
  .. add_subgroup.subtype (Lp.simple_func E p μ) }

variables {α E 𝕜}

end coe_to_Lp

section order

variables {G : Type*} [normed_lattice_add_comm_group G]

lemma coe_fn_le (f g : Lp.simple_func G p μ) : f ≤ᵐ[μ] g ↔ f ≤ g :=
by rw [← subtype.coe_le_coe, ← Lp.coe_fn_le, coe_fn_coe_base', coe_fn_coe_base' g]

instance : covariant_class (Lp.simple_func G p μ) (Lp.simple_func G p μ) (+) (≤) :=
begin
  refine ⟨λ f g₁ g₂ hg₁₂, _⟩,
  rw ← Lp.simple_func.coe_fn_le at hg₁₂ ⊢,
  have h_add_1 : ⇑(f + g₁) =ᵐ[μ] f + g₁, from Lp.coe_fn_add _ _,
  have h_add_2 : ⇑(f + g₂) =ᵐ[μ] f + g₂, from Lp.coe_fn_add _ _,
  filter_upwards [h_add_1, h_add_2, hg₁₂] with _ h1 h2 h3,
  rw [h1, h2, pi.add_apply, pi.add_apply],
  exact add_le_add le_rfl h3,
end

variables (p μ G)
lemma coe_fn_zero : (0 : Lp.simple_func G p μ) =ᵐ[μ] (0 : α → G) := Lp.coe_fn_zero _ _ _
variables{p μ G}

lemma coe_fn_nonneg (f : Lp.simple_func G p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f :=
begin
  rw ← Lp.simple_func.coe_fn_le,
  have h0 : (0 : Lp.simple_func G p μ) =ᵐ[μ] (0 : α → G), from Lp.simple_func.coe_fn_zero p μ G,
  split; intro h; filter_upwards [h, h0] with _ _ h2,
  { rwa h2, },
  { rwa ← h2, },
end

lemma exists_simple_func_nonneg_ae_eq {f : Lp.simple_func G p μ} (hf : 0 ≤ f) :
  ∃ f' : α →ₛ G, 0 ≤ f' ∧ f =ᵐ[μ] f' :=
begin
  rw ← Lp.simple_func.coe_fn_nonneg at hf,
  have hf_ae : 0 ≤ᵐ[μ] (simple_func.to_simple_func f),
    by { filter_upwards [to_simple_func_eq_to_fun f, hf] with _ h1 _, rwa h1 },
  let s := (to_measurable μ {x | ¬ 0 ≤ simple_func.to_simple_func f x})ᶜ,
  have hs_zero : μ sᶜ = 0,
    by { rw [compl_compl, measure_to_measurable], rwa [eventually_le, ae_iff] at hf_ae, },
  have hfs_nonneg : ∀ x ∈ s, 0 ≤ simple_func.to_simple_func f x,
  { intros x hxs,
    rw mem_compl_iff at hxs,
    have hx' : x ∉ {a : α | ¬0 ≤ simple_func.to_simple_func f a},
      from λ h, hxs (subset_to_measurable μ _ h),
    rwa [set.nmem_set_of_iff, not_not] at hx', },
  let f' := simple_func.piecewise s (measurable_set_to_measurable μ _).compl
    (simple_func.to_simple_func f) (simple_func.const α (0 : G)),
  refine ⟨f', λ x, _, _⟩,
  { rw simple_func.piecewise_apply,
    by_cases hxs : x ∈ s,
    { simp only [hxs, hfs_nonneg x hxs, if_true, pi.zero_apply, simple_func.coe_zero], },
    { simp only [hxs, simple_func.const_zero, if_false], }, },
  { rw simple_func.coe_piecewise,
    have : s =ᵐ[μ] univ,
    { rw ae_eq_set,
      simp only [true_and, measure_empty, eq_self_iff_true, diff_univ, ← compl_eq_univ_diff],
      exact hs_zero, },
    refine eventually_eq.trans (to_simple_func_eq_to_fun f).symm _,
    refine eventually_eq.trans _ (piecewise_ae_eq_of_ae_eq_set this.symm),
    simp only [simple_func.const_zero, indicator_univ, piecewise_eq_indicator,
      simple_func.coe_zero], },
end

variables (p μ G)
/-- Coercion from nonnegative simple functions of Lp to nonnegative functions of Lp. -/
def coe_simple_func_nonneg_to_Lp_nonneg :
  {g : Lp.simple_func G p μ // 0 ≤ g} → {g : Lp G p μ // 0 ≤ g} :=
λ g, ⟨g, g.2⟩

lemma dense_range_coe_simple_func_nonneg_to_Lp_nonneg [hp : fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
  dense_range (coe_simple_func_nonneg_to_Lp_nonneg p μ G) :=
begin
  borelize G,
  assume g,
  rw mem_closure_iff_seq_limit,
  have hg_mem_ℒp : mem_ℒp g p μ := Lp.mem_ℒp g,
  have zero_mem : (0 : G) ∈ (range g ∪ {0} : set G) ∩ {y | 0 ≤ y}, by simp only [union_singleton,
    mem_inter_iff, mem_insert_iff, eq_self_iff_true, true_or, mem_set_of_eq, le_refl, and_self],
  haveI : separable_space (((range g ∪ {0}) ∩ {y | 0 ≤ y}) : set G),
  { apply is_separable.separable_space,
    apply is_separable.mono _ (set.inter_subset_left _ _),
    exact (Lp.strongly_measurable (g : Lp G p μ)).is_separable_range.union
      (finite_singleton _).is_separable },
  have g_meas : measurable g := (Lp.strongly_measurable (g : Lp G p μ)).measurable,
  let x := λ n, simple_func.approx_on g g_meas ((range g ∪ {0}) ∩ {y | 0 ≤ y}) 0 zero_mem n,
  have hx_nonneg : ∀ n, 0 ≤ x n,
  { assume n a,
    change x n a ∈ {y : G | 0 ≤ y},
    have A : (range g ∪ {0} : set G) ∩ {y | 0 ≤ y} ⊆ {y | 0 ≤ y} := inter_subset_right _ _,
    apply A,
    exact simple_func.approx_on_mem g_meas _ n a },
  have hx_mem_ℒp : ∀ n, mem_ℒp (x n) p μ,
    from simple_func.mem_ℒp_approx_on _ hg_mem_ℒp _ ⟨ae_strongly_measurable_const, by simp⟩,
  have h_to_Lp := λ n, mem_ℒp.coe_fn_to_Lp (hx_mem_ℒp n),
  have hx_nonneg_Lp : ∀ n, 0 ≤ to_Lp (x n) (hx_mem_ℒp n),
  { intro n,
    rw [← Lp.simple_func.coe_fn_le, coe_fn_coe_base' (simple_func.to_Lp (x n) _),
      Lp.simple_func.to_Lp_eq_to_Lp],
    have h0 := Lp.simple_func.coe_fn_zero p μ G,
    filter_upwards [Lp.simple_func.coe_fn_zero p μ G, h_to_Lp n] with a ha0 ha_to_Lp,
    rw [ha0, ha_to_Lp],
    exact hx_nonneg n a, },
  have hx_tendsto : tendsto (λ (n : ℕ), snorm (x n - g) p μ) at_top (𝓝 0),
  { apply simple_func.tendsto_approx_on_Lp_snorm g_meas zero_mem hp_ne_top,
    { have hg_nonneg : 0 ≤ᵐ[μ] g, from (Lp.coe_fn_nonneg _).mpr g.2,
      refine hg_nonneg.mono (λ a ha, subset_closure _),
      simpa using ha, },
    { simp_rw sub_zero, exact hg_mem_ℒp.snorm_lt_top, }, },
  refine ⟨λ n, (coe_simple_func_nonneg_to_Lp_nonneg p μ G) ⟨to_Lp (x n) (hx_mem_ℒp n),
    hx_nonneg_Lp n⟩, λ n, mem_range_self _, _⟩,
  suffices : tendsto (λ (n : ℕ), ↑(to_Lp (x n) (hx_mem_ℒp n))) at_top (𝓝 (g : Lp G p μ)),
  { rw tendsto_iff_dist_tendsto_zero at this ⊢,
    simp_rw subtype.dist_eq,
    convert this, },
  rw Lp.tendsto_Lp_iff_tendsto_ℒp',
  convert hx_tendsto,
  refine funext (λ n, snorm_congr_ae (eventually_eq.sub _ _)),
  { rw Lp.simple_func.to_Lp_eq_to_Lp,
    exact h_to_Lp n, },
  { rw ← coe_fn_coe_base, },
end

variables {p μ G}

end order

end simple_func

end Lp

variables [measurable_space α] [normed_add_comm_group E] {f : α → E} {p : ℝ≥0∞} {μ : measure α}

/-- To prove something for an arbitrary `Lp` function in a second countable Borel normed group, it
suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in `Lp` for which the property holds is closed.
-/
@[elab_as_eliminator]
lemma Lp.induction [_i : fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (P : Lp E p μ → Prop)
  (h_ind : ∀ (c : E) {s : set α} (hs : measurable_set s) (hμs : μ s < ∞),
      P (Lp.simple_func.indicator_const p hs hμs.ne c))
  (h_add : ∀ ⦃f g⦄, ∀ hf : mem_ℒp f p μ, ∀ hg : mem_ℒp g p μ, disjoint (support f) (support g) →
    P (hf.to_Lp f) → P (hg.to_Lp g) → P ((hf.to_Lp f) + (hg.to_Lp g)))
  (h_closed : is_closed {f : Lp E p μ | P f}) :
  ∀ f : Lp E p μ, P f :=
begin
  refine λ f, (Lp.simple_func.dense_range hp_ne_top).induction_on f h_closed _,
  refine Lp.simple_func.induction (lt_of_lt_of_le zero_lt_one _i.elim).ne' hp_ne_top _ _,
  { exact λ c s, h_ind c },
  { exact λ f g hf hg, h_add hf hg },
end

/-- To prove something for an arbitrary `mem_ℒp` function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `Lᵖ` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_eliminator]
lemma mem_ℒp.induction [_i : fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
  (h_ind : ∀ (c : E) ⦃s⦄, measurable_set s → μ s < ∞ → P (s.indicator (λ _, c)))
  (h_add : ∀ ⦃f g : α → E⦄, disjoint (support f) (support g) → mem_ℒp f p μ → mem_ℒp g p μ →
    P f → P g → P (f + g))
  (h_closed : is_closed {f : Lp E p μ | P f} )
  (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → mem_ℒp f p μ → P f → P g) :
  ∀ ⦃f : α → E⦄ (hf : mem_ℒp f p μ), P f :=
begin
  have : ∀ (f : simple_func α E), mem_ℒp f p μ → P f,
  { refine simple_func.induction _ _,
    { intros c s hs h,
      by_cases hc : c = 0,
      { subst hc, convert h_ind 0 measurable_set.empty (by simp) using 1, ext, simp [const] },
      have hp_pos : p ≠ 0 := (lt_of_lt_of_le zero_lt_one _i.elim).ne',
      exact h_ind c hs (simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs h) },
    { intros f g hfg hf hg int_fg,
      rw [simple_func.coe_add,
        mem_ℒp_add_of_disjoint hfg f.strongly_measurable g.strongly_measurable] at int_fg,
      refine h_add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2) } },
  have : ∀ (f : Lp.simple_func E p μ), P f,
  { intro f,
    exact h_ae (Lp.simple_func.to_simple_func_eq_to_fun f) (Lp.simple_func.mem_ℒp f)
      (this (Lp.simple_func.to_simple_func f) (Lp.simple_func.mem_ℒp f)) },
  have : ∀ (f : Lp E p μ), P f :=
    λ f, (Lp.simple_func.dense_range hp_ne_top).induction_on f h_closed this,
  exact λ f hf, h_ae hf.coe_fn_to_Lp (Lp.mem_ℒp _) (this (hf.to_Lp f)),
end

/-- If a set of ae strongly measurable functions is stable under addition and approximates
characteristic functions in `ℒp`, then it is dense in `ℒp`. -/
lemma mem_ℒp.induction_dense (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
  (h0P : ∀ (c : E) ⦃s : set α⦄, measurable_set s → μ s < ∞ → ∀ {ε : ℝ≥0∞}, ε ≠ 0 →
    (∃ (g : α → E), snorm (g - s.indicator (λ x, c)) p μ ≤ ε ∧ P g))
  (h1P : ∀ f g, P f → P g → P (f + g))
  (h2P : ∀ f, P f → ae_strongly_measurable f μ)
  {f : α → E} (hf : mem_ℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (g : α → E), snorm (f - g) p μ ≤ ε ∧ P g :=
begin
  rcases eq_or_ne p 0 with rfl|hp_pos,
  { rcases h0P (0 : E) measurable_set.empty
      (by simp only [measure_empty, with_top.zero_lt_top]) hε with ⟨g, hg, Pg⟩,
    exact ⟨g, by simp only [snorm_exponent_zero, zero_le'], Pg⟩ },
  have A : ∀ (δ : ℝ≥0∞), δ ≠ 0 → ∃ η, η ≠ 0 ∧ Lp_add_const p * (η + η) ≤ δ,
  { assume δ hδ,
    have : tendsto (λ (η : ℝ≥0∞), Lp_add_const p * (η + η)) (𝓝[>] 0) (𝓝 (Lp_add_const p * (0 + 0))),
      from (ennreal.tendsto.const_mul (tendsto_id.add tendsto_id)
        (or.inr (Lp_add_const_lt_top p).ne)).mono_left nhds_within_le_nhds,
    simp only [add_zero, mul_zero] at this,
    rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhds_within).exists
      with ⟨η, hη, ηpos⟩,
    exact ⟨η, ηpos.ne', hη.le⟩ },
  suffices H : ∀ (f' : α →ₛ E) (δ : ℝ≥0∞) (hδ : δ ≠ 0), mem_ℒp f' p μ →
    ∃ g, snorm (f' - g) p μ ≤ δ ∧ P g,
  { obtain ⟨η, ηpos, hη⟩ : ∃ (η : ℝ≥0∞), η ≠ 0 ∧ Lp_add_const p * (η + η) ≤ ε := A ε hε,
    rcases hf.exists_simple_func_snorm_sub_lt hp_ne_top ηpos with ⟨f', hf', f'_mem⟩,
    rcases H f' η ηpos f'_mem with ⟨g, hg, Pg⟩,
    refine ⟨g, _, Pg⟩,
    calc snorm (f - g) p μ
        = snorm ((f - f') + (f' - g)) p μ : by { congr, abel }
    ... ≤ Lp_add_const p * (snorm (f - f') p μ + snorm (f' - g) p μ) :
        snorm_add_le' (hf.ae_strongly_measurable.sub f'.ae_strongly_measurable)
          (f'.ae_strongly_measurable.sub (h2P g Pg)) p
    ... ≤ Lp_add_const p * (η + η) :
      mul_le_mul_of_nonneg_left (add_le_add hf'.le hg) bot_le
    ... ≤ ε : hη },
  refine simple_func.induction _ _,
  { intros c s hs ε εpos Hs,
    rcases eq_or_ne c 0 with rfl|hc,
    { rcases h0P (0 : E) measurable_set.empty
        (by simp only [measure_empty, with_top.zero_lt_top]) εpos with ⟨g, hg, Pg⟩,
      rw [← snorm_neg, neg_sub] at hg,
      refine ⟨g, _, Pg⟩,
      convert hg,
      ext x,
      simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_zero,
        piecewise_eq_indicator, indicator_zero', pi.zero_apply, indicator_zero] },
    { have : μ s < ∞,
        from (simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs Hs),
      rcases h0P c hs this εpos with ⟨g, hg, Pg⟩,
      rw [← snorm_neg, neg_sub] at hg,
      exact ⟨g, hg, Pg⟩ } },
  { intros f f' hff' hf hf' δ δpos int_ff',
    obtain ⟨η, ηpos, hη⟩ : ∃ (η : ℝ≥0∞), η ≠ 0 ∧ Lp_add_const p * (η + η) ≤ δ := A δ δpos,
    rw [simple_func.coe_add,
      mem_ℒp_add_of_disjoint hff' f.strongly_measurable f'.strongly_measurable] at int_ff',
    rcases hf η ηpos int_ff'.1 with ⟨g, hg, Pg⟩,
    rcases hf' η ηpos int_ff'.2 with ⟨g', hg', Pg'⟩,
    refine ⟨g + g', _, h1P g g' Pg Pg'⟩,
    calc snorm ((f + f') - (g + g')) p μ
        = snorm ((f - g) + (f' - g')) p μ : by { congr, abel }
    ... ≤ Lp_add_const p * (snorm (f - g) p μ + snorm (f' - g') p μ) :
        snorm_add_le' (f.ae_strongly_measurable.sub (h2P g Pg))
          (f'.ae_strongly_measurable.sub (h2P g' Pg')) p
    ... ≤ Lp_add_const p * (η + η) :
      mul_le_mul_of_nonneg_left (add_le_add hg hg') bot_le
    ... ≤ δ : hη },
end

section integrable

notation α ` →₁ₛ[`:25 μ `] ` E := @measure_theory.Lp.simple_func α E _ _ 1 μ

lemma L1.simple_func.to_Lp_one_eq_to_L1 (f : α →ₛ E) (hf : integrable f μ) :
  (Lp.simple_func.to_Lp f (mem_ℒp_one_iff_integrable.2 hf) : α →₁[μ] E) = hf.to_L1 f :=
rfl

protected lemma L1.simple_func.integrable (f : α →₁ₛ[μ] E) :
  integrable (Lp.simple_func.to_simple_func f) μ :=
by { rw ← mem_ℒp_one_iff_integrable, exact (Lp.simple_func.mem_ℒp f) }

/-- To prove something for an arbitrary integrable function in a normed group,
it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `L¹` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_eliminator]
lemma integrable.induction (P : (α → E) → Prop)
  (h_ind : ∀ (c : E) ⦃s⦄, measurable_set s → μ s < ∞ → P (s.indicator (λ _, c)))
  (h_add : ∀ ⦃f g : α → E⦄, disjoint (support f) (support g) → integrable f μ → integrable g μ →
    P f → P g → P (f + g))
  (h_closed : is_closed {f : α →₁[μ] E | P f} )
  (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → integrable f μ → P f → P g) :
  ∀ ⦃f : α → E⦄ (hf : integrable f μ), P f :=
begin
  simp only [← mem_ℒp_one_iff_integrable] at *,
  exact mem_ℒp.induction one_ne_top P h_ind h_add h_closed h_ae
end

end integrable

end measure_theory
