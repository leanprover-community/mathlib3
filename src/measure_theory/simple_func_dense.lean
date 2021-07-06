/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
import measure_theory.integrable_on

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated,
both pointwise and in `Lᵖ` norm, by a sequence of simple functions.

## Main definitions

* `measure_theory.simple_func.nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `simple_func` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `measure_theory.simple_func.approx_on (f : β → α) (hf : measurable f) (s : set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.
* `measure_theory.Lp.simple_func`, the type of `Lp` simple functions (notation: `α →₁ₛ[μ] E`)
* `coe_to_Lp`, the embedding of `Lp.simple_func E p μ` into `Lp E p μ`

## Main results

* `tendsto_approx_on` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `measure_theory.simple_func.approx_on f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.
* `tendsto_approx_on_univ_Lp` (Lᵖ convergence): If `E` is a `normed_group` and `f` is measurable
  and `mem_ℒp` (for `p < ∞`), then the simple functions `simple_func.approx_on f hf s 0 h₀ n` may
  be considered as elements of `Lp E p μ`, and they tend in Lᵖ to `f`.
* `tendsto_approx_on_univ_L1` (L¹ convergence): If `E` is a `normed_group` and `f` is measurable
  and integrable, then the simple functions `simple_func.approx_on f hf s 0 h₀ n` may be considered
  as elements of `Lp E 1 μ`, and they tend in L¹ to `f`.
* `Lp.simple_func.dense_embedding`: the embedding `coe_to_Lp` of the `Lp` simple functions into
  `Lp` is dense.
* `integrable.induction`: to prove a predicate for all elements of `Lp`, it suffices to check that
  it behaves correctly on simple functions in `Lp`.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/

open set function filter topological_space ennreal emetric finset
open_locale classical topological_space ennreal measure_theory big_operators
variables {α β ι E F 𝕜 : Type*}

noncomputable theory

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

/-! ### Pointwise approximation by simple functions -/

section pointwise
variables [measurable_space α] [emetric_space α] [opens_measurable_space α]

/-- `nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearest_pt_ind e N x` returns the least of their indexes. -/
noncomputable def nearest_pt_ind (e : ℕ → α) : ℕ → α →ₛ ℕ
| 0 := const α 0
| (N + 1) := piecewise (⋂ k ≤ N, {x | edist (e (N + 1)) x < edist (e k) x})
    (measurable_set.Inter $ λ k, measurable_set.Inter_Prop $ λ hk,
      measurable_set_lt measurable_edist_right measurable_edist_right)
    (const α $ N + 1) (nearest_pt_ind N)

/-- `nearest_pt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearest_pt e N x` returns the point with the
least possible index. -/
noncomputable def nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
(nearest_pt_ind e N).map e

@[simp] lemma nearest_pt_ind_zero (e : ℕ → α) : nearest_pt_ind e 0 = const α 0 := rfl

@[simp] lemma nearest_pt_zero (e : ℕ → α) : nearest_pt e 0 = const α (e 0) := rfl

lemma nearest_pt_ind_succ (e : ℕ → α) (N : ℕ) (x : α) :
  nearest_pt_ind e (N + 1) x =
    if ∀ k ≤ N, edist (e (N + 1)) x < edist (e k) x
    then N + 1 else nearest_pt_ind e N x :=
by { simp only [nearest_pt_ind, coe_piecewise, set.piecewise], congr, simp }

lemma nearest_pt_ind_le (e : ℕ → α) (N : ℕ) (x : α) : nearest_pt_ind e N x ≤ N :=
begin
  induction N with N ihN, { simp },
  simp only [nearest_pt_ind_succ],
  split_ifs,
  exacts [le_rfl, ihN.trans N.le_succ]
end

lemma edist_nearest_pt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) :
  edist (nearest_pt e N x) x ≤ edist (e k) x :=
begin
  induction N with N ihN generalizing k,
  { simp [nonpos_iff_eq_zero.1 hk, le_refl] },
  { simp only [nearest_pt, nearest_pt_ind_succ, map_apply],
    split_ifs,
    { rcases hk.eq_or_lt with rfl|hk,
      exacts [le_rfl, (h k (nat.lt_succ_iff.1 hk)).le] },
    { push_neg at h,
      rcases h with ⟨l, hlN, hxl⟩,
      rcases hk.eq_or_lt with rfl|hk,
      exacts [(ihN hlN).trans hxl, ihN (nat.lt_succ_iff.1 hk)] } }
end

lemma tendsto_nearest_pt {e : ℕ → α} {x : α} (hx : x ∈ closure (range e)) :
  tendsto (λ N, nearest_pt e N x) at_top (𝓝 x) :=
begin
  refine (at_top_basis.tendsto_iff nhds_basis_eball).2 (λ ε hε, _),
  rcases emetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩,
  rw [edist_comm] at hN,
  exact ⟨N, trivial, λ n hn, (edist_nearest_pt_le e x hn).trans_lt hN⟩
end

variables [measurable_space β] {f : β → α}

/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
noncomputable def approx_on (f : β → α) (hf : measurable f) (s : set α) (y₀ : α) (h₀ : y₀ ∈ s)
  [separable_space s] (n : ℕ) :
  β →ₛ α :=
by haveI : nonempty s := ⟨⟨y₀, h₀⟩⟩;
  exact comp (nearest_pt (λ k, nat.cases_on k y₀ (coe ∘ dense_seq s) : ℕ → α) n) f hf

@[simp] lemma approx_on_zero {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] (x : β) :
  approx_on f hf s y₀ h₀ 0 x = y₀ :=
rfl

lemma approx_on_mem {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] (n : ℕ) (x : β) :
  approx_on f hf s y₀ h₀ n x ∈ s :=
begin
  haveI : nonempty s := ⟨⟨y₀, h₀⟩⟩,
  suffices : ∀ n, (nat.cases_on n y₀ (coe ∘ dense_seq s) : α) ∈ s, { apply this },
  rintro (_|n),
  exacts [h₀, subtype.mem _]
end

@[simp] lemma approx_on_comp {γ : Type*} [measurable_space γ] {f : β → α} (hf : measurable f)
  {g : γ → β} (hg : measurable g) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) :
  approx_on (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approx_on f hf s y₀ h₀ n).comp g hg :=
rfl

lemma tendsto_approx_on {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] {x : β} (hx : f x ∈ closure s) :
  tendsto (λ n, approx_on f hf s y₀ h₀ n x) at_top (𝓝 $ f x) :=
begin
  haveI : nonempty s := ⟨⟨y₀, h₀⟩⟩,
  rw [← @subtype.range_coe _ s, ← image_univ, ← (dense_range_dense_seq s).closure_eq] at hx,
  simp only [approx_on, coe_comp],
  refine tendsto_nearest_pt (closure_minimal _ is_closed_closure hx),
  simp only [nat.range_cases_on, closure_union, range_comp coe],
  exact subset.trans (image_closure_subset_closure_image continuous_subtype_coe)
    (subset_union_right _ _)
end

lemma edist_approx_on_le {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] (x : β) (n : ℕ) :
  edist (approx_on f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
begin
  dsimp only [approx_on, coe_comp, (∘)],
  exact edist_nearest_pt_le _ _ (zero_le _)
end

lemma edist_approx_on_y0_le {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] (x : β) (n : ℕ) :
  edist y₀ (approx_on f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
calc edist y₀ (approx_on f hf s y₀ h₀ n x) ≤
  edist y₀ (f x) + edist (approx_on f hf s y₀ h₀ n x) (f x) : edist_triangle_right _ _ _
... ≤ edist y₀ (f x) + edist y₀ (f x) : add_le_add_left (edist_approx_on_le hf h₀ x n) _

end pointwise

/-! ### Lp approximation by simple functions -/

section Lp
variables [measurable_space β]
variables [measurable_space E] [normed_group E] {q : ℝ} {p : ℝ≥0∞}

lemma nnnorm_approx_on_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ∥approx_on f hf s y₀ h₀ n x - f x∥₊ ≤ ∥f x - y₀∥₊ :=
begin
  have := edist_approx_on_le hf h₀ x n,
  rw edist_comm y₀ at this,
  simp only [edist_nndist, nndist_eq_nnnorm] at this,
  exact_mod_cast this
end

lemma norm_approx_on_y₀_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ∥approx_on f hf s y₀ h₀ n x - y₀∥ ≤ ∥f x - y₀∥ + ∥f x - y₀∥ :=
begin
  have := edist_approx_on_y0_le hf h₀ x n,
  repeat { rw [edist_comm y₀, edist_eq_coe_nnnorm_sub] at this },
  exact_mod_cast this,
end

lemma norm_approx_on_zero_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} (h₀ : (0 : E) ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ∥approx_on f hf s 0 h₀ n x∥ ≤ ∥f x∥ + ∥f x∥ :=
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
  have hp : 0 < p.to_real := to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr hp_zero, hp_ne_top⟩,
  suffices : tendsto (λ n, ∫⁻ x, ∥approx_on f hf s y₀ h₀ n x - f x∥₊ ^ p.to_real ∂μ) at_top (𝓝 0),
  { simp only [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_ne_top],
    convert continuous_rpow_const.continuous_at.tendsto.comp this;
    simp [_root_.inv_pos.mpr hp] },
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas : ∀ n, measurable (λ x, (∥approx_on f hf s y₀ h₀ n x - f x∥₊ : ℝ≥0∞) ^ p.to_real),
  { simpa only [← edist_eq_coe_nnnorm_sub] using
      λ n, (approx_on f hf s y₀ h₀ n).measurable_bind (λ y x, (edist y (f x)) ^ p.to_real)
      (λ y, (measurable_edist_right.comp hf).pow_const p.to_real) },
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `λ x, ∥f x - y₀∥ ^ p.to_real`
  have h_bound : ∀ n, (λ x, (∥approx_on f hf s y₀ h₀ n x - f x∥₊ : ℝ≥0∞) ^ p.to_real)
      ≤ᵐ[μ] (λ x, ∥f x - y₀∥₊ ^ p.to_real),
  { exact λ n, eventually_of_forall
      (λ x, rpow_le_rpow (coe_mono (nnnorm_approx_on_le hf h₀ x n)) to_real_nonneg) },
  -- (3) The bounding function `λ x, ∥f x - y₀∥ ^ p.to_real` has finite integral
  have h_fin :  ∫⁻ (a : β), ∥f a - y₀∥₊ ^ p.to_real ∂μ < ⊤,
  { exact lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_zero hp_ne_top hi },
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim : ∀ᵐ (a : β) ∂μ,
    tendsto (λ n, (∥approx_on f hf s y₀ h₀ n a - f a∥₊ : ℝ≥0∞) ^ p.to_real) at_top (𝓝 0),
  { filter_upwards [hμ],
    intros a ha,
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
  refine ⟨(approx_on f fmeas s y₀ h₀ n).ae_measurable, _⟩,
  suffices : snorm (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) p μ < ⊤,
  { have : mem_ℒp (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approx_on f fmeas s y₀ h₀ n - const β y₀).ae_measurable, this⟩,
    convert snorm_add_lt_top this hi₀,
    ext x,
    simp },
  -- We don't necessarily have `mem_ℒp (λ x, f x - y₀) p μ`, because the `ae_measurable` part
  -- requires `ae_measurable.add`, which requires second-countability
  have hf' : mem_ℒp (λ x, ∥f x - y₀∥) p μ,
  { have h_meas : measurable (λ x, ∥f x - y₀∥),
    { simp only [← dist_eq_norm],
      exact (continuous_id.dist continuous_const).measurable.comp fmeas },
    refine ⟨h_meas.ae_measurable, _⟩,
    rw snorm_norm,
    convert snorm_add_lt_top hf hi₀.neg,
    ext x,
    simp [sub_eq_add_neg] },
  have : ∀ᵐ x ∂μ, ∥approx_on f fmeas s y₀ h₀ n x - y₀∥ ≤ ∥(∥f x - y₀∥ + ∥f x - y₀∥)∥,
  { refine eventually_of_forall _,
    intros x,
    convert norm_approx_on_y₀_le fmeas h₀ x n,
    rw [real.norm_eq_abs, abs_of_nonneg],
    exact add_nonneg (norm_nonneg _) (norm_nonneg _) },
  calc snorm (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) p μ
      ≤ snorm (λ x, ∥f x - y₀∥ + ∥f x - y₀∥) p μ : snorm_mono_ae this
  ... < ⊤ : snorm_add_lt_top hf' hf',
end

lemma tendsto_approx_on_univ_Lp_snorm [opens_measurable_space E] [second_countable_topology E]
  {f : β → E} (hp_ne_top : p ≠ ∞) {μ : measure β} (fmeas : measurable f) (hf : snorm f p μ < ∞) :
  tendsto (λ n, snorm (approx_on f fmeas univ 0 trivial n - f) p μ) at_top (𝓝 0) :=
tendsto_approx_on_Lp_snorm fmeas trivial hp_ne_top (by simp) (by simpa using hf)

lemma mem_ℒp_approx_on_univ [borel_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : mem_ℒp f p μ) (n : ℕ) :
  mem_ℒp (approx_on f fmeas univ 0 trivial n) p μ :=
mem_ℒp_approx_on fmeas hf (mem_univ _) zero_mem_ℒp n

lemma tendsto_approx_on_univ_Lp [borel_space E] [second_countable_topology E]
  {f : β → E} [hp : fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) {μ : measure β} (fmeas : measurable f)
  (hf : mem_ℒp f p μ) :
  tendsto (λ n, (mem_ℒp_approx_on_univ fmeas hf n).to_Lp (approx_on f fmeas univ 0 trivial n))
    at_top (𝓝 (hf.to_Lp f)) :=
by simp [Lp.tendsto_Lp_iff_tendsto_ℒp'', tendsto_approx_on_univ_Lp_snorm hp_ne_top fmeas hf.2]

end Lp

/-! ### L1 approximation by simple functions -/

section integrable
variables [measurable_space β]
variables [measurable_space E] [normed_group E]

lemma tendsto_approx_on_L1_nnnorm [opens_measurable_space E]
  {f : β → E} (hf : measurable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s]
  {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : has_finite_integral (λ x, f x - y₀) μ) :
  tendsto (λ n, ∫⁻ x, ∥approx_on f hf s y₀ h₀ n x - f x∥₊ ∂μ) at_top (𝓝 0) :=
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

lemma tendsto_approx_on_univ_L1_nnnorm [opens_measurable_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ) :
  tendsto (λ n, ∫⁻ x, ∥approx_on f fmeas univ 0 trivial n x - f x∥₊ ∂μ) at_top (𝓝 0) :=
tendsto_approx_on_L1_nnnorm fmeas trivial (by simp) (by simpa using hf.2)

lemma integrable_approx_on_univ [borel_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ) (n : ℕ) :
  integrable (approx_on f fmeas univ 0 trivial n) μ :=
integrable_approx_on fmeas hf _ (integrable_zero _ _ _) n

local attribute [instance] fact_one_le_one_ennreal

lemma tendsto_approx_on_univ_L1 [borel_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ) :
  tendsto (λ n, integrable.to_L1 (approx_on f fmeas univ 0 trivial n)
    (integrable_approx_on_univ fmeas hf n)) at_top (𝓝 $ hf.to_L1 f) :=
tendsto_approx_on_univ_Lp one_ne_top fmeas _

end integrable

section simple_func_properties

variables [measurable_space α]
variables [normed_group E] [measurable_space E] [normed_group F]
variables {μ : measure α} {p : ℝ≥0∞}

/-!
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `μ`:
- `mem_ℒp f 0 μ` and `mem_ℒp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`, `mem_ℒp f p μ ↔ integrable f μ ↔ f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞`.
-/

lemma exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ∥f x∥ ≤ C :=
exists_forall_le (f.map (λ x, ∥x∥))

lemma mem_ℒp_zero (f : α →ₛ E) (μ : measure α) : mem_ℒp f 0 μ :=
mem_ℒp_zero_iff_ae_measurable.mpr f.ae_measurable

lemma mem_ℒp_top (f : α →ₛ E) (μ : measure α) : mem_ℒp f ∞ μ :=
let ⟨C, hfC⟩ := f.exists_forall_norm_le in
mem_ℒp_top_of_bound f.ae_measurable C $ eventually_of_forall hfC

protected lemma snorm'_eq {p : ℝ} (f : α →ₛ F) (μ : measure α) :
  snorm' f p μ = (∑ y in f.range, (nnnorm y : ℝ≥0∞) ^ p * μ (f ⁻¹' {y})) ^ (1/p) :=
have h_map : (λ a, (nnnorm (f a) : ℝ≥0∞) ^ p) = f.map (λ a : F, (nnnorm a : ℝ≥0∞) ^ p), by simp,
by rw [snorm', h_map, lintegral_eq_lintegral, map_lintegral]

lemma measure_preimage_lt_top_of_mem_ℒp  (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) (f : α →ₛ E)
  (hf : mem_ℒp f p μ) (y : E) (hy_ne : y ≠ 0) :
  μ (f ⁻¹' {y}) < ∞ :=
begin
  have hp_pos_real : 0 < p.to_real, from ennreal.to_real_pos_iff.mpr ⟨hp_pos, hp_ne_top⟩,
  have hf_snorm := mem_ℒp.snorm_lt_top hf,
  rw [snorm_eq_snorm' hp_pos.ne.symm hp_ne_top, f.snorm'_eq,
    ← @ennreal.lt_rpow_one_div_iff _ _ (1 / p.to_real) (by simp [hp_pos_real]),
    @ennreal.top_rpow_of_pos (1 / (1 / p.to_real)) (by simp [hp_pos_real]),
    ennreal.sum_lt_top_iff] at hf_snorm,
  by_cases hyf : y ∈ f.range,
  swap,
  { suffices h_empty : f ⁻¹' {y} = ∅,
      by { rw [h_empty, measure_empty], exact ennreal.coe_lt_top, },
    ext1 x,
    rw [set.mem_preimage, set.mem_singleton_iff, mem_empty_eq, iff_false],
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
  { rw [hp0, mem_ℒp_zero_iff_ae_measurable], exact f.ae_measurable, },
  by_cases hp_top : p = ∞,
  { rw hp_top, exact mem_ℒp_top f μ, },
  refine ⟨f.ae_measurable, _⟩,
  rw [snorm_eq_snorm' hp0 hp_top, f.snorm'_eq],
  refine ennreal.rpow_lt_top_of_nonneg (by simp) (ennreal.sum_lt_top_iff.mpr (λ y hy, _)).ne,
  by_cases hy0 : y = 0,
  { simp [hy0, ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) (ne.symm hp0), hp_top⟩], },
  { refine ennreal.mul_lt_top _ (hf y hy0),
    exact ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg ennreal.coe_ne_top, },
end

lemma mem_ℒp_iff {f : α →ₛ E} (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
⟨λ h, measure_preimage_lt_top_of_mem_ℒp hp_pos hp_ne_top f h,
  λ h, mem_ℒp_of_finite_measure_preimage p h⟩

lemma integrable_iff {f : α →ₛ E} : integrable f μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
mem_ℒp_one_iff_integrable.symm.trans $ mem_ℒp_iff ennreal.zero_lt_one ennreal.coe_ne_top

lemma mem_ℒp_iff_integrable {f : α →ₛ E} (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ integrable f μ :=
(mem_ℒp_iff hp_pos hp_ne_top).trans integrable_iff.symm

lemma mem_ℒp_iff_fin_meas_supp {f : α →ₛ E} (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ f.fin_meas_supp μ :=
(mem_ℒp_iff hp_pos hp_ne_top).trans fin_meas_supp_iff.symm

lemma integrable_iff_fin_meas_supp {f : α →ₛ E} : integrable f μ ↔ f.fin_meas_supp μ :=
integrable_iff.trans fin_meas_supp_iff.symm

lemma fin_meas_supp.integrable {f : α →ₛ E} (h : f.fin_meas_supp μ) : integrable f μ :=
integrable_iff_fin_meas_supp.2 h

lemma integrable_pair [measurable_space F] {f : α →ₛ E} {g : α →ₛ F} :
  integrable f μ → integrable g μ → integrable (pair f g) μ :=
by simpa only [integrable_iff_fin_meas_supp] using fin_meas_supp.pair

lemma mem_ℒp_of_finite_measure (f : α →ₛ E) (p : ℝ≥0∞) (μ : measure α) [finite_measure μ] :
  mem_ℒp f p μ :=
let ⟨C, hfC⟩ := f.exists_forall_norm_le in
mem_ℒp.of_bound f.ae_measurable C $ eventually_of_forall hfC

lemma integrable_of_finite_measure [finite_measure μ] (f : α →ₛ E) : integrable f μ :=
mem_ℒp_one_iff_integrable.mp (f.mem_ℒp_of_finite_measure 1 μ)

lemma measure_preimage_lt_top_of_integrable (f : α →ₛ E) (hf : integrable f μ) {x : E}
  (hx : x ≠ 0) :
  μ (f ⁻¹' {x}) < ∞ :=
integrable_iff.mp hf x hx

end simple_func_properties

end simple_func

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/
namespace Lp

open ae_eq_fun

variables
  [measurable_space α]
  [normed_group E] [second_countable_topology E] [measurable_space E] [borel_space E]
  [normed_group F] [second_countable_topology F] [measurable_space F] [borel_space F]
  (p : ℝ≥0∞) [fact (1 ≤ p)] {μ : measure α}

variables (E p μ)

/-- `Lp.simple_func` is a subspace of Lp consisting of equivalence classes of an integrable simple
    function. -/
def simple_func : add_subgroup (Lp E p μ) :=
{ carrier := {f : Lp E p μ | ∃ (s : α →ₛ E), (ae_eq_fun.mk s s.ae_measurable : α →ₘ[μ] E) = f},
  zero_mem' := ⟨0, rfl⟩,
  add_mem' := λ f g ⟨s, hs⟩ ⟨t, ht⟩, ⟨s + t,
      by simp only [←hs, ←ht, mk_add_mk, add_subgroup.coe_add, mk_eq_mk, simple_func.coe_add]⟩,
  neg_mem' := λ f ⟨s, hs⟩, ⟨-s,
      by simp only [←hs, neg_mk, simple_func.coe_neg, mk_eq_mk, add_subgroup.coe_neg]⟩ }

variables {α E p μ}

-- notation α ` →₁ₛ[`:25 μ `] ` E := measure_theory.Lp.simple_func α E μ

namespace simple_func

section instances
/-! Simple functions in Lp space form a `normed_space`. -/

-- instance : has_coe (Lp.simple_func E p μ) (Lp E p μ) := coe_subtype
-- instance : has_coe_to_fun (Lp.simple_func E p μ) := by apply_instance--⟨λ f, α → E, λ f, ⇑(f : Lp E p μ)⟩

@[simp, norm_cast] lemma coe_coe (f : Lp.simple_func E p μ) : ⇑(f : Lp E p μ) = f := rfl
protected lemma eq {f g : Lp.simple_func E p μ} : (f : Lp E p μ) = (g : Lp E p μ) → f = g := subtype.eq
protected lemma eq' {f g : Lp.simple_func E p μ} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
subtype.eq ∘ subtype.eq

@[norm_cast] protected lemma eq_iff {f g : Lp.simple_func E p μ} : (f : Lp E p μ) = g ↔ f = g :=
subtype.ext_iff.symm

@[norm_cast] protected lemma eq_iff' {f g : Lp.simple_func E p μ} : (f : α →ₘ[μ] E) = g ↔ f = g :=
iff.intro (simple_func.eq') (congr_arg _)

/-- Lp simple functions forms a `normed_group`, with the metric being inherited from Lp space,
  i.e., `dist f g = ennreal.to_real (∫⁻ a, edist (f a) (g a)`).
  Not declared as an instance as `α →₁ₛ[μ] β` will only be useful in the construction of the Bochner
  integral. -/
protected def normed_group : normed_group (Lp.simple_func E p μ) := by apply_instance

local attribute [instance] simple_func.normed_group

-- /-- Functions `Lp.simple_func E p μ` form an additive commutative group. -/
-- instance : inhabited (Lp.simple_func E p μ) := ⟨0⟩

@[simp, norm_cast]
lemma coe_zero : ((0 : Lp.simple_func E p μ) : Lp E p μ) = 0 := rfl
@[simp, norm_cast]
lemma coe_add (f g : Lp.simple_func E p μ) : ((f + g : Lp.simple_func E p μ) : Lp E p μ) = f + g := rfl
@[simp, norm_cast]
lemma coe_neg (f : Lp.simple_func E p μ) : ((-f : Lp.simple_func E p μ) : Lp E p μ) = -f := rfl
@[simp, norm_cast]
lemma coe_sub (f g : Lp.simple_func E p μ) : ((f - g : Lp.simple_func E p μ) : Lp E p μ) = f - g := rfl

@[simp] lemma edist_eq (f g : Lp.simple_func E p μ) : edist f g = edist (f : Lp E p μ) (g : Lp E p μ) := rfl
@[simp] lemma dist_eq (f g : Lp.simple_func E p μ) : dist f g = dist (f : Lp E p μ) (g : Lp E p μ) := rfl

lemma norm_eq (f : Lp.simple_func E p μ) : ∥f∥ = ∥(f : Lp E p μ)∥ := rfl

variables [normed_field 𝕜] [normed_space 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜]

/-- Not declared as an instance as `Lp.simple_func E p μ` will only be useful in the construction of the
Bochner integral. -/
protected def has_scalar : has_scalar 𝕜 (Lp.simple_func E p μ) := ⟨λk f, ⟨k • f,
begin
  rcases f with ⟨f, ⟨s, hs⟩⟩,
  use k • s,
  apply eq.trans (smul_mk k s s.ae_measurable).symm _,
  rw hs,
  refl,
end ⟩⟩

local attribute [instance, priority 10000] simple_func.has_scalar

@[simp, norm_cast] lemma coe_smul (c : 𝕜) (f : Lp.simple_func E p μ) :
  ((c • f : Lp.simple_func E p μ) : Lp E p μ) = c • (f : Lp E p μ) := rfl

/-- Not declared as an instance as `Lp.simple_func E p μ` will only be useful in the construction of the
  Bochner integral. -/
protected def module : module 𝕜 (Lp.simple_func E p μ) :=
{ one_smul  := λf, simple_func.eq (by { simp only [coe_smul], exact one_smul _ _ }),
  mul_smul  := λx y f, simple_func.eq (by { simp only [coe_smul], exact mul_smul _ _ _ }),
  smul_add  := λx f g, simple_func.eq (by { simp only [coe_smul], exact smul_add _ _ _ }),
  smul_zero := λx, simple_func.eq (by { simp only [coe_smul], exact smul_zero _ }),
  add_smul  := λx y f, simple_func.eq (by { simp only [coe_smul], exact add_smul _ _ _ }),
  zero_smul := λf, simple_func.eq (by { simp only [coe_smul], exact zero_smul _ _ }) }

local attribute [instance] simple_func.normed_group simple_func.module

/-- Not declared as an instance as `Lp.simple_func E p μ` will only be useful in the construction of the
Bochner integral. -/
protected def normed_space : normed_space 𝕜 (Lp.simple_func E p μ) :=
⟨ λc f, by { rw [norm_eq, norm_eq, coe_smul, norm_smul] } ⟩

end instances

local attribute [instance] simple_func.normed_group simple_func.normed_space

section to_Lp

/-- Construct the equivalence class `[f]` of a simple function `f` satisfying `mem_ℒp`. -/
@[reducible] def to_Lp (f : α →ₛ E) (hf : mem_ℒp f p μ) : (Lp.simple_func E p μ) :=
⟨hf.to_Lp f, ⟨f, rfl⟩⟩

lemma to_Lp_eq_to_Lp (f : α →ₛ E) (hf : mem_ℒp f p μ) :
  (to_Lp f hf : Lp E p μ) = hf.to_Lp f := rfl

lemma to_Lp_eq_mk (f : α →ₛ E) (hf : mem_ℒp f p μ) :
  (to_Lp f hf : α →ₘ[μ] E) = ae_eq_fun.mk f f.ae_measurable := rfl

lemma to_Lp_zero : to_Lp (0 : α →ₛ E) zero_mem_ℒp = (0 : Lp.simple_func E p μ) := rfl

lemma to_Lp_add (f g : α →ₛ E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  to_Lp (f + g) (hf.add hg) = to_Lp f hf + to_Lp g hg := rfl

lemma to_Lp_neg (f : α →ₛ E) (hf : mem_ℒp f p μ) :
  to_Lp (-f) hf.neg = -to_Lp f hf := rfl

lemma to_Lp_sub (f g : α →ₛ E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  to_Lp (f - g) (hf.sub hg) = to_Lp f hf - to_Lp g hg :=
by { simp only [sub_eq_add_neg, ← to_Lp_neg, ← to_Lp_add], refl }

variables [normed_field 𝕜] [normed_space 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜]

lemma to_Lp_smul (f : α →ₛ E) (hf : mem_ℒp f p μ) (c : 𝕜) :
  to_Lp (c • f) (hf.const_smul c) = c • to_Lp f hf := rfl

lemma norm_to_Lp (f : α →ₛ E) (hf : mem_ℒp f p μ) : ∥to_Lp f hf∥ = ennreal.to_real (snorm f p μ) :=
norm_to_Lp f hf

end to_Lp

section to_simple_func

/-- Find a representative of a `Lp.simple_func`. -/
def to_simple_func (f : Lp.simple_func E p μ) : α →ₛ E := classical.some f.2

/-- `(to_simple_func f)` is measurable. -/
@[measurability]
protected lemma measurable (f : Lp.simple_func E p μ) : measurable (to_simple_func f) :=
(to_simple_func f).measurable

@[measurability]
protected lemma ae_measurable (f : Lp.simple_func E p μ) : ae_measurable (to_simple_func f) μ :=
(simple_func.measurable f).ae_measurable

lemma to_simple_func_eq_to_fun (f : Lp.simple_func E p μ) : to_simple_func f =ᵐ[μ] f :=
show ⇑(to_simple_func f) =ᵐ[μ] ⇑(f : α →ₘ[μ] E), by
begin
  convert (ae_eq_fun.coe_fn_mk (to_simple_func f) (simple_func.ae_measurable f)).symm using 2,
  exact (classical.some_spec f.2).symm,
end

/-- `to_simple_func f` satisfies the predicate `mem_ℒp`. -/
protected lemma mem_ℒp (f : Lp.simple_func E p μ) : mem_ℒp (to_simple_func f) p μ :=
mem_ℒp.ae_eq (to_simple_func_eq_to_fun f).symm $ mem_Lp_iff_mem_ℒp.mp (f : Lp E p μ).2

lemma to_Lp_to_simple_func (f : Lp.simple_func E p μ) :
  to_Lp (to_simple_func f) (simple_func.mem_ℒp f) = f :=
by { rw ← simple_func.eq_iff', exact classical.some_spec f.2 }

lemma to_simple_func_to_Lp (f : α →ₛ E) (hfi : mem_ℒp f p μ) :
  to_simple_func (to_Lp f hfi) =ᵐ[μ] f :=
by { rw ← mk_eq_mk, exact classical.some_spec (to_Lp f hfi).2 }

variables (E μ)
lemma zero_to_simple_func : to_simple_func (0 : Lp.simple_func E p μ) =ᵐ[μ] 0 :=
begin
  filter_upwards [to_simple_func_eq_to_fun (0 : Lp.simple_func E p μ), Lp.coe_fn_zero E 1 μ],
  assume a h₁ h₂,
  rwa h₁,
end
variables {E μ}

lemma add_to_simple_func (f g : Lp.simple_func E p μ) :
  to_simple_func (f + g) =ᵐ[μ] to_simple_func f + to_simple_func g :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f + g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, Lp.coe_fn_add (f :  Lp E p μ) g],
  assume a,
  simp only [← coe_coe, coe_add, pi.add_apply],
  iterate 4 { assume h, rw h }
end

lemma neg_to_simple_func (f : Lp.simple_func E p μ) : to_simple_func (-f) =ᵐ[μ] - to_simple_func f :=
begin
  filter_upwards [to_simple_func_eq_to_fun (-f), to_simple_func_eq_to_fun f,
    Lp.coe_fn_neg (f : Lp E p μ)],
  assume a,
  simp only [pi.neg_apply, coe_neg, ← coe_coe],
  repeat { assume h, rw h }
end

lemma sub_to_simple_func (f g : Lp.simple_func E p μ) :
  to_simple_func (f - g) =ᵐ[μ] to_simple_func f - to_simple_func g :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f - g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, Lp.coe_fn_sub (f : Lp E p μ) g],
  assume a,
  simp only [coe_sub, pi.sub_apply, ← coe_coe],
  repeat { assume h, rw h }
end

variables [normed_field 𝕜] [normed_space 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜]

lemma smul_to_simple_func (k : 𝕜) (f : Lp.simple_func E p μ) :
  to_simple_func (k • f) =ᵐ[μ] k • to_simple_func f :=
begin
  filter_upwards [to_simple_func_eq_to_fun (k • f), to_simple_func_eq_to_fun f,
    Lp.coe_fn_smul k (f : Lp E p μ)],
  assume a,
  simp only [pi.smul_apply, coe_smul, ← coe_coe],
  repeat { assume h, rw h }
end

-- lemma lintegral_edist_to_simple_func_lt_top (f g : Lp.simple_func E p μ) :
--   ∫⁻ (x : α), edist (to_simple_func f x) (to_simple_func g x) ∂μ < ∞ :=
-- begin
--   rw lintegral_rw₂ (to_simple_func_eq_to_fun f) (to_simple_func_eq_to_fun g),
--   exact lintegral_edist_lt_top (integrable_coe_fn _) (integrable_coe_fn _)
-- end

-- lemma dist_to_simple_func (f g : Lp.simple_func E p μ) : dist f g =
--   ennreal.to_real (∫⁻ x, edist (to_simple_func f x) (to_simple_func g x) ∂μ) :=
-- begin
--   rw [dist_eq, Lp.dist_def, ennreal.to_real_eq_to_real],
--   { rw lintegral_rw₂, repeat { exact ae_eq_symm (to_simple_func_eq_to_fun _) } },
--   { exact lintegral_edist_lt_top (integrable_coe_fn _) (integrable_coe_fn _) },
--   { exact lintegral_edist_to_simple_func_lt_top _ _ }
-- end

-- lemma norm_to_simple_func (f : Lp.simple_func E p μ) :
--   ∥f∥ = ennreal.to_real (∫⁻ (a : α), nnnorm ((to_simple_func f) a) ∂μ) :=
-- calc ∥f∥ =
--   ennreal.to_real (∫⁻x, edist ((to_simple_func f) x) (to_simple_func (0 : Lp.simple_func E p μ) x) ∂μ) :
-- begin
--   rw [← dist_zero_right, dist_to_simple_func]
-- end
-- ... = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) ((to_simple_func f) x) ∂μ) :
-- begin
--   rw lintegral_nnnorm_eq_lintegral_edist,
--   have : ∫⁻ x, edist ((to_simple_func f) x) ((to_simple_func (0 : Lp.simple_func E p μ)) x) ∂μ =
--     ∫⁻ x, edist ((to_simple_func f) x) 0 ∂μ,
--   { refine lintegral_congr_ae ((zero_to_simple_func E μ).mono (λ a h, _)),
--     rw [h, pi.zero_apply] },
--   rw [ennreal.to_real_eq_to_real],
--   { exact this },
--   { exact lintegral_edist_to_simple_func_lt_top _ _ },
--   { rw ← this, exact lintegral_edist_to_simple_func_lt_top _ _ }
-- end

end to_simple_func

section coe_to_Lp

protected lemma uniform_continuous : uniform_continuous (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
uniform_continuous_comap

protected lemma uniform_embedding : uniform_embedding (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
uniform_embedding_comap subtype.val_injective

protected lemma uniform_inducing : uniform_inducing (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
simple_func.uniform_embedding.to_uniform_inducing

protected lemma dense_embedding (hp_ne_top : p ≠ ⊤) :
  dense_embedding (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
begin
  apply simple_func.uniform_embedding.dense_embedding,
  assume f,
  rw mem_closure_iff_seq_limit,
  have hfi' : mem_ℒp f p μ := Lp.mem_ℒp f,
  refine ⟨λ n, ↑(to_Lp (simple_func.approx_on f (Lp.measurable f) univ 0 trivial n)
    (simple_func.mem_ℒp_approx_on_univ (Lp.measurable f) hfi' n)), λ n, mem_range_self _, _⟩,
  convert simple_func.tendsto_approx_on_univ_Lp hp_ne_top (Lp.measurable f) hfi',
  rw to_Lp_coe_fn f (Lp.mem_ℒp f)
end

protected lemma dense_inducing (hp_ne_top : p ≠ ⊤) :
  dense_inducing (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
(simple_func.dense_embedding hp_ne_top).to_dense_inducing

protected lemma dense_range (hp_ne_top : p ≠ ⊤) :
  dense_range (coe : (Lp.simple_func E p μ) → (Lp E p μ)) :=
(simple_func.dense_inducing hp_ne_top).dense

variables [normed_field 𝕜] [normed_space 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜]

variables (α E 𝕜)

/-- The embedding of Lp simple functions into Lp functions, as a continuous linear map. -/
def coe_to_Lp : (Lp.simple_func E p μ) →L[𝕜] (Lp E p μ) :=
{ to_fun := (coe : (Lp.simple_func E p μ) → (Lp E p μ)),
  map_add' := λf g, rfl,
  map_smul' := λk f, rfl,
  cont := Lp.simple_func.uniform_continuous.continuous, }

variables {α E 𝕜}

end coe_to_Lp

end simple_func

end Lp

variables [measurable_space α] [normed_group E] [measurable_space E] {f g : α → E} {s t : set α}
  {p : ℝ≥0∞} [_i : fact (1 ≤ p)]
  {μ ν : measure α} {l l' : filter α} [borel_space E] [second_countable_topology E]

include _i

/-- To prove something for an arbitrary integrable function in a second countable
Borel normed group, it suffices to show that
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
lemma integrable.induction (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
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
      apply h_ind c hs,
      have hp_pos : 0 < p := lt_of_lt_of_le ennreal.zero_lt_one _i.elim,
      rw simple_func.mem_ℒp_iff hp_pos hp_ne_top at h,
      convert h c hc,
      ext x,
      simp only [simple_func.coe_const, set.mem_preimage, mem_singleton_iff, simple_func.coe_zero,
        indicator_apply_eq_self, piecewise_eq_indicator, simple_func.const_zero,
        simple_func.coe_piecewise, const_apply, hc],
      exact not_not.symm },
    { intros f g hfg hf hg int_fg,
      refine h_add hfg _ _ (hf _) (hg _),
      have := integrable_add,
      sorry } },
      -- rw [simple_func.coe_add, integrable_add hfg f.measurable g.measurable] at int_fg,
      -- refine h_add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2) } },
  have : ∀ (f : Lp.simple_func E p μ), P f,
  { intro f,
    exact h_ae (Lp.simple_func.to_simple_func_eq_to_fun f) (Lp.simple_func.mem_ℒp f)
      (this (Lp.simple_func.to_simple_func f) (Lp.simple_func.mem_ℒp f)) },
  have : ∀ (f : Lp E p μ), P f :=
    λ f, (Lp.simple_func.dense_range hp_ne_top).induction_on f h_closed this,
  exact λ f hf, h_ae hf.coe_fn_to_Lp (Lp.mem_ℒp _) (this (hf.to_Lp f)),
end

end measure_theory
