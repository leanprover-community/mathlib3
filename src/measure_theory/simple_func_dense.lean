/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
import measure_theory.l1_space

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

## TODO

Simple functions are also dense in L^∞ -- prove this.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

open set filter topological_space
open_locale classical topological_space ennreal
variables {α β ι E : Type*}

namespace measure_theory
open ennreal emetric

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

lemma tendsto_approx_on_Lp_nnnorm [opens_measurable_space E]
  {f : β → E} (hf : measurable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s]
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ⊤) {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s)
  (hi : snorm (λ x, f x - y₀) p μ < ∞) :
  tendsto (λ n, snorm (approx_on f hf s y₀ h₀ n - f) p μ) at_top (𝓝 0) :=
begin
  have hp : 0 < p.to_real := to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr hp_ne_zero, hp_ne_top⟩,
  suffices : tendsto (λ n, ∫⁻ x, ∥approx_on f hf s y₀ h₀ n x - f x∥₊ ^ p.to_real ∂μ) at_top (𝓝 0),
  { simp only [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top],
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
  { exact lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_ne_zero hp_ne_top hi },
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
  {f : β → E} {μ : measure β} (fmeas : measurable f)
  (hf : mem_ℒp f p μ) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s]
  (hi₀ : mem_ℒp (λ x, y₀) p μ) (n : ℕ) :
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

lemma tendsto_approx_on_univ_Lp_nnnorm [opens_measurable_space E] [second_countable_topology E]
  {f : β → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ⊤) {μ : measure β} (fmeas : measurable f)
  (hf : snorm f p μ < ∞) :
  tendsto (λ n, snorm (approx_on f fmeas univ 0 trivial n - f) p μ) at_top (𝓝 0) :=
tendsto_approx_on_Lp_nnnorm fmeas trivial hp_ne_zero hp_ne_top (by simp) (by simpa using hf)

lemma mem_ℒp_approx_on_univ [borel_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : mem_ℒp f p μ) (n : ℕ) :
  mem_ℒp (approx_on f fmeas univ 0 trivial n) p μ :=
mem_ℒp_approx_on fmeas hf (mem_univ _) zero_mem_ℒp n

lemma tendsto_approx_on_univ_Lp [borel_space E] [second_countable_topology E]
  {f : β → E} [hp : fact (1 ≤ p)] (hp_ne_top : p ≠ ⊤) {μ : measure β} (fmeas : measurable f)
  (hf : mem_ℒp f p μ) :
  tendsto (λ n, (mem_ℒp_approx_on_univ fmeas hf n).to_Lp (approx_on f fmeas univ 0 trivial n))
    at_top (𝓝 (hf.to_Lp f)) :=
begin
  rw Lp.tendsto_Lp_iff_tendsto_ℒp'',
  have hp_ne_zero : p ≠ 0 := (lt_of_lt_of_le ennreal.zero_lt_one hp.elim).ne',
  convert tendsto_approx_on_univ_Lp_nnnorm hp_ne_zero hp_ne_top fmeas hf.2
end

end Lp

/-! ### L1 approximation by simple functions -/

section integrable
variables [measurable_space β]
variables [measurable_space E] [normed_group E]

lemma tendsto_approx_on_L1_nnnorm [opens_measurable_space E]
  {f : β → E} (hf : measurable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s]
  {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : has_finite_integral (λ x, f x - y₀) μ) :
  tendsto (λ n, ∫⁻ x, ∥approx_on f hf s y₀ h₀ n x - f x∥₊ ∂μ) at_top (𝓝 0) :=
by simpa [snorm_one_eq_lintegral_nnnorm] using tendsto_approx_on_Lp_nnnorm hf h₀ one_ne_zero
  one_ne_top hμ (by simpa [snorm_one_eq_lintegral_nnnorm] using hi)

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

end simple_func

end measure_theory
