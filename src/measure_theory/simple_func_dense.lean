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

* Pointwise convergence: If `f x ∈ s`, then `measure_theory.simple_func.approx_on f hf s y₀ h₀ n x`
  tends to `f x` as `n` tends to `∞`.
* If `α` is a `normed_group`, `f x` is `measure_theory.integrable`, and `f x ∈ s` for a.e. `x`,
  then `simple_func.approx_on f hf s 0 h₀ n` tends to `f` in `Lᵖ`. The main use case is `s = univ`.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

open set filter topological_space
open_locale classical topological_space nnreal ennreal
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
variables [measurable_space E] [normed_group E] {p : ℝ}

lemma nnnorm_approx_on_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} (h₀ : (0 : E) ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ∥approx_on f hf s 0 h₀ n x - f x∥₊ ≤ ∥f x∥₊ :=
begin
  have := edist_approx_on_le hf h₀ x n,
  simp [edist_nndist, nndist_eq_nnnorm] at this,
  exact_mod_cast this
end

lemma nnnorm_approx_on_y0_le [opens_measurable_space E] {f : β → E} (hf : measurable f)
  {s : set E} {y₀ : E}  (h₀ : y₀ ∈ s) [separable_space s] (x : β) (n : ℕ) :
  ∥approx_on f hf s y₀ h₀ n x - y₀∥₊ ≤ ∥f x - y₀∥₊ + ∥f x - y₀∥₊ :=
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

lemma tendsto_approx_on_Lp_nnnorm  [opens_measurable_space E]
  {f : β → E} (hf : measurable f) {s : set E} (h₀ : (0 : E) ∈ s) [separable_space s] (hp : 0 < p)
  {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : snorm' f p μ < ∞) :
  tendsto (λ n, snorm' (approx_on f hf s 0 h₀ n - f) p μ) at_top (𝓝 0) :=
begin
  suffices : tendsto (λ n, ∫⁻ x, ∥approx_on f hf s 0 h₀ n x - f x∥₊ ^ p ∂μ) at_top (𝓝 0),
  { simp only [snorm'],
    have hp' : 0 < p⁻¹ := _root_.inv_pos.mpr hp,
    convert (ennreal.continuous_at_rpow_const hp').tendsto.comp this;
    simp [hp'] },
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas : ∀ n, measurable (λ x, (∥approx_on f hf s 0 h₀ n x - f x∥₊ : ℝ≥0∞) ^ p),
  { simpa only [← edist_eq_coe_nnnorm_sub] using
      λ n, (approx_on f hf s 0 h₀ n).measurable_bind (λ y x, (edist y (f x)) ^  p)
      (λ y, (measurable_edist_right.comp hf).pow_const p) },
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `λ x, ∥f x∥ ^ p`
  have h_bound : ∀ n,
    (λ x, (∥approx_on f hf s 0 h₀ n x - f x∥₊ : ℝ≥0∞) ^ p) ≤ᵐ[μ] (λ x, ∥f x∥₊ ^ p),
  { exact λ n, eventually_of_forall
      (λ x, rpow_le_rpow (coe_mono (nnnorm_approx_on_le hf h₀ x n)) hp.le) },
  -- (3) The bounding function `λ x, ∥f x∥ ^ p` has finite integral
  have h_fin :  ∫⁻ (a : β), ∥f a∥₊ ^ p ∂μ < ⊤,
  { exact lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hp hi },
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim : ∀ᵐ (a : β) ∂μ,
    tendsto (λ n, (∥approx_on f hf s 0 h₀ n a - f a∥₊ : ℝ≥0∞) ^ p) at_top (𝓝 0),
  { filter_upwards [hμ],
    intros a ha,
    have : tendsto (λ n, (approx_on f hf s 0 h₀ n) a - f a) at_top (𝓝 (f a - f a)),
    { exact (tendsto_approx_on hf h₀ ha).sub tendsto_const_nhds },
    convert ennreal.tendsto_coe.mpr (this.nnnorm.nnrpow tendsto_const_nhds (or.inr hp)),
    { ext1 x,
      rw [ennreal.coe_rpow_of_nonneg _ hp.le] },
    simp [nnreal.zero_rpow hp.ne'] },
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim,
end

-- to avoid assuming `[second_countable_space E]`, we do not make use of the various `mem_ℒp.*`
-- lemmas
lemma snorm'_lt_top_approx_on [borel_space E]
  {f : β → E} (hp : 0 < p) {μ : measure β} (fmeas : measurable f) (hf : snorm' f p μ < ⊤)
  {s : set E} {y₀ : E} (h₀ : y₀ ∈ s)
  [separable_space s] (hi₀ : snorm' (λ x, y₀) p μ < ∞) (n : ℕ) :
  snorm' (approx_on f fmeas s y₀ h₀ n) p μ < ⊤ :=
begin
  -- haveI : has_measurable_sub₂ E := has_continuous_sub.has_measurable_sub₂,
  have approx_meas' : ae_measurable (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) μ,
  { exact (approx_on f fmeas s y₀ h₀ n - const β y₀).ae_measurable },
  have approx_meas : measurable (λ x, (∥approx_on f fmeas s y₀ h₀ n x - y₀∥₊ ^ p : ℝ≥0∞)),
  { simp only [← edist_eq_coe_nnnorm_sub],
    convert (measurable_edist_left.comp (approx_on f fmeas s y₀ h₀ n).measurable).pow_const p },
  -- have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  suffices : snorm' (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) p μ < ⊤,
  { have hfp : mem_ℒp (λ x, y₀) (ennreal.of_real p) μ := ⟨ae_measurable_const, sorry⟩,
    have hafp : mem_ℒp (λ x, approx_on f fmeas s y₀ h₀ n x - y₀) (ennreal.of_real p) μ :=
      ⟨approx_meas', sorry⟩,
    convert snorm_add_lt_top hfp hafp using 1,
    rw snorm_eq_snorm',
    congr' 1,
    ext x,
    simp,
    sorry },
  have hf' : snorm' (λ x, f x - y₀) p μ < ⊤,
  { sorry },
  rw lintegral_rpow_nnnorm_lt_top_iff_snorm'_lt_top hp,
  have h_two : (2 : ℝ≥0∞) = ↑(2 : ℝ≥0) := by norm_num,
  have h_meas : measurable (λ x, (∥f x - y₀∥₊ : ℝ≥0∞) ^ p),
  { simp only [← edist_eq_coe_nnnorm_sub],
    exact (measurable_edist_left.comp fmeas).pow_const p },
    -- (measurable_ennnorm.comp (fmeas.sub measurable_const)).pow_const p,
  have h_le' : ∀ x, ∥approx_on f fmeas s y₀ h₀ n x - y₀∥₊ ^ p ≤ 2 ^ p * ∥f x - y₀∥₊ ^ p,
  { intros x,
    calc ∥approx_on f fmeas s y₀ h₀ n x - y₀∥₊ ^ p ≤ (∥f x - y₀∥₊ + ∥f x - y₀∥₊) ^ p :
      nnreal.rpow_le_rpow (nnnorm_approx_on_y0_le fmeas h₀ x n) hp.le
    ... = (2 * ∥f x - y₀∥₊) ^ p : by { congr' 1, ring }
    ... = 2 ^ p * ∥f x - y₀∥₊ ^ p : nnreal.mul_rpow },
  have h_le : ∀ x, (∥approx_on f fmeas s y₀ h₀ n x - y₀∥₊ : ℝ≥0∞) ^ p ≤ 2 ^ p * ∥f x - y₀∥₊ ^ p,
  { intros x,
    simpa only [h_two, ennreal.coe_rpow_of_nonneg _ hp.le, ennreal.coe_mul]
      using coe_mono (h_le' x) },
  calc
  ∫⁻ x, ∥approx_on f fmeas s y₀ h₀ n x - y₀∥₊ ^ p ∂μ ≤ ∫⁻ x, 2 ^ p * ∥f x - y₀∥₊ ^ p ∂μ :
    measure_theory.lintegral_mono h_le
  ... = 2 ^ p * ∫⁻ x, ∥f x - y₀∥₊ ^ p ∂μ : lintegral_const_mul _ h_meas
  ... < ∞ : ennreal.mul_lt_top _ (lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hp hf'),
  exact rpow_lt_top_of_nonneg hp.le two_ne_top,
end

lemma tendsto_approx_on_univ_Lp_nnnorm [opens_measurable_space E] [second_countable_topology E]
  {f : β → E} (hp : 0 < p) {μ : measure β} (fmeas : measurable f) (hf : snorm' f p μ < ∞) :
  tendsto (λ n, snorm' (approx_on f fmeas univ 0 trivial n - f) p μ) at_top (𝓝 0) :=
tendsto_approx_on_Lp_nnnorm fmeas trivial hp (by simp) hf

lemma snorm'_lt_top_approx_on_univ [borel_space E] [second_countable_topology E]
  {f : β → E} (hp : 0 < p) {μ : measure β} (fmeas : measurable f) (hf : snorm' f p μ < ⊤) (n : ℕ) :
  snorm' (approx_on f fmeas univ 0 trivial n) p μ < ⊤ :=
snorm'_lt_top_approx_on hp fmeas hf _ (integrable_zero _ _ μ) n

end Lp

/-! ### L1 approximation by simple functions -/

section integrable
variables [measurable_space β]
variables [measurable_space E] [normed_group E]

lemma tendsto_approx_on_L1_nnnorm  [opens_measurable_space E]
  {f : β → E} (hf : measurable f) {s : set E} (h₀ : (0 : E) ∈ s) [separable_space s]
  {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : has_finite_integral f μ) :
  tendsto (λ n, ∫⁻ x, ∥approx_on f hf s 0 h₀ n x - f x∥₊ ∂μ) at_top (𝓝 0) :=
by simpa [snorm'] using
  tendsto_approx_on_Lp_nnnorm hf h₀ zero_lt_one hμ (by simpa [snorm'] using hi)

lemma integrable_approx_on [borel_space E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ)
  {s : set E} {y₀ : E} (h₀ : y₀ ∈ s)
  [separable_space s] (hi₀ : integrable (λ x, y₀) μ) (n : ℕ) :
  integrable (approx_on f fmeas s y₀ h₀ n) μ :=
begin
  refine ⟨(approx_on f fmeas s y₀ h₀ n).ae_measurable, _⟩,
  have : snorm' f 1 μ < ⊤,
  { simpa [snorm', has_finite_integral] using hf.2 },
  simpa [snorm', has_finite_integral] using snorm'_lt_top_approx_on zero_lt_one fmeas this h₀ hi₀ n
end

lemma tendsto_approx_on_univ_L1_nnnorm [opens_measurable_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ) :
  tendsto (λ n, ∫⁻ x, ∥approx_on f fmeas univ 0 trivial n x - f x∥₊ ∂μ) at_top (𝓝 0) :=
tendsto_approx_on_L1_nnnorm fmeas trivial (by simp) hf.2

lemma integrable_approx_on_univ [borel_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ) (n : ℕ) :
  integrable (approx_on f fmeas univ 0 trivial n) μ :=
integrable_approx_on fmeas hf _ (integrable_zero _ _ μ) n

lemma tendsto_approx_on_univ_L1 [borel_space E] [second_countable_topology E]
  {f : β → E} {μ : measure β} (fmeas : measurable f) (hf : integrable f μ) :
  tendsto (λ n, (integrable_approx_on_univ fmeas hf n).to_L1 (approx_on f fmeas univ 0 trivial n))
    at_top (𝓝 $ hf.to_L1 f) :=
begin
  rw integrable.tendsto_to_L1_iff_tendsto_lintegral_zero,
  convert tendsto_approx_on_univ_L1_nnnorm fmeas hf
end

end integrable

end simple_func

end measure_theory
