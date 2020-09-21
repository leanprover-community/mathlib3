/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import measure_theory.l1_space

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated,
both pointwise and in `L¹` norm, by a sequence of simple functions.
-/

open set filter topological_space
open_locale classical topological_space
variables {α β ι E : Type*}

namespace measure_theory
open ennreal emetric

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

variables [measurable_space α] [emetric_space α] [opens_measurable_space α]

/-- `nearest_pt e N x` is the index `k` such that `e k` is the nearest point to `x` among the points
`e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then `nearest_pt e N x`
returns the least of their indexes. -/
noncomputable def nearest_pt_ind (e : ℕ → α) : ℕ → α →ₛ ℕ
| 0 := const α 0
| (N + 1) := piecewise (⋂ k ≤ N, {x | edist (e (N + 1)) x < edist (e k) x})
    (is_measurable.Inter $ λ k, is_measurable.Inter_Prop $ λ hk,
      is_measurable_lt measurable_edist_right measurable_edist_right)
    (const α $ N + 1) (nearest_pt_ind N)

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
  { simp [le_zero_iff_eq.1 hk, le_refl] },
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

lemma tendsto_approx_on {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] {x : β} (hx : f x ∈ closure s) :
  tendsto (λ n, approx_on f hf s y₀ h₀ n x) at_top (𝓝 $ f x) :=
begin
  haveI : nonempty s := ⟨⟨y₀, h₀⟩⟩,
  rw [← @subtype.range_coe _ s, ← image_univ, ← dense_seq_dense s] at hx,
  simp only [approx_on, coe_comp],
  refine tendsto_nearest_pt (closure_minimal _ is_closed_closure hx),
  simp only [nat.range_cases_on, closure_union, @range_comp _ _ _ _ coe],
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

-- Actually, we can avoid `second_countable_topology E` if needed
lemma tendsto_approx_on_l1 [measurable_space E] [normed_group E] [opens_measurable_space E]
  [second_countable_topology E] {f : β → E} (hf : measurable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s)
  {μ : measure β} (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : integrable (λ x, f x - y₀) μ) :
  tendsto (λ n, ∫⁻ x, edist (approx_on f hf s y₀ h₀ n x) (f x) ∂μ) at_top (𝓝 0) :=
begin
  simp only [integrable, ← nndist_eq_nnnorm, ← edist_nndist, ← edist_comm y₀] at hi,
  convert tendsto_lintegral_of_dominated_convergence _
    (λ n, (approx_on f hf s y₀ h₀ n).measurable.edist hf)
    (λ n, eventually_of_forall $ λ x, edist_approx_on_le hf h₀ x n) hi
    (hμ.mono $ λ x hx, _),
  show tendsto (λ n, edist _ (f x)) at_top (𝓝 $ edist (f x) (f x)),
    from (tendsto_approx_on hf h₀ hx).edist tendsto_const_nhds,
  simp
end

lemma integrable_approx_on [measurable_space E] [normed_group E] [borel_space E]
  {f : β → E} (hf : measurable f) {s : set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s]
  {μ : measure β} (hi : integrable (λ x, f x - y₀) μ) (hi₀ : integrable (λ x, y₀) μ) (n : ℕ) :
  integrable (approx_on f hf s y₀ h₀ n) μ :=
begin
  suffices : integrable (λ x, approx_on f hf s y₀ h₀ n x - y₀) μ,
  { simpa using this.add (approx_on f hf s y₀ h₀ n - const _ y₀).measurable measurable_const hi₀ },
  simp only [integrable, ← nndist_eq_nnnorm, ← edist_nndist, edist_comm _ y₀] at hi ⊢,
  have : measurable (λ x, edist y₀ (f x)) :=
    (continuous_const.edist continuous_id).measurable.comp hf,
  calc ∫⁻ x, edist y₀ (approx_on f hf s y₀ h₀ n x) ∂μ ≤ ∫⁻ x, edist y₀ (f x) + edist y₀ (f x) ∂μ :
    measure_theory.lintegral_mono (λ x, edist_approx_on_y0_le hf h₀ x n)
  ... = ∫⁻ x, edist y₀ (f x) ∂μ + ∫⁻ x, edist y₀ (f x) ∂μ :
    measure_theory.lintegral_add this this
  ... < ⊤ :
    add_lt_top.2 ⟨hi, hi⟩
end

end simple_func

open simple_func

variables [measurable_space α] [emetric_space β] [measurable_space β] [opens_measurable_space β]
  [normed_group E] [measurable_space E] [second_countable_topology E]

lemma simple_func_sequence_tendsto [opens_measurable_space E] {f : α → E} (hf : measurable f) :
  ∃ (F : ℕ → (α →ₛ E)), ∀ x : α, tendsto (λ n, F n x) at_top (𝓝 (f x)) :=
⟨approx_on f hf univ 0 trivial, λ x, tendsto_approx_on hf _ (by simp)⟩

lemma simple_func_sequence_tendsto' [borel_space E] {μ : measure α} {f : α → E}
  (hfm : measurable f) (hfi : integrable f μ) :
    ∃ (F : ℕ → (α →ₛ E)), (∀n, integrable (F n) μ) ∧
   tendsto (λ n, ∫⁻ x,  nndist (F n x) (f x) ∂μ) at_top (𝓝 0) :=
⟨approx_on f hfm univ 0 trivial, integrable_approx_on _ _ (by simpa) (integrable_zero _ _ _),
  by { simp only [← edist_nndist], exact tendsto_approx_on_l1 _ _ (by simp) (by simpa) }⟩

end measure_theory
