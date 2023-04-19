/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
import measure_theory.integral.lebesgue

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

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

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

open set function filter topological_space ennreal emetric finset
open_locale classical topology ennreal measure_theory big_operators
variables {α β ι E F 𝕜 : Type*}

noncomputable theory

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

/-! ### Pointwise approximation by simple functions -/

variables [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]

/-- `nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearest_pt_ind e N x` returns the least of their indexes. -/
noncomputable def nearest_pt_ind (e : ℕ → α) : ℕ → α →ₛ ℕ
| 0 := const α 0
| (N + 1) := piecewise (⋂ k ≤ N, {x | edist (e (N + 1)) x < edist (e k) x})
    (measurable_set.Inter $ λ k, measurable_set.Inter $ λ hk,
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

lemma edist_approx_on_mono {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] (x : β) {m n : ℕ} (h : m ≤ n) :
  edist (approx_on f hf s y₀ h₀ n x) (f x) ≤ edist (approx_on f hf s y₀ h₀ m x) (f x) :=
begin
  dsimp only [approx_on, coe_comp, (∘)],
  exact edist_nearest_pt_le _ _ ((nearest_pt_ind_le _ _ _).trans h)
end

lemma edist_approx_on_le {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] (x : β) (n : ℕ) :
  edist (approx_on f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
edist_approx_on_mono hf h₀ x (zero_le n)

lemma edist_approx_on_y0_le {f : β → α} (hf : measurable f) {s : set α} {y₀ : α} (h₀ : y₀ ∈ s)
  [separable_space s] (x : β) (n : ℕ) :
  edist y₀ (approx_on f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
calc edist y₀ (approx_on f hf s y₀ h₀ n x) ≤
  edist y₀ (f x) + edist (approx_on f hf s y₀ h₀ n x) (f x) : edist_triangle_right _ _ _
... ≤ edist y₀ (f x) + edist y₀ (f x) : add_le_add_left (edist_approx_on_le hf h₀ x n) _

end simple_func

end measure_theory
