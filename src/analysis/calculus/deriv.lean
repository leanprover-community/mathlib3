/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel

The Fréchet derivative.

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `has_fderiv_within_at f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_within_at f f' x univ`

The derivative is defined in terms of the `is_o` relation, but also
characterized in terms of the `tendsto` relation.

We also introduce predicates `differentiable_within_at 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `differentiable_at 𝕜 f x`,
`differentiable_on 𝕜 f s` and `differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderiv_within 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `unique_diff_within_at s x` and
`unique_diff_on s`, defined in `tangent_cone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

In addition to the definition and basic properties of the derivative, this file contains the
usual formulas (and existence assertions) for the derivative of
* constants
* the identity
* bounded linear maps
* bounded bilinear maps
* sum of two functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
* multiplication of a function by a scalar function
* multiplication of two scalar functions
* composition of functions (the chain rule)

-/

import analysis.asymptotics analysis.calculus.tangent_cone

open filter asymptotics continuous_linear_map set

noncomputable theory
local attribute [instance, priority 10] classical.decidable_inhabited classical.prop_decidable

set_option class.instance_max_depth 90

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space 𝕜 G]

def has_fderiv_at_filter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : filter E) :=
is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L

def has_fderiv_within_at (f : E → F) (f' : E →L[𝕜] F) (s : set E) (x : E) :=
has_fderiv_at_filter f f' x (nhds_within x s)

def has_fderiv_at (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
has_fderiv_at_filter f f' x (nhds x)

variables (𝕜)

def differentiable_within_at (f : E → F) (s : set E) (x : E) :=
∃f' : E →L[𝕜] F, has_fderiv_within_at f f' s x

def differentiable_at (f : E → F) (x : E) :=
∃f' : E →L[𝕜] F, has_fderiv_at f f' x

def fderiv_within (f : E → F) (s : set E) (x : E) : E →L[𝕜] F :=
if h : ∃f', has_fderiv_within_at f f' s x then classical.some h else 0

def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
if h : ∃f', has_fderiv_at f f' x then classical.some h else 0

def differentiable_on (f : E → F) (s : set E) :=
∀x ∈ s, differentiable_within_at 𝕜 f s x

def differentiable (f : E → F) :=
∀x, differentiable_at 𝕜 f x

variables {𝕜}
variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}


section derivative_uniqueness
/- In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `unique_diff_within_at` and `unique_diff_on` indeed imply the
uniqueness of the derivative. -/

/-- `unique_diff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem unique_diff_within_at.eq (H : unique_diff_within_at 𝕜 s x)
  (h : has_fderiv_within_at f f' s x) (h₁ : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
begin
  have A : ∀y ∈ tangent_cone_at 𝕜 s x, f' y = f₁' y,
  { assume y hy,
    rcases hy with ⟨c, d, hd, hc, ylim⟩,
    have at_top_is_finer : at_top ≤ comap (λ (n : ℕ), x + d n) (nhds_within (x + 0) s),
    { rw [←tendsto_iff_comap, nhds_within, tendsto_inf],
      split,
      { apply tendsto_add tendsto_const_nhds (tangent_cone_at.lim_zero hc ylim) },
      { rwa tendsto_principal } },
    rw add_zero at at_top_is_finer,
    have : is_o (λ y, f₁' (y - x) - f' (y - x)) (λ y, y - x) (nhds_within x s),
      by simpa using h.sub h₁,
    have : is_o (λ n:ℕ, f₁' ((x + d n) - x) - f' ((x + d n) - x)) (λ n, (x + d n)  - x)
      ((nhds_within x s).comap (λn, x+ d n)) := is_o.comp this _,
    have L1 : is_o (λ n:ℕ, f₁' (d n) - f' (d n)) d
      ((nhds_within x s).comap (λn, x + d n)) := by simpa using this,
    have L2 : is_o (λn:ℕ, f₁' (d n) - f' (d n)) d at_top :=
      is_o.mono at_top_is_finer L1,
    have L3 : is_o (λn:ℕ, c n • (f₁' (d n) - f' (d n))) (λn, c n • d n) at_top :=
      is_o_smul L2,
    have L4 : is_o (λn:ℕ, c n • (f₁' (d n) - f' (d n))) (λn, (1:ℝ)) at_top :=
      L3.trans_is_O (is_O_one_of_tendsto ylim),
    have L : tendsto (λn:ℕ, c n • (f₁' (d n) - f' (d n))) at_top (nhds 0) :=
      is_o_one_iff.1 L4,
    have L' : tendsto (λ (n : ℕ), c n • (f₁' (d n) - f' (d n))) at_top (nhds (f₁' y - f' y)),
    { simp only [smul_sub, (continuous_linear_map.map_smul _ _ _).symm],
      apply tendsto_sub ((f₁'.continuous.tendsto _).comp ylim) ((f'.continuous.tendsto _).comp ylim) },
    have : f₁' y - f' y = 0 := tendsto_nhds_unique (by simp) L' L,
    exact (sub_eq_zero_iff_eq.1 this).symm },
  have B : ∀y ∈ submodule.span 𝕜 (tangent_cone_at 𝕜 s x), f' y = f₁' y,
  { assume y hy,
    apply submodule.span_induction hy,
    { exact λy hy, A y hy },
    { simp only [continuous_linear_map.map_zero] },
    { simp {contextual := tt} },
    { simp {contextual := tt} } },
  have C : ∀y ∈ closure ((submodule.span 𝕜 (tangent_cone_at 𝕜 s x)) : set E), f' y = f₁' y,
  { assume y hy,
    let K := {y | f' y = f₁' y},
    have : (submodule.span 𝕜 (tangent_cone_at 𝕜 s x) : set E) ⊆ K := B,
    have : closure (submodule.span 𝕜 (tangent_cone_at 𝕜 s x) : set E) ⊆ closure K :=
      closure_mono this,
    have : y ∈ closure K := this hy,
    rwa closure_eq_of_is_closed (is_closed_eq f'.continuous f₁'.continuous) at this },
  rw H.1 at C,
  ext y,
  exact C y (mem_univ _)
end

theorem unique_diff_on.eq (H : unique_diff_on 𝕜 s) (hx : x ∈ s)
  (h : has_fderiv_within_at f f' s x) (h₁ : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
unique_diff_within_at.eq (H x hx) h h₁

end derivative_uniqueness

/- Basic properties of the derivative -/
section fderiv_properties

theorem has_fderiv_at_filter_iff_tendsto :
  has_fderiv_at_filter f f' x L ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) L (nhds 0) :=
have h : ∀ x', ∥x' - x∥ = 0 → ∥f x' - f x - f' (x' - x)∥ = 0, from λ x' hx',
  by { rw [sub_eq_zero.1 ((norm_eq_zero (x' - x)).1 hx')], simp },
begin
  unfold has_fderiv_at_filter,
  rw [←is_o_norm_left, ←is_o_norm_right, is_o_iff_tendsto h],
  exact tendsto.congr'r (λ _, div_eq_inv_mul),
end

theorem has_fderiv_within_at_iff_tendsto : has_fderiv_within_at f f' s x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds_within x s) (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_tendsto : has_fderiv_at f f' x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds x) (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_filter.mono (h : has_fderiv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_fderiv_at_filter f f' x L₁ :=
is_o.mono hst h

theorem has_fderiv_within_at.mono (h : has_fderiv_within_at f f' t x) (hst : s ⊆ t) :
  has_fderiv_within_at f f' s x :=
h.mono (nhds_within_mono _ hst)

theorem has_fderiv_at.has_fderiv_at_filter (h : has_fderiv_at f f' x) (hL : L ≤ nhds x) :
  has_fderiv_at_filter f f' x L :=
h.mono hL

theorem has_fderiv_at.has_fderiv_within_at
  (h : has_fderiv_at f f' x) : has_fderiv_within_at f f' s x :=
h.has_fderiv_at_filter lattice.inf_le_left

lemma has_fderiv_within_at.differentiable_within_at (h : has_fderiv_within_at f f' s x) :
  differentiable_within_at 𝕜 f s x :=
⟨f', h⟩

lemma has_fderiv_at.differentiable_at (h : has_fderiv_at f f' x) : differentiable_at 𝕜 f x :=
⟨f', h⟩

@[simp] lemma has_fderiv_within_at_univ :
  has_fderiv_within_at f f' univ x ↔ has_fderiv_at f f' x :=
by { simp only [has_fderiv_within_at, nhds_within_univ], refl }

theorem has_fderiv_at_unique
  (h₀ : has_fderiv_at f f₀' x) (h₁ : has_fderiv_at f f₁' x) : f₀' = f₁' :=
begin
  rw ← has_fderiv_within_at_univ at h₀ h₁,
  exact unique_diff_within_at_univ.eq h₀ h₁
end

lemma has_fderiv_within_at_inter' (h : t ∈ nhds_within x s) :
  has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
by simp [has_fderiv_within_at, nhds_within_restrict'' s h]

lemma has_fderiv_within_at_inter (h : t ∈ nhds x) :
  has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
by simp [has_fderiv_within_at, nhds_within_restrict' s h]

lemma differentiable_within_at.has_fderiv_within_at (h : differentiable_within_at 𝕜 f s x) :
  has_fderiv_within_at f (fderiv_within 𝕜 f s x) s x :=
begin
  dunfold fderiv_within,
  dunfold differentiable_within_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma differentiable_at.has_fderiv_at (h : differentiable_at 𝕜 f x) :
  has_fderiv_at f (fderiv 𝕜 f x) x :=
begin
  dunfold fderiv,
  dunfold differentiable_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma has_fderiv_at.fderiv (h : has_fderiv_at f f' x) : fderiv 𝕜 f x = f' :=
by { ext, rw has_fderiv_at_unique h h.differentiable_at.has_fderiv_at }

lemma has_fderiv_within_at.fderiv_within
  (h : has_fderiv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f s x = f' :=
by { ext, rw hxs.eq h h.differentiable_within_at.has_fderiv_within_at }

lemma differentiable_within_at.mono (h : differentiable_within_at 𝕜 f t x) (st : s ⊆ t) :
  differentiable_within_at 𝕜 f s x :=
begin
  rcases h with ⟨f', hf'⟩,
  exact ⟨f', hf'.mono st⟩
end

lemma differentiable_within_at_univ :
  differentiable_within_at 𝕜 f univ x ↔ differentiable_at 𝕜 f x :=
begin
  simp [differentiable_within_at, has_fderiv_within_at, nhds_within_univ],
  refl
end

lemma differentiable_within_at_inter (ht : t ∈ nhds x) :
  differentiable_within_at 𝕜 f (s ∩ t) x ↔ differentiable_within_at 𝕜 f s x :=
by simp only [differentiable_within_at, has_fderiv_within_at, has_fderiv_at_filter,
    nhds_within_restrict' s ht]

lemma differentiable_at.differentiable_within_at
  (h : differentiable_at 𝕜 f x) : differentiable_within_at 𝕜 f s x :=
(differentiable_within_at_univ.2 h).mono (subset_univ _)

lemma differentiable_within_at.differentiable_at
  (h : differentiable_within_at 𝕜 f s x) (hs : s ∈ nhds x) : differentiable_at 𝕜 f x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, differentiable_within_at_inter hs, differentiable_within_at_univ] at h
end

lemma differentiable.fderiv_within
  (h : differentiable_at 𝕜 f x) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
begin
  apply has_fderiv_within_at.fderiv_within _ hxs,
  exact h.has_fderiv_at.has_fderiv_within_at
end

lemma differentiable_on.mono (h : differentiable_on 𝕜 f t) (st : s ⊆ t) :
  differentiable_on 𝕜 f s :=
λx hx, (h x (st hx)).mono st

lemma differentiable_on_univ :
  differentiable_on 𝕜 f univ ↔ differentiable 𝕜 f :=
by { simp [differentiable_on, differentiable_within_at_univ], refl }

lemma differentiable.differentiable_on (h : differentiable 𝕜 f) : differentiable_on 𝕜 f s :=
(differentiable_on_univ.2 h).mono (subset_univ _)

lemma differentiable_on_of_locally_differentiable_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ differentiable_on 𝕜 f (s ∩ u)) : differentiable_on 𝕜 f s :=
begin
  assume x xs,
  rcases h x xs with ⟨t, t_open, xt, ht⟩,
  exact (differentiable_within_at_inter (mem_nhds_sets t_open xt)).1 (ht x ⟨xs, xt⟩)
end

lemma fderiv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
((differentiable_within_at.has_fderiv_within_at h).mono st).fderiv_within ht

@[simp] lemma fderiv_within_univ : fderiv_within 𝕜 f univ = fderiv 𝕜 f :=
begin
  ext x : 1,
  by_cases h : differentiable_at 𝕜 f x,
  { apply has_fderiv_within_at.fderiv_within _ (is_open_univ.unique_diff_within_at (mem_univ _)),
    rw has_fderiv_within_at_univ,
    apply h.has_fderiv_at },
  { have : fderiv 𝕜 f x = 0,
      by { unfold differentiable_at at h, simp [fderiv, h] },
    rw this,
    have : ¬(differentiable_within_at 𝕜 f univ x), by rwa differentiable_within_at_univ,
    unfold differentiable_within_at at this,
    simp [fderiv_within, this, -has_fderiv_within_at_univ] }
end

lemma fderiv_within_inter (ht : t ∈ nhds x) (hs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f (s ∩ t) x = fderiv_within 𝕜 f s x :=
begin
  by_cases h : differentiable_within_at 𝕜 f (s ∩ t) x,
  { apply fderiv_within_subset (inter_subset_left _ _) _ ((differentiable_within_at_inter ht).1 h),
    apply hs.inter ht },
  { have : fderiv_within 𝕜 f (s ∩ t) x = 0,
      by { unfold differentiable_within_at at h, simp [fderiv_within, h] },
    rw this,
    rw differentiable_within_at_inter ht at h,
    have : fderiv_within 𝕜 f s x = 0,
      by { unfold differentiable_within_at at h, simp [fderiv_within, h] },
    rw this }
end

end fderiv_properties

/- Congr -/
section congr

theorem has_fderiv_at_filter_congr_of_mem_sets
  (hx : f₀ x = f₁ x) (h₀ : {x | f₀ x = f₁ x} ∈ L) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter f₀ f₀' x L ↔ has_fderiv_at_filter f₁ f₁' x L :=
by { rw (ext h₁), exact is_o_congr
  (by filter_upwards [h₀] λ x (h : _ = _), by simp [h, hx])
  (univ_mem_sets' $ λ _, rfl) }

lemma has_fderiv_at_filter.congr_of_mem_sets (h : has_fderiv_at_filter f f' x L)
  (hL : {x | f₁ x = f x} ∈ L) (hx : f₁ x = f x) : has_fderiv_at_filter f₁ f' x L :=
begin
  apply (has_fderiv_at_filter_congr_of_mem_sets hx hL _).2 h,
  exact λx, rfl
end

lemma has_fderiv_within_at.congr_mono (h : has_fderiv_within_at f f' s x) (ht : ∀x ∈ t, f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_fderiv_within_at f₁ f' t x :=
has_fderiv_at_filter.congr_of_mem_sets (h.mono h₁) (filter.mem_inf_sets_of_right ht) hx

lemma has_fderiv_within_at.congr_of_mem_nhds_within (h : has_fderiv_within_at f f' s x)
  (h₁ : {y | f₁ y = f y} ∈ nhds_within x s) (hx : f₁ x = f x) : has_fderiv_within_at f₁ f' s x :=
has_fderiv_at_filter.congr_of_mem_sets h h₁ hx

lemma has_fderiv_at.congr_of_mem_nhds (h : has_fderiv_at f f' x)
  (h₁ : {y | f₁ y = f y} ∈ nhds x) : has_fderiv_at f₁ f' x :=
has_fderiv_at_filter.congr_of_mem_sets h h₁ (mem_of_nhds h₁ : _)

lemma differentiable_within_at.congr_mono (h : differentiable_within_at 𝕜 f s x)
  (ht : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : differentiable_within_at 𝕜 f₁ t x :=
(has_fderiv_within_at.congr_mono h.has_fderiv_within_at ht hx h₁).differentiable_within_at

lemma differentiable_within_at.congr_of_mem_nhds_within
  (h : differentiable_within_at 𝕜 f s x) (h₁ : {y | f₁ y = f y} ∈ nhds_within x s)
  (hx : f₁ x = f x) : differentiable_within_at 𝕜 f₁ s x :=
(h.has_fderiv_within_at.congr_of_mem_nhds_within h₁ hx).differentiable_within_at

lemma differentiable_on.congr_mono (h : differentiable_on 𝕜 f s) (h' : ∀x ∈ t, f₁ x = f x)
  (h₁ : t ⊆ s) : differentiable_on 𝕜 f₁ t :=
λ x hx, (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

lemma differentiable_at.congr_of_mem_nhds (h : differentiable_at 𝕜 f x)
  (hL : {y | f₁ y = f y} ∈ nhds x) : differentiable_at 𝕜 f₁ x :=
has_fderiv_at.differentiable_at (has_fderiv_at_filter.congr_of_mem_sets h.has_fderiv_at hL (mem_of_nhds hL : _))

lemma differentiable_within_at.fderiv_within_congr_mono (h : differentiable_within_at 𝕜 f s x)
  (hs : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : unique_diff_within_at 𝕜 t x) (h₁ : t ⊆ s) :
  fderiv_within 𝕜 f₁ t x = fderiv_within 𝕜 f s x :=
(has_fderiv_within_at.congr_mono h.has_fderiv_within_at hs hx h₁).fderiv_within hxt

lemma fderiv_within_congr_of_mem_nhds_within (hs : unique_diff_within_at 𝕜 s x)
  (hL : {y | f₁ y = f y} ∈ nhds_within x s) (hx : f₁ x = f x) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
begin
  by_cases h : differentiable_within_at 𝕜 f s x ∨ differentiable_within_at 𝕜 f₁ s x,
  { cases h,
    { apply has_fderiv_within_at.fderiv_within _ hs,
      exact has_fderiv_at_filter.congr_of_mem_sets h.has_fderiv_within_at hL hx },
    { symmetry,
      apply has_fderiv_within_at.fderiv_within _ hs,
      apply has_fderiv_at_filter.congr_of_mem_sets h.has_fderiv_within_at _ hx.symm,
      convert hL,
      ext y,
      exact eq_comm } },
  { push_neg at h,
    have A : fderiv_within 𝕜 f s x = 0,
      by { unfold differentiable_within_at at h, simp [fderiv_within, h] },
    have A₁ : fderiv_within 𝕜 f₁ s x = 0,
      by { unfold differentiable_within_at at h, simp [fderiv_within, h] },
    rw [A, A₁] }
end

lemma fderiv_within_congr (hs : unique_diff_within_at 𝕜 s x)
  (hL : ∀y∈s, f₁ y = f y) (hx : f₁ x = f x) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
begin
  apply fderiv_within_congr_of_mem_nhds_within hs _ hx,
  apply mem_sets_of_superset self_mem_nhds_within,
  exact hL
end

lemma fderiv_congr_of_mem_nhds (hL : {y | f₁ y = f y} ∈ nhds x) :
  fderiv 𝕜 f₁ x = fderiv 𝕜 f x :=
begin
  have A : f₁ x = f x := (mem_of_nhds hL : _),
  rw [← fderiv_within_univ, ← fderiv_within_univ],
  rw ← nhds_within_univ at hL,
  exact fderiv_within_congr_of_mem_nhds_within unique_diff_within_at_univ hL A
end

end congr

/- id -/
section id

theorem has_fderiv_at_filter_id (x : E) (L : filter E) :
  has_fderiv_at_filter id (id : E →L[𝕜] E) x L :=
(is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_within_at_id (x : E) (s : set E) :
  has_fderiv_within_at id (id : E →L[𝕜] E) s x :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_id (x : E) : has_fderiv_at id (id : E →L[𝕜] E) x :=
has_fderiv_at_filter_id _ _

lemma differentiable_at_id : differentiable_at 𝕜 id x :=
(has_fderiv_at_id x).differentiable_at

lemma differentiable_within_at_id : differentiable_within_at 𝕜 id s x :=
differentiable_at_id.differentiable_within_at

lemma differentiable_id : differentiable 𝕜 (id : E → E) :=
λx, differentiable_at_id

lemma differentiable_on_id : differentiable_on 𝕜 id s :=
differentiable_id.differentiable_on

lemma fderiv_id : fderiv 𝕜 id x = id :=
has_fderiv_at.fderiv (has_fderiv_at_id x)

lemma fderiv_within_id (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 id s x = id :=
begin
  rw differentiable.fderiv_within (differentiable_at_id) hxs,
  exact fderiv_id
end

end id

/- constants -/
section const

theorem has_fderiv_at_filter_const (c : F) (x : E) (L : filter E) :
  has_fderiv_at_filter (λ x, c) (0 : E →L[𝕜] F) x L :=
(is_o_zero _ _).congr_left $ λ _, by simp only [zero_apply, sub_self]

theorem has_fderiv_within_at_const (c : F) (x : E) (s : set E) :
  has_fderiv_within_at (λ x, c) (0 : E →L[𝕜] F) s x :=
has_fderiv_at_filter_const _ _ _

theorem has_fderiv_at_const (c : F) (x : E) :
  has_fderiv_at (λ x, c) (0 : E →L[𝕜] F) x :=
has_fderiv_at_filter_const _ _ _

lemma differentiable_at_const (c : F) : differentiable_at 𝕜 (λx, c) x :=
⟨0, has_fderiv_at_const c x⟩

lemma differentiable_within_at_const (c : F) : differentiable_within_at 𝕜 (λx, c) s x :=
differentiable_at.differentiable_within_at (differentiable_at_const _)

lemma fderiv_const (c : F) : fderiv 𝕜 (λy, c) x = 0 :=
has_fderiv_at.fderiv (has_fderiv_at_const c x)

lemma fderiv_within_const (c : F) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λy, c) s x = 0 :=
begin
  rw differentiable.fderiv_within (differentiable_at_const _) hxs,
  exact fderiv_const _
end

lemma differentiable_const (c : F) : differentiable 𝕜 (λx : E, c) :=
λx, differentiable_at_const _

lemma differentiable_on_const (c : F) : differentiable_on 𝕜 (λx, c) s :=
(differentiable_const _).differentiable_on

end const

/- Bounded linear maps -/
section is_bounded_linear_map

lemma is_bounded_linear_map.has_fderiv_at_filter (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_at_filter f h.to_continuous_linear_map x L :=
begin
  have : (λ (x' : E), f x' - f x - h.to_continuous_linear_map (x' - x)) = λx', 0,
  { ext,
    have : ∀a, h.to_continuous_linear_map a = f a := λa, rfl,
    simp,
    simp [this] },
  rw [has_fderiv_at_filter, this],
  exact asymptotics.is_o_zero _ _
end

lemma is_bounded_linear_map.has_fderiv_within_at (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_within_at f h.to_continuous_linear_map s x :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.has_fderiv_at (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_at f h.to_continuous_linear_map x  :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.differentiable_at (h : is_bounded_linear_map 𝕜 f) :
  differentiable_at 𝕜 f x :=
h.has_fderiv_at.differentiable_at

lemma is_bounded_linear_map.differentiable_within_at (h : is_bounded_linear_map 𝕜 f) :
  differentiable_within_at 𝕜 f s x :=
h.differentiable_at.differentiable_within_at

lemma is_bounded_linear_map.fderiv (h : is_bounded_linear_map 𝕜 f) :
  fderiv 𝕜 f x = h.to_continuous_linear_map :=
has_fderiv_at.fderiv (h.has_fderiv_at)

lemma is_bounded_linear_map.fderiv_within (h : is_bounded_linear_map 𝕜 f)
  (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 f s x = h.to_continuous_linear_map :=
begin
  rw differentiable.fderiv_within h.differentiable_at hxs,
  exact h.fderiv
end

lemma is_bounded_linear_map.differentiable (h : is_bounded_linear_map 𝕜 f) :
  differentiable 𝕜 f :=
λx, h.differentiable_at

lemma is_bounded_linear_map.differentiable_on (h : is_bounded_linear_map 𝕜 f) :
  differentiable_on 𝕜 f s :=
h.differentiable.differentiable_on

end is_bounded_linear_map

/- multiplication by a constant -/
section smul_const

theorem has_fderiv_at_filter.smul (h : has_fderiv_at_filter f f' x L) (c : 𝕜) :
  has_fderiv_at_filter (λ x, c • f x) (c • f') x L :=
(is_o_const_smul_left h c).congr_left $ λ x, by simp [smul_neg, smul_add]

theorem has_fderiv_within_at.smul (h : has_fderiv_within_at f f' s x) (c : 𝕜) :
  has_fderiv_within_at (λ x, c • f x) (c • f') s x :=
h.smul c

theorem has_fderiv_at.smul (h : has_fderiv_at f f' x) (c : 𝕜) :
  has_fderiv_at (λ x, c • f x) (c • f') x :=
h.smul c

lemma differentiable_within_at.smul (h : differentiable_within_at 𝕜 f s x) (c : 𝕜) :
  differentiable_within_at 𝕜 (λy, c • f y) s x :=
(h.has_fderiv_within_at.smul c).differentiable_within_at

lemma differentiable_at.smul (h : differentiable_at 𝕜 f x) (c : 𝕜) :
  differentiable_at 𝕜 (λy, c • f y) x :=
(h.has_fderiv_at.smul c).differentiable_at

lemma differentiable_on.smul (h : differentiable_on 𝕜 f s) (c : 𝕜) :
  differentiable_on 𝕜 (λy, c • f y) s :=
λx hx, (h x hx).smul c

lemma differentiable.smul (h : differentiable 𝕜 f) (c : 𝕜) :
  differentiable 𝕜 (λy, c • f y) :=
λx, (h x).smul c

lemma fderiv_within_smul (hxs : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f s x) (c : 𝕜) :
  fderiv_within 𝕜 (λy, c • f y) s x = c • fderiv_within 𝕜 f s x :=
(h.has_fderiv_within_at.smul c).fderiv_within hxs

lemma fderiv_smul (h : differentiable_at 𝕜 f x) (c : 𝕜) :
  fderiv 𝕜 (λy, c • f y) x = c • fderiv 𝕜 f x :=
(h.has_fderiv_at.smul c).fderiv

end smul_const

/- add -/
section add

theorem has_fderiv_at_filter.add
  (hf : has_fderiv_at_filter f f' x L) (hg : has_fderiv_at_filter g g' x L) :
  has_fderiv_at_filter (λ y, f y + g y) (f' + g') x L :=
(hf.add hg).congr_left $ λ _, by simp

theorem has_fderiv_within_at.add
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ y, f y + g y) (f' + g') s x :=
hf.add hg

theorem has_fderiv_at.add
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x + g x) (f' + g') x :=
hf.add hg

lemma differentiable_within_at.add
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  differentiable_within_at 𝕜 (λ y, f y + g y) s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  differentiable_at 𝕜 (λ y, f y + g y) x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).differentiable_at

lemma differentiable_on.add
  (hf : differentiable_on 𝕜 f s) (hg : differentiable_on 𝕜 g s) :
  differentiable_on 𝕜 (λy, f y + g y) s :=
λx hx, (hf x hx).add (hg x hx)

lemma differentiable.add
  (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
  differentiable 𝕜 (λy, f y + g y) :=
λx, (hf x).add (hg x)

lemma fderiv_within_add (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  fderiv_within 𝕜 (λy, f y + g y) s x = fderiv_within 𝕜 f s x + fderiv_within 𝕜 g s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λy, f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).fderiv

end add

/- neg -/
section neg

theorem has_fderiv_at_filter.neg (h : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (λ x, -f x) (-f') x L :=
(h.smul (-1:𝕜)).congr (by simp) (by simp)

theorem has_fderiv_within_at.neg (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_fderiv_at.neg (h : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, -f x) (-f') x :=
h.neg

lemma differentiable_within_at.neg (h : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λy, -f y) s x :=
h.has_fderiv_within_at.neg.differentiable_within_at

lemma differentiable_at.neg (h : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λy, -f y) x :=
h.has_fderiv_at.neg.differentiable_at

lemma differentiable_on.neg (h : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λy, -f y) s :=
λx hx, (h x hx).neg

lemma differentiable.neg (h : differentiable 𝕜 f) :
  differentiable 𝕜 (λy, -f y) :=
λx, (h x).neg

lemma fderiv_within_neg (hxs : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f s x) :
  fderiv_within 𝕜 (λy, -f y) s x = - fderiv_within 𝕜 f s x :=
h.has_fderiv_within_at.neg.fderiv_within hxs

lemma fderiv_neg (h : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (λy, -f y) x = - fderiv 𝕜 f x :=
h.has_fderiv_at.neg.fderiv

end neg

/- sub -/
section sub

theorem has_fderiv_at_filter.sub
  (hf : has_fderiv_at_filter f f' x L) (hg : has_fderiv_at_filter g g' x L) :
  has_fderiv_at_filter (λ x, f x - g x) (f' - g') x L :=
hf.add hg.neg

theorem has_fderiv_within_at.sub
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ x, f x - g x) (f' - g') s x :=
hf.sub hg

theorem has_fderiv_at.sub
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x - g x) (f' - g') x :=
hf.sub hg

lemma differentiable_within_at.sub
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  differentiable_within_at 𝕜 (λ y, f y - g y) s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  differentiable_at 𝕜 (λ y, f y - g y) x :=
(hf.has_fderiv_at.sub hg.has_fderiv_at).differentiable_at

lemma differentiable_on.sub
  (hf : differentiable_on 𝕜 f s) (hg : differentiable_on 𝕜 g s) :
  differentiable_on 𝕜 (λy, f y - g y) s :=
λx hx, (hf x hx).sub (hg x hx)

lemma differentiable.sub
  (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
  differentiable 𝕜 (λy, f y - g y) :=
λx, (hf x).sub (hg x)

lemma fderiv_within_sub (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  fderiv_within 𝕜 (λy, f y - g y) s x = fderiv_within 𝕜 f s x - fderiv_within 𝕜 g s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λy, f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
(hf.has_fderiv_at.sub hg.has_fderiv_at).fderiv

theorem has_fderiv_at_filter.is_O_sub (h : has_fderiv_at_filter f f' x L) :
is_O (λ x', f x' - f x) (λ x', x' - x) L :=
h.to_is_O.congr_of_sub.2 (f'.is_O_sub _ _)

end sub

/- Continuity -/
section continuous

theorem has_fderiv_at_filter.tendsto_nhds
  (hL : L ≤ nhds x) (h : has_fderiv_at_filter f f' x L) :
  tendsto f L (nhds (f x)) :=
begin
  have : tendsto (λ x', f x' - f x) L (nhds 0),
  { refine h.is_O_sub.trans_tendsto (tendsto_le_left hL _),
    rw ← sub_self x, exact tendsto_sub tendsto_id tendsto_const_nhds },
  have := tendsto_add this tendsto_const_nhds,
  rw zero_add (f x) at this,
  exact this.congr (by simp)
end

theorem has_fderiv_within_at.continuous_within_at
  (h : has_fderiv_within_at f f' s x) : continuous_within_at f s x :=
has_fderiv_at_filter.tendsto_nhds lattice.inf_le_left h

theorem has_fderiv_at.continuous_at (h : has_fderiv_at f f' x) :
  continuous_at f x :=
has_fderiv_at_filter.tendsto_nhds (le_refl _) h

lemma differentiable_within_at.continuous_within_at (h : differentiable_within_at 𝕜 f s x) :
  continuous_within_at f s x :=
let ⟨f', hf'⟩ := h in hf'.continuous_within_at

lemma differentiable_at.continuous_at (h : differentiable_at 𝕜 f x) : continuous_at f x :=
let ⟨f', hf'⟩ := h in hf'.continuous_at

lemma differentiable_on.continuous_on (h : differentiable_on 𝕜 f s) : continuous_on f s :=
λx hx, (h x hx).continuous_within_at

lemma differentiable.continuous (h : differentiable 𝕜 f) : continuous f :=
continuous_iff_continuous_at.2 $ λx, (h x).continuous_at

end continuous

/- Bounded bilinear maps -/

section bilinear_map
variables {b : E × F → G} {u : set (E × F) }

lemma is_bounded_bilinear_map.has_fderiv_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_fderiv_at b (h.deriv p) p :=
begin
  have : (λ (x : E × F), b x - b p - (h.deriv p) (x - p)) = (λx, b (x.1 - p.1, x.2 - p.2)),
  { ext x,
    delta is_bounded_bilinear_map.deriv,
    change b x - b p - (b (p.1, x.2-p.2) + b (x.1-p.1, p.2))
           = b (x.1 - p.1, x.2 - p.2),
    have : b x = b (x.1, x.2), by { cases x, refl },
    rw this,
    have : b p = b (p.1, p.2), by { cases p, refl },
    rw this,
    simp only [h.map_sub_left, h.map_sub_right],
    abel },
  rw [has_fderiv_at, has_fderiv_at_filter, this],
  rcases h.bound with ⟨C, Cpos, hC⟩,
  have A : asymptotics.is_O (λx : E × F, b (x.1 - p.1, x.2 - p.2))
    (λx, ∥x - p∥ * ∥x - p∥) (nhds p) :=
  ⟨C, Cpos, filter.univ_mem_sets' (λx, begin
    simp only [mem_set_of_eq, norm_mul, norm_norm],
    calc ∥b (x.1 - p.1, x.2 - p.2)∥ ≤ C * ∥x.1 - p.1∥ * ∥x.2 - p.2∥ : hC _ _
    ... ≤ C * ∥x-p∥ * ∥x-p∥ : by apply_rules [mul_le_mul, le_max_left, le_max_right, norm_nonneg,
      le_of_lt Cpos, le_refl, mul_nonneg, norm_nonneg, norm_nonneg]
    ... = C * (∥x-p∥ * ∥x-p∥) : mul_assoc _ _ _ end)⟩,
  have B : asymptotics.is_o (λ (x : E × F), ∥x - p∥ * ∥x - p∥)
    (λx, 1 * ∥x - p∥) (nhds p),
  { apply asymptotics.is_o_mul_right _ (asymptotics.is_O_refl _ _),
    rw [asymptotics.is_o_iff_tendsto],
    { simp only [div_one],
      have : 0 = ∥p - p∥, by simp,
      rw this,
      have : continuous (λx, ∥x-p∥) :=
        continuous_norm.comp (continuous_sub continuous_id continuous_const),
      exact this.tendsto p },
    simp only [forall_prop_of_false, not_false_iff, one_ne_zero, forall_true_iff] },
  simp only [one_mul, asymptotics.is_o_norm_right] at B,
  exact A.trans_is_o B
end

lemma is_bounded_bilinear_map.has_fderiv_within_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_fderiv_within_at b (h.deriv p) u p :=
(h.has_fderiv_at p).has_fderiv_within_at

lemma is_bounded_bilinear_map.differentiable_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  differentiable_at 𝕜 b p :=
(h.has_fderiv_at p).differentiable_at

lemma is_bounded_bilinear_map.differentiable_within_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  differentiable_within_at 𝕜 b u p :=
(h.differentiable_at p).differentiable_within_at

lemma is_bounded_bilinear_map.fderiv (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  fderiv 𝕜 b p = h.deriv p :=
has_fderiv_at.fderiv (h.has_fderiv_at p)

lemma is_bounded_bilinear_map.fderiv_within (h : is_bounded_bilinear_map 𝕜 b) (p : E × F)
  (hxs : unique_diff_within_at 𝕜 u p) : fderiv_within 𝕜 b u p = h.deriv p :=
begin
  rw differentiable.fderiv_within (h.differentiable_at p) hxs,
  exact h.fderiv p
end

lemma is_bounded_bilinear_map.differentiable (h : is_bounded_bilinear_map 𝕜 b) :
  differentiable 𝕜 b :=
λx, h.differentiable_at x

lemma is_bounded_bilinear_map.differentiable_on (h : is_bounded_bilinear_map 𝕜 b) :
  differentiable_on 𝕜 b u :=
h.differentiable.differentiable_on

lemma is_bounded_bilinear_map.continuous (h : is_bounded_bilinear_map 𝕜 b) :
  continuous b :=
h.differentiable.continuous

end bilinear_map


/- Cartesian products -/
section cartesian_product
variables {f₂ : E → G} {f₂' : E →L[𝕜] G}

lemma has_fderiv_at_filter.prod
  (hf₁ : has_fderiv_at_filter f₁ f₁' x L) (hf₂ : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λx, (f₁ x, f₂ x)) (continuous_linear_map.prod f₁' f₂') x L :=
begin
  have : (λ (x' : E), (f₁ x', f₂ x') - (f₁ x, f₂ x) - (continuous_linear_map.prod f₁' f₂') (x' -x)) =
           (λ (x' : E), (f₁ x' - f₁ x - f₁' (x' - x), f₂ x' - f₂ x - f₂' (x' - x))) := rfl,
  rw [has_fderiv_at_filter, this],
  rw [asymptotics.is_o_prod_left],
  exact ⟨hf₁, hf₂⟩
end

lemma has_fderiv_within_at.prod
  (hf₁ : has_fderiv_within_at f₁ f₁' s x) (hf₂ : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λx, (f₁ x, f₂ x)) (continuous_linear_map.prod f₁' f₂') s x :=
hf₁.prod hf₂

lemma has_fderiv_at.prod (hf₁ : has_fderiv_at f₁ f₁' x) (hf₂ : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λx, (f₁ x, f₂ x)) (continuous_linear_map.prod f₁' f₂') x :=
hf₁.prod hf₂

lemma differentiable_within_at.prod
  (hf₁ : differentiable_within_at 𝕜 f₁ s x) (hf₂ : differentiable_within_at 𝕜 f₂ s x) :
  differentiable_within_at 𝕜 (λx:E, (f₁ x, f₂ x)) s x :=
(hf₁.has_fderiv_within_at.prod hf₂.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.prod (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
  differentiable_at 𝕜 (λx:E, (f₁ x, f₂ x)) x :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).differentiable_at

lemma differentiable_on.prod (hf₁ : differentiable_on 𝕜 f₁ s) (hf₂ : differentiable_on 𝕜 f₂ s) :
  differentiable_on 𝕜 (λx:E, (f₁ x, f₂ x)) s :=
λx hx, differentiable_within_at.prod (hf₁ x hx) (hf₂ x hx)

lemma differentiable.prod (hf₁ : differentiable 𝕜 f₁) (hf₂ : differentiable 𝕜 f₂) :
  differentiable 𝕜 (λx:E, (f₁ x, f₂ x)) :=
λ x, differentiable_at.prod (hf₁ x) (hf₂ x)

lemma differentiable_at.fderiv_prod
  (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
  fderiv 𝕜 (λx:E, (f₁ x, f₂ x)) x =
    continuous_linear_map.prod (fderiv 𝕜 f₁ x) (fderiv 𝕜 f₂ x) :=
has_fderiv_at.fderiv (has_fderiv_at.prod hf₁.has_fderiv_at hf₂.has_fderiv_at)

lemma differentiable_at.fderiv_within_prod
  (hf₁ : differentiable_within_at 𝕜 f₁ s x) (hf₂ : differentiable_within_at 𝕜 f₂ s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx:E, (f₁ x, f₂ x)) s x =
    continuous_linear_map.prod (fderiv_within 𝕜 f₁ s x) (fderiv_within 𝕜 f₂ s x) :=
begin
  apply has_fderiv_within_at.fderiv_within _ hxs,
  exact has_fderiv_within_at.prod hf₁.has_fderiv_within_at hf₂.has_fderiv_within_at
end

end cartesian_product

/- Composition -/
section composition

/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/

variable (x)

theorem has_fderiv_at_filter.comp {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at_filter g g' (f x) (L.map f))
  (hf : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (g ∘ f) (g'.comp f') x L :=
let eq₁ := (g'.is_O_comp _ _).trans_is_o hf in
let eq₂ := ((hg.comp f).mono le_comap_map).trans_is_O hf.is_O_sub in
by { refine eq₂.tri (eq₁.congr_left (λ x', _)), simp }

/- A readable version of the previous theorem,
   a general form of the chain rule. -/

example {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at_filter g g' (f x) (L.map f))
  (hf : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (g ∘ f) (g'.comp f') x L :=
begin
  unfold has_fderiv_at_filter at hg,
  have : is_o (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', f x' - f x) L,
    from (hg.comp f).mono le_comap_map,
  have eq₁ : is_o (λ x', g (f x') - g (f x) - g' (f x' - f x)) (λ x', x' - x) L,
    from this.trans_is_O hf.is_O_sub,
  have eq₂ : is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L,
    from hf,
  have : is_O
    (λ x', g' (f x' - f x - f' (x' - x))) (λ x', f x' - f x - f' (x' - x)) L,
    from g'.is_O_comp _ _,
  have : is_o (λ x', g' (f x' - f x - f' (x' - x))) (λ x', x' - x) L,
    from this.trans_is_o eq₂,
  have eq₃ : is_o (λ x', g' (f x' - f x) - (g' (f' (x' - x)))) (λ x', x' - x) L,
    by { refine this.congr_left _, simp},
  exact eq₁.tri eq₃
end

theorem has_fderiv_within_at.comp {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_within_at g g' (f '' s) (f x))
  (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
(has_fderiv_at_filter.mono hg
  hf.continuous_within_at.tendsto_nhds_within_image).comp x hf

/-- The chain rule. -/
theorem has_fderiv_at.comp {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (g ∘ f) (g'.comp f') x :=
(hg.mono hf.continuous_at).comp x hf

theorem has_fderiv_at.comp_has_fderiv_within_at {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
begin
  rw ← has_fderiv_within_at_univ at hg,
  exact has_fderiv_within_at.comp x (hg.mono (subset_univ _)) hf
end

lemma differentiable_within_at.comp {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (h : f '' s ⊆ t) : differentiable_within_at 𝕜 (g ∘ f) s x :=
begin
  rcases hf with ⟨f', hf'⟩,
  rcases hg with ⟨g', hg'⟩,
  exact ⟨continuous_linear_map.comp g' f', (hg'.mono h).comp x hf'⟩
end

lemma differentiable_at.comp {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (g ∘ f) x :=
(hg.has_fderiv_at.comp x hf.has_fderiv_at).differentiable_at

lemma fderiv_within.comp {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (h : f '' s ⊆ t) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (g ∘ f) s x =
    continuous_linear_map.comp (fderiv_within 𝕜 g t (f x)) (fderiv_within 𝕜 f s x) :=
begin
  apply has_fderiv_within_at.fderiv_within _ hxs,
  apply has_fderiv_within_at.comp x _ (hf.has_fderiv_within_at),
  apply hg.has_fderiv_within_at.mono h
end

lemma fderiv.comp {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (g ∘ f) x = continuous_linear_map.comp (fderiv 𝕜 g (f x)) (fderiv 𝕜 f x) :=
begin
  apply has_fderiv_at.fderiv,
  exact has_fderiv_at.comp x hg.has_fderiv_at hf.has_fderiv_at
end

lemma differentiable_on.comp {g : F → G} {t : set F}
  (hg : differentiable_on 𝕜 g t) (hf : differentiable_on 𝕜 f s) (st : f '' s ⊆ t) :
  differentiable_on 𝕜 (g ∘ f) s :=
λx hx, differentiable_within_at.comp x (hg (f x) (st (mem_image_of_mem _ hx))) (hf x hx) st

lemma differentiable.comp {g : F → G} (hg : differentiable 𝕜 g) (hf : differentiable 𝕜 f) :
  differentiable 𝕜 (g ∘ f) :=
λx, differentiable_at.comp x (hg (f x)) (hf x)

end composition

/- Multiplication by a scalar function -/
section smul
variables {c : E → 𝕜} {c' : E →L[𝕜] 𝕜}

theorem has_fderiv_within_at.smul'
  (hc : has_fderiv_within_at c c' s x) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ y, c y • f y) (c x • f' + c'.scalar_prod_space_iso (f x)) s x :=
begin
  have : is_bounded_bilinear_map 𝕜 (λ (p : 𝕜 × F), p.1 • p.2) := is_bounded_bilinear_map_smul,
  exact has_fderiv_at.comp_has_fderiv_within_at x (this.has_fderiv_at (c x, f x)) (hc.prod hf)
end

theorem has_fderiv_at.smul' (hc : has_fderiv_at c c' x) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ y, c y • f y) (c x • f' + c'.scalar_prod_space_iso (f x)) x :=
begin
  have : is_bounded_bilinear_map 𝕜 (λ (p : 𝕜 × F), p.1 • p.2) := is_bounded_bilinear_map_smul,
  exact has_fderiv_at.comp x (this.has_fderiv_at (c x, f x)) (hc.prod hf)
end

lemma differentiable_within_at.smul'
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λ y, c y • f y) s x :=
(hc.has_fderiv_within_at.smul' hf.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.smul' (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λ y, c y • f y) x :=
(hc.has_fderiv_at.smul' hf.has_fderiv_at).differentiable_at

lemma differentiable_on.smul' (hc : differentiable_on 𝕜 c s) (hf : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λ y, c y • f y) s :=
λx hx, (hc x hx).smul' (hf x hx)

lemma differentiable.smul' (hc : differentiable 𝕜 c) (hf : differentiable 𝕜 f) :
  differentiable 𝕜 (λ y, c y • f y) :=
λx, (hc x).smul' (hf x)

lemma fderiv_within_smul' (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  fderiv_within 𝕜 (λ y, c y • f y) s x =
    c x • fderiv_within 𝕜 f s x + (fderiv_within 𝕜 c s x).scalar_prod_space_iso (f x) :=
(hc.has_fderiv_within_at.smul' hf.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_smul' (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (λ y, c y • f y) x =
    c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).scalar_prod_space_iso (f x) :=
(hc.has_fderiv_at.smul' hf.has_fderiv_at).fderiv

end smul


/- Multiplication of scalar functions -/

section mul
set_option class.instance_max_depth 120
variables {c d : E → 𝕜} {c' d' : E →L[𝕜] 𝕜}

theorem has_fderiv_within_at.mul
  (hc : has_fderiv_within_at c c' s x) (hd : has_fderiv_within_at d d' s x) :
  has_fderiv_within_at (λ y, c y * d y) (c x • d' + d x • c') s x :=
begin
  have : is_bounded_bilinear_map 𝕜 (λ (p : 𝕜 × 𝕜), p.1 * p.2) := is_bounded_bilinear_map_mul,
  convert has_fderiv_at.comp_has_fderiv_within_at x (this.has_fderiv_at (c x, d x)) (hc.prod hd),
  ext z,
  change c x * d' z + d x * c' z = c x * d' z + c' z * d x,
  ring
end

theorem has_fderiv_at.mul (hc : has_fderiv_at c c' x) (hd : has_fderiv_at d d' x) :
  has_fderiv_at (λ y, c y * d y) (c x • d' + d x • c') x :=
begin
  have : is_bounded_bilinear_map 𝕜 (λ (p : 𝕜 × 𝕜), p.1 * p.2) := is_bounded_bilinear_map_mul,
  convert has_fderiv_at.comp x (this.has_fderiv_at (c x, d x)) (hc.prod hd),
  ext z,
  change c x * d' z + d x * c' z = c x * d' z + c' z * d x,
  ring
end

lemma differentiable_within_at.mul
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  differentiable_within_at 𝕜 (λ y, c y * d y) s x :=
(hc.has_fderiv_within_at.mul hd.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  differentiable_at 𝕜 (λ y, c y * d y) x :=
(hc.has_fderiv_at.mul hd.has_fderiv_at).differentiable_at

lemma differentiable_on.mul (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) :
  differentiable_on 𝕜 (λ y, c y * d y) s :=
λx hx, (hc x hx).mul (hd x hx)

lemma differentiable.mul (hc : differentiable 𝕜 c) (hd : differentiable 𝕜 d) :
  differentiable 𝕜 (λ y, c y * d y) :=
λx, (hc x).mul (hd x)

lemma fderiv_within_mul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  fderiv_within 𝕜 (λ y, c y * d y) s x =
    c x • fderiv_within 𝕜 d s x + d x • fderiv_within 𝕜 c s x :=
(hc.has_fderiv_within_at.mul hd.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  fderiv 𝕜 (λ y, c y * d y) x =
    c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
(hc.has_fderiv_at.mul hd.has_fderiv_at).fderiv

end mul

end
/-
  In the special case of a normed space over the reals,
  we can use  scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/

section

variables {E : Type*} [normed_group E] [normed_space ℝ E]
variables {F : Type*} [normed_group F] [normed_space ℝ F]
variables {G : Type*} [normed_group G] [normed_space ℝ G]

theorem has_fderiv_at_filter_real_equiv {f : E → F} {f' : E →L[ℝ] F} {x : E} {L : filter E} :
  tendsto (λ x' : E, ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) L (nhds 0) ↔
  tendsto (λ x' : E, ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) L (nhds 0) :=
begin
  symmetry,
  rw [tendsto_iff_norm_tendsto_zero], refine tendsto.congr'r (λ x', _),
  have : ∥x' + -x∥⁻¹ ≥ 0, from inv_nonneg.mpr (norm_nonneg _),
  simp [norm_smul, real.norm_eq_abs, abs_of_nonneg this]
end

end
