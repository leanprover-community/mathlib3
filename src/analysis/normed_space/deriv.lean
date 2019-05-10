/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel

The Fréchet derivative.

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[k] F` a
bounded k-linear map, where `k` is a non-discrete normed field. Then

  `has_fderiv_within_at f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_within_at f f' x univ`

The derivative is defined in terms of the `is_o` relation, but also
characterized in terms of the `tendsto` relation.

We also introduce predicates `differentiable_within_at k f s x` (where `k` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `differentiable_at k f x`,
`differentiable_on k f s` and `differentiable k f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderiv_within k f s x` and `fderiv k f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `unique_diff_within_at s x` and
`unique_diff_on s` express this property, and we prove that indeed they imply the uniqueness of the
derivative. This is satisfied for open subsets, and in particular for `univ`. This uniqueness
only holds when the field is non-discrete, which we request at the very beginning:
otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

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
* bounded bilinear maps
* multiplication of a function by a scalar function
* multiplication of two scalar functions
* composition of functions (the chain rule)

-/
import topology.basic topology.sequences topology.opens
import analysis.normed_space.operator_norm analysis.normed_space.bounded_linear_maps

import analysis.asymptotics
import tactic.abel

open filter asymptotics bounded_linear_map set

noncomputable theory
local attribute [instance, priority 0] classical.decidable_inhabited classical.prop_decidable

section

set_option class.instance_max_depth 60

variables {k : Type*} [nondiscrete_normed_field k]
variables {E : Type*} [normed_space k E]
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

def has_fderiv_at_filter (f : E → F) (f' : E →L[k] F) (x : E) (L : filter E) :=
is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L

def has_fderiv_within_at (f : E → F) (f' : E →L[k] F) (s : set E) (x : E) :=
has_fderiv_at_filter f f' x (nhds_within x s)

def has_fderiv_at (f : E → F) (f' : E →L[k] F) (x : E) :=
has_fderiv_at_filter f f' x (nhds x)

variables (k)

def differentiable_within_at (f : E → F) (s : set E) (x : E) :=
∃f' : E →L[k] F, has_fderiv_within_at f f' s x

def differentiable_at (f : E → F) (x : E) :=
∃f' : E →L[k] F, has_fderiv_at f f' x

def fderiv_within (f : E → F) (s : set E) (x : E) : E →L[k] F :=
if h : ∃f', has_fderiv_within_at f f' s x then classical.some h else 0

def fderiv (f : E → F) (x : E) : E →L[k] F :=
if h : ∃f', has_fderiv_at f f' x then classical.some h else 0

def differentiable_on (f : E → F) (s : set E) :=
∀x ∈ s, differentiable_within_at k f s x

def differentiable (f : E → F) :=
∀x, differentiable_at k f x

/- A notation for sets on which the differential has to be unique. This is for instance the case
on open sets, which is the main case of applications, but also on closed halfspaces or closed
disks. It is only on such sets that it makes sense to talk about "the" derivative, and to talk
about higher smoothness.

The differential is unique when the tangent directions (called the tangent cone below) spans a
dense subset of the underlying normed space. -/

def tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c:ℕ → k) (d: ℕ → E), {n:ℕ | x + d n ∈ s} ∈ (at_top : filter ℕ) ∧
  (tendsto (λn, ∥c n∥) at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (nhds y))}

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `unique_diff_within_at.eq` -/
def unique_diff_within_at (s : set E) (x : E) : Prop :=
closure ((submodule.span k (tangent_cone_at k s x)) : set E) = univ

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space.  The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `unique_diff_on.eq` -/
def unique_diff_on (s : set E) : Prop :=
∀x ∈ s, unique_diff_within_at k s x

variables {k}
variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[k] F}
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}


section derivative_uniqueness
/- In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `unique_diff_within_at` and `unique_diff_on` indeed imply the
uniqueness of the derivative. -/

lemma tangent_cone_univ : tangent_cone_at k univ x = univ :=
begin
  refine univ_subset_iff.1 (λy hy, _),
  rcases exists_one_lt_norm k with ⟨w, hw⟩,
  refine ⟨λn, w^n, λn, (w^n)⁻¹ • y, univ_mem_sets' (λn, mem_univ _),  _, _⟩,
  { simp only [norm_pow],
    exact tendsto_pow_at_top_at_top_of_gt_1 hw },
  { convert tendsto_const_nhds,
    ext n,
    have : w ^ n * (w ^ n)⁻¹ = 1,
    { apply mul_inv_cancel,
      apply pow_ne_zero,
      simpa [norm_eq_zero] using (ne_of_lt (lt_trans zero_lt_one hw)).symm },
    rw [smul_smul, this, one_smul] }
end

lemma tangent_cone_mono (h : s ⊆ t) :
  tangent_cone_at k s x ⊆ tangent_cone_at k t x :=
begin
  rintros y ⟨c, d, ds, ctop, clim⟩,
  exact ⟨c, d, mem_sets_of_superset ds (λn hn, h hn), ctop, clim⟩
end

/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
lemma tangent_cone_at.lim_zero {y : E} {c : ℕ → k} {d : ℕ → E}
  (hc : tendsto (λn, ∥c n∥) at_top at_top) (hd : tendsto (λn, c n • d n) at_top (nhds y)) :
  tendsto d at_top (nhds 0) :=
begin
  have A : tendsto (λn, ∥c n∥⁻¹) at_top (nhds 0) :=
    hc.comp tendsto_inverse_at_top_nhds_0,
  have B : tendsto (λn, ∥c n • d n∥) at_top (nhds ∥y∥) :=
    hd.comp (continuous_norm.tendsto _),
  have C : tendsto (λn, ∥c n∥⁻¹ * ∥c n • d n∥) at_top (nhds (0 * ∥y∥)) :=
    tendsto_mul A B,
  rw zero_mul at C,
  have : {n | ∥c n∥⁻¹ * ∥c n • d n∥ = ∥d n∥} ∈ (@at_top ℕ _),
  { have : {n | 1 ≤ ∥c n∥} ∈ (@at_top ℕ _) :=
      hc (mem_at_top 1),
    apply mem_sets_of_superset this (λn hn, _),
    rw mem_set_of_eq at hn,
    rw [mem_set_of_eq, ← norm_inv, ← norm_smul, smul_smul, inv_mul_cancel, one_smul],
    simpa [norm_eq_zero] using (ne_of_lt (lt_of_lt_of_le zero_lt_one hn)).symm },
  have D : tendsto (λ (n : ℕ), ∥d n∥) at_top (nhds 0) :=
    tendsto.congr' this C,
  rw tendsto_zero_iff_norm_tendsto_zero,
  exact D
end

/-- Intersecting with an open set does not change the tangent cone. -/
lemma tangent_cone_inter_open {x : E} {s t : set E} (xs : x ∈ s) (xt : x ∈ t) (ht : is_open t) :
  tangent_cone_at k (s ∩ t) x = tangent_cone_at k s x :=
begin
  refine subset.antisymm (tangent_cone_mono (inter_subset_left _ _)) _,
  rintros y ⟨c, d, ds, ctop, clim⟩,
  refine ⟨c, d, _, ctop, clim⟩,
  have : {n : ℕ | x + d n ∈ t} ∈ at_top,
  { have : tendsto (λn, x + d n) at_top (nhds (x + 0)) :=
      tendsto_add tendsto_const_nhds (tangent_cone_at.lim_zero ctop clim),
    rw add_zero at this,
    exact tendsto_nhds.1 this t ht xt },
  exact inter_mem_sets ds this
end

/-- `unique_diff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem unique_diff_within_at.eq (H : unique_diff_within_at k s x)
  (h : has_fderiv_within_at f f' s x) (h₁ : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
begin
  have A : ∀y ∈ tangent_cone_at k s x, f' y = f₁' y,
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
    { simp only [smul_sub, (bounded_linear_map.map_smul _ _ _).symm],
      apply tendsto_sub (ylim.comp (f₁'.continuous.tendsto _)) (ylim.comp (f'.continuous.tendsto _)) },
    have : f₁' y - f' y = 0 := tendsto_nhds_unique (by simp) L' L,
    exact (sub_eq_zero_iff_eq.1 this).symm },
  have B : ∀y ∈ submodule.span k (tangent_cone_at k s x), f' y = f₁' y,
  { assume y hy,
    apply submodule.span_induction hy,
    { exact λy hy, A y hy },
    { simp only [bounded_linear_map.map_zero] },
    { simp {contextual := tt} },
    { simp {contextual := tt} } },
  have C : ∀y ∈ closure ((submodule.span k (tangent_cone_at k s x)) : set E), f' y = f₁' y,
  { assume y hy,
    let K := {y | f' y = f₁' y},
    have : (submodule.span k (tangent_cone_at k s x) : set E) ⊆ K := B,
    have : closure (submodule.span k (tangent_cone_at k s x) : set E) ⊆ closure K :=
      closure_mono this,
    have : y ∈ closure K := this hy,
    rwa closure_eq_of_is_closed (is_closed_eq f'.continuous f₁'.continuous) at this },
  unfold unique_diff_within_at at H,
  rw H at C,
  ext y,
  exact C y (mem_univ _)
end

theorem unique_diff_on.eq (H : unique_diff_on k s) (hx : x ∈ s)
  (h : has_fderiv_within_at f f' s x) (h₁ : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
unique_diff_within_at.eq (H x hx) h h₁

lemma unique_diff_within_univ_at : unique_diff_within_at k univ x :=
by { rw [unique_diff_within_at, tangent_cone_univ], simp }

lemma unique_diff_within_at_inter (xs : x ∈ s) (xt : x ∈ t) (hs : unique_diff_within_at k s x)
  (ht : is_open t) : unique_diff_within_at k (s ∩ t) x :=
begin
  unfold unique_diff_within_at,
  rw tangent_cone_inter_open xs xt ht,
  exact hs
end

lemma is_open.unique_diff_within_at (xs : x ∈ s) (hs : is_open s) : unique_diff_within_at k s x :=
begin
  have := unique_diff_within_at_inter (mem_univ _) xs unique_diff_within_univ_at hs,
  rwa univ_inter at this
end

lemma unique_diff_on_inter (hs : unique_diff_on k s) (ht : is_open t) : unique_diff_on k (s ∩ t) :=
λx hx, unique_diff_within_at_inter hx.1 hx.2 (hs x hx.1) ht

lemma is_open.unique_diff_on (hs : is_open s) : unique_diff_on k s :=
λx hx, is_open.unique_diff_within_at hx hs

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
  differentiable_within_at k f s x :=
⟨f', h⟩

lemma has_fderiv_at.differentiable_at (h : has_fderiv_at f f' x) : differentiable_at k f x :=
⟨f', h⟩

lemma differentiable_within_at.has_fderiv_within_at (h : differentiable_within_at k f s x) :
  has_fderiv_within_at f (fderiv_within k f s x) s x :=
begin
  dunfold fderiv_within,
  dunfold differentiable_within_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma differentiable_at.has_fderiv_at (h : differentiable_at k f x) :
  has_fderiv_at f (fderiv k f x) x :=
begin
  dunfold fderiv,
  dunfold differentiable_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma differentiable_within_at.mono {t : set E} (h : s ⊆ t)
  (h : differentiable_within_at k f t x) : differentiable_within_at k f s x :=
begin
  rcases h with ⟨f', hf'⟩,
  exact ⟨f', hf'.mono h⟩
end

lemma differentiable_within_univ_at :
  differentiable_within_at k f univ x ↔ differentiable_at k f x :=
begin
  unfold differentiable_within_at has_fderiv_within_at,
  rw nhds_within_univ,
  refl
end

@[simp] lemma has_fderiv_within_univ_at :
  has_fderiv_within_at f f' univ x ↔ has_fderiv_at f f' x :=
by { simp only [has_fderiv_within_at, nhds_within_univ], refl }

theorem has_fderiv_at_unique
  (h₀ : has_fderiv_at f f₀' x) (h₁ : has_fderiv_at f f₁' x) : f₀' = f₁' :=
begin
  rw ← has_fderiv_within_univ_at at h₀ h₁,
  exact unique_diff_within_univ_at.eq h₀ h₁
end

lemma differentiable_at.differentiable_within_at
  (h : differentiable_at k f x) : differentiable_within_at k f s x :=
differentiable_within_at.mono (subset_univ _) (differentiable_within_univ_at.2 h)

lemma has_fderiv_within_at.fderiv_within {f' : E →L[k] F}
  (h : has_fderiv_within_at f f' s x) (hxs : unique_diff_within_at k s x) :
  fderiv_within k f s x = f' :=
by { ext, rw hxs.eq h h.differentiable_within_at.has_fderiv_within_at }

lemma has_fderiv_at.fderiv {f' : E →L[k] F} (h : has_fderiv_at f f' x) :
  fderiv k f x = f' :=
by { ext, rw has_fderiv_at_unique h h.differentiable_at.has_fderiv_at }

lemma differentiable.fderiv_within
  (h : differentiable_at k f x) (hxs : unique_diff_within_at k s x) :
  fderiv_within k f s x = fderiv k f x :=
begin
  apply has_fderiv_within_at.fderiv_within _ hxs,
  exact h.has_fderiv_at.has_fderiv_within_at
end

lemma differentiable_on.mono {f : E → F} {s t : set E}
  (h : differentiable_on k f t) (st : s ⊆ t) : differentiable_on k f s :=
λx hx, (h x (st hx)).mono st

lemma differentiable_on_univ :
  differentiable_on k f univ ↔ differentiable k f :=
by { simp [differentiable_on, differentiable_within_univ_at], refl }

lemma differentiable.differentiable_on
  (h : differentiable k f) : differentiable_on k f s :=
(differentiable_on_univ.2 h).mono (subset_univ _)

@[simp] lemma fderiv_within_univ : fderiv_within k f univ = fderiv k f :=
begin
  ext x : 1,
  by_cases h : differentiable_at k f x,
  { apply has_fderiv_within_at.fderiv_within _ (is_open_univ.unique_diff_within_at (mem_univ _)),
    rw has_fderiv_within_univ_at,
    apply h.has_fderiv_at },
  { have : fderiv k f x = 0,
      by { unfold differentiable_at at h, simp [fderiv, h] },
    rw this,
    have : ¬(differentiable_within_at k f univ x), by rwa differentiable_within_univ_at,
    unfold differentiable_within_at at this,
    simp [fderiv_within, this, -has_fderiv_within_univ_at] }
end

lemma differentiable_within_at_inter (xs : x ∈ s) (xt : x ∈ t) (ht : is_open t) :
  differentiable_within_at k f (s ∩ t) x ↔ differentiable_within_at k f s x :=
by simp only [differentiable_within_at, has_fderiv_within_at, has_fderiv_at_filter,
    nhds_within_restrict s xt ht]

lemma differentiable_on_of_locally_differentiable_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ differentiable_on k f (s ∩ u)) : differentiable_on k f s :=
begin
  assume x xs,
  rcases h x xs with ⟨t, t_open, xt, ht⟩,
  exact (differentiable_within_at_inter xs xt t_open).1 (ht x ⟨xs, xt⟩)
end

end fderiv_properties

/- Congr -/
section congr

theorem has_fderiv_at_filter_congr'
  (hx : f₀ x = f₁ x) (h₀ : {x | f₀ x = f₁ x} ∈ L) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter f₀ f₀' x L ↔ has_fderiv_at_filter f₁ f₁' x L :=
by { rw (ext h₁), exact is_o_congr
  (by filter_upwards [h₀] λ x (h : _ = _), by simp [h, hx])
  (univ_mem_sets' $ λ _, rfl) }

theorem has_fderiv_at_filter_congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter f₀ f₀' x L ↔ has_fderiv_at_filter f₁ f₁' x L :=
has_fderiv_at_filter_congr' (h₀ _) (univ_mem_sets' h₀) h₁

theorem has_fderiv_at_filter.congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter f₀ f₀' x L → has_fderiv_at_filter f₁ f₁' x L :=
(has_fderiv_at_filter_congr h₀ h₁).1

theorem has_fderiv_within_at_congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_within_at f₀ f₀' s x ↔ has_fderiv_within_at f₁ f₁' s x :=
has_fderiv_at_filter_congr h₀ h₁

theorem has_fderiv_within_at.congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_within_at f₀ f₀' s x → has_fderiv_within_at f₁ f₁' s x :=
(has_fderiv_within_at_congr h₀ h₁).1

theorem has_fderiv_at_congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at f₀ f₀' x ↔ has_fderiv_at f₁ f₁' x :=
has_fderiv_at_filter_congr h₀ h₁

theorem has_fderiv_at.congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at f₀ f₀' x → has_fderiv_at f₁ f₁' x :=
(has_fderiv_at_congr h₀ h₁).1

lemma has_fderiv_at_filter.congr' (h : has_fderiv_at_filter f f' x L)
  (hL : {x | f₁ x = f x} ∈ L) (hx : f₁ x = f x) : has_fderiv_at_filter f₁ f' x L :=
begin
  refine (asymptotics.is_o_congr_left _).1 h,
  convert hL,
  ext,
  finish [hx],
end

lemma has_fderiv_within_at.congr_mono (h : has_fderiv_within_at f f' s x) (ht : ∀x ∈ t, f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_fderiv_within_at f₁ f' t x :=
has_fderiv_at_filter.congr' (h.mono h₁) (filter.mem_inf_sets_of_right ht) hx

lemma differentiable_within_at.congr_mono (h : differentiable_within_at k f s x)
  (ht : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : differentiable_within_at k f₁ t x :=
(has_fderiv_within_at.congr_mono h.has_fderiv_within_at ht hx h₁).differentiable_within_at

lemma differentiable_at.congr (h : differentiable_at k f x) (h' : ∀x, f₁ x = f x) :
  differentiable_at k f₁ x :=
by { have : f₁ = f, by { ext y, exact h' y }, rwa this }

lemma differentiable_on.congr_mono (h : differentiable_on k f s) (h' : ∀x ∈ t, f₁ x = f x)
  (h₁ : t ⊆ s) : differentiable_on k f₁ t :=
λ x hx, (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

lemma differentiable.congr (h : differentiable k f) (h' : ∀x, f₁ x = f x) :
  differentiable k f₁ :=
by { have : f₁ = f, by { ext y, exact h' y }, rwa this }

lemma differentiable.congr' (h : differentiable_at k f x)
  (hL : {y | f₁ y = f y} ∈ nhds x) (hx : f₁ x = f x) :
  differentiable_at k f₁ x :=
has_fderiv_at.differentiable_at (has_fderiv_at_filter.congr' h.has_fderiv_at hL hx)

lemma differentiable_within_at.fderiv_within_congr_mono (h : differentiable_within_at k f s x)
  (hs : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : unique_diff_within_at k t x) (h₁ : t ⊆ s) :
  fderiv_within k f₁ t x = fderiv_within k f s x :=
(has_fderiv_within_at.congr_mono h.has_fderiv_within_at hs hx h₁).fderiv_within hxt

lemma differentiable_at.fderiv_congr (h : differentiable_at k f x) (h' : ∀x, f₁ x = f x) :
  fderiv k f₁ x = fderiv k f x :=
by { have : f₁ = f, by { ext y, exact h' y }, rwa this }

lemma differentiable_at.fderiv_congr' (h : differentiable_at k f x)
  (hL : {y | f₁ y = f y} ∈ nhds x) (hx : f₁ x = f x) :
  fderiv k f₁ x = fderiv k f x :=
has_fderiv_at.fderiv (has_fderiv_at_filter.congr' h.has_fderiv_at hL hx)

end congr

/- id -/
section id

theorem has_fderiv_at_filter_id (x : E) (L : filter E) :
  has_fderiv_at_filter id (id : E →L[k] E) x L :=
(is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_within_at_id (x : E) (s : set E) :
  has_fderiv_within_at id (id : E →L[k] E) s x :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_id (x : E) : has_fderiv_at id (id : E →L[k] E) x :=
has_fderiv_at_filter_id _ _

lemma differentiable_at_id : differentiable_at k id x :=
(has_fderiv_at_id x).differentiable_at

lemma differentiable_within_at_id : differentiable_within_at k id s x :=
differentiable_at_id.differentiable_within_at

lemma differentiable_id : differentiable k (id : E → E) :=
λx, differentiable_at_id

lemma differentiable_on_id : differentiable_on k id s :=
differentiable_id.differentiable_on

lemma fderiv_id : fderiv k id x = id :=
has_fderiv_at.fderiv (has_fderiv_at_id x)

lemma fderiv_within_id (hxs : unique_diff_within_at k s x) :
  fderiv_within k id s x = id :=
begin
  rw differentiable.fderiv_within (differentiable_at_id) hxs,
  exact fderiv_id
end

end id

/- constants -/
section const

theorem has_fderiv_at_filter_const (c : F) (x : E) (L : filter E) :
  has_fderiv_at_filter (λ x, c) (0 : E →L[k] F) x L :=
(is_o_zero _ _).congr_left $ λ _, by simp only [zero_apply, sub_self]

theorem has_fderiv_within_at_const (c : F) (x : E) (s : set E) :
  has_fderiv_within_at (λ x, c) (0 : E →L[k] F) s x :=
has_fderiv_at_filter_const _ _ _

theorem has_fderiv_at_const (c : F) (x : E) :
  has_fderiv_at (λ x, c) (0 : E →L[k] F) x :=
has_fderiv_at_filter_const _ _ _

lemma differentiable_at_const (c : F) : differentiable_at k (λx, c) x :=
⟨0, has_fderiv_at_const c x⟩

lemma differentiable_within_at_const (c : F) : differentiable_within_at k (λx, c) s x :=
differentiable_at.differentiable_within_at (differentiable_at_const _)

lemma fderiv_const (c : F) : fderiv k (λy, c) x = 0 :=
has_fderiv_at.fderiv (has_fderiv_at_const c x)

lemma fderiv_within_const (c : F) (hxs : unique_diff_within_at k s x) :
  fderiv_within k (λy, c) s x = 0 :=
begin
  rw differentiable.fderiv_within (differentiable_at_const _) hxs,
  exact fderiv_const _
end

lemma differentiable_const (c : F) : differentiable k (λx : E, c) :=
λx, differentiable_at_const _

lemma differentiable_on_const (c : F) : differentiable_on k (λx, c) s :=
(differentiable_const _).differentiable_on

end const

/- Bounded linear maps -/
section is_bounded_linear_map

lemma is_bounded_linear_map.has_fderiv_at_filter (h : is_bounded_linear_map k f) :
  has_fderiv_at_filter f h.to_bounded_linear_map x L :=
begin
  have : (λ (x' : E), f x' - f x - h.to_bounded_linear_map (x' - x)) = λx', 0,
  { ext,
    have : ∀a, h.to_bounded_linear_map a = f a := λa, rfl,
    simp,
    simp [this] },
  rw [has_fderiv_at_filter, this],
  exact asymptotics.is_o_zero _ _
end

lemma is_bounded_linear_map.has_fderiv_within_at (h : is_bounded_linear_map k f) :
  has_fderiv_within_at f h.to_bounded_linear_map s x :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.has_fderiv_at (h : is_bounded_linear_map k f) :
  has_fderiv_at f h.to_bounded_linear_map x  :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.differentiable_at (h : is_bounded_linear_map k f) :
  differentiable_at k f x :=
h.has_fderiv_at.differentiable_at

lemma is_bounded_linear_map.differentiable_within_at (h : is_bounded_linear_map k f) :
  differentiable_within_at k f s x :=
h.differentiable_at.differentiable_within_at

lemma is_bounded_linear_map.fderiv (h : is_bounded_linear_map k f) :
  fderiv k f x = h.to_bounded_linear_map :=
has_fderiv_at.fderiv (h.has_fderiv_at)

lemma is_bounded_linear_map.fderiv_within (h : is_bounded_linear_map k f)
  (hxs : unique_diff_within_at k s x) : fderiv_within k f s x = h.to_bounded_linear_map :=
begin
  rw differentiable.fderiv_within h.differentiable_at hxs,
  exact h.fderiv
end

lemma is_bounded_linear_map.differentiable (h : is_bounded_linear_map k f) :
  differentiable k f :=
λx, h.differentiable_at

lemma is_bounded_linear_map.differentiable_on (h : is_bounded_linear_map k f) :
  differentiable_on k f s :=
h.differentiable.differentiable_on

end is_bounded_linear_map

/- multiplication by a constant -/
section smul_const

theorem has_fderiv_at_filter.smul (h : has_fderiv_at_filter f f' x L) (c : k) :
  has_fderiv_at_filter (λ x, c • f x) (c • f') x L :=
(is_o_const_smul_left h c).congr_left $ λ x, by simp [smul_neg, smul_add]

theorem has_fderiv_within_at.smul (h : has_fderiv_within_at f f' s x) (c : k) :
  has_fderiv_within_at (λ x, c • f x) (c • f') s x :=
h.smul c

theorem has_fderiv_at.smul (h : has_fderiv_at f f' x) (c : k) :
  has_fderiv_at (λ x, c • f x) (c • f') x :=
h.smul c

lemma differentiable_within_at.smul (h : differentiable_within_at k f s x) (c : k) :
  differentiable_within_at k (λy, c • f y) s x :=
(h.has_fderiv_within_at.smul c).differentiable_within_at

lemma differentiable_at.smul (h : differentiable_at k f x) (c : k) :
  differentiable_at k (λy, c • f y) x :=
(h.has_fderiv_at.smul c).differentiable_at

lemma differentiable_on.smul (h : differentiable_on k f s) (c : k) :
  differentiable_on k (λy, c • f y) s :=
λx hx, (h x hx).smul c

lemma differentiable.smul (h : differentiable k f) (c : k) :
  differentiable k (λy, c • f y) :=
λx, (h x).smul c

lemma fderiv_within_smul (hxs : unique_diff_within_at k s x)
  (h : differentiable_within_at k f s x) (c : k) :
  fderiv_within k (λy, c • f y) s x = c • fderiv_within k f s x :=
(h.has_fderiv_within_at.smul c).fderiv_within hxs

lemma fderiv_smul (h : differentiable_at k f x) (c : k) :
  fderiv k (λy, c • f y) x = c • fderiv k f x :=
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
  (hf : differentiable_within_at k f s x) (hg : differentiable_within_at k g s x) :
  differentiable_within_at k (λ y, f y + g y) s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.add
  (hf : differentiable_at k f x) (hg : differentiable_at k g x) :
  differentiable_at k (λ y, f y + g y) x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).differentiable_at

lemma differentiable_on.add
  (hf : differentiable_on k f s) (hg : differentiable_on k g s) :
  differentiable_on k (λy, f y + g y) s :=
λx hx, (hf x hx).add (hg x hx)

lemma differentiable.add
  (hf : differentiable k f) (hg : differentiable k g) :
  differentiable k (λy, f y + g y) :=
λx, (hf x).add (hg x)

lemma fderiv_within_add (hxs : unique_diff_within_at k s x)
  (hf : differentiable_within_at k f s x) (hg : differentiable_within_at k g s x) :
  fderiv_within k (λy, f y + g y) s x = fderiv_within k f s x + fderiv_within k g s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_add
  (hf : differentiable_at k f x) (hg : differentiable_at k g x) :
  fderiv k (λy, f y + g y) x = fderiv k f x + fderiv k g x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).fderiv

end add

/- neg -/
section neg

theorem has_fderiv_at_filter.neg (h : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (λ x, -f x) (-f') x L :=
(h.smul (-1:k)).congr (by simp) (by simp)

theorem has_fderiv_within_at.neg (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_fderiv_at.neg (h : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, -f x) (-f') x :=
h.neg

lemma differentiable_within_at.neg (h : differentiable_within_at k f s x) :
  differentiable_within_at k (λy, -f y) s x :=
h.has_fderiv_within_at.neg.differentiable_within_at

lemma differentiable_at.neg (h : differentiable_at k f x) :
  differentiable_at k (λy, -f y) x :=
h.has_fderiv_at.neg.differentiable_at

lemma differentiable_on.neg (h : differentiable_on k f s) :
  differentiable_on k (λy, -f y) s :=
λx hx, (h x hx).neg

lemma differentiable.neg (h : differentiable k f) :
  differentiable k (λy, -f y) :=
λx, (h x).neg

lemma fderiv_within_neg (hxs : unique_diff_within_at k s x)
  (h : differentiable_within_at k f s x) :
  fderiv_within k (λy, -f y) s x = - fderiv_within k f s x :=
h.has_fderiv_within_at.neg.fderiv_within hxs

lemma fderiv_neg (h : differentiable_at k f x) :
  fderiv k (λy, -f y) x = - fderiv k f x :=
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
  (hf : differentiable_within_at k f s x) (hg : differentiable_within_at k g s x) :
  differentiable_within_at k (λ y, f y - g y) s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.sub
  (hf : differentiable_at k f x) (hg : differentiable_at k g x) :
  differentiable_at k (λ y, f y - g y) x :=
(hf.has_fderiv_at.sub hg.has_fderiv_at).differentiable_at

lemma differentiable_on.sub
  (hf : differentiable_on k f s) (hg : differentiable_on k g s) :
  differentiable_on k (λy, f y - g y) s :=
λx hx, (hf x hx).sub (hg x hx)

lemma differentiable.sub
  (hf : differentiable k f) (hg : differentiable k g) :
  differentiable k (λy, f y - g y) :=
λx, (hf x).sub (hg x)

lemma fderiv_within_sub (hxs : unique_diff_within_at k s x)
  (hf : differentiable_within_at k f s x) (hg : differentiable_within_at k g s x) :
  fderiv_within k (λy, f y - g y) s x = fderiv_within k f s x - fderiv_within k g s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_sub
  (hf : differentiable_at k f x) (hg : differentiable_at k g x) :
  fderiv k (λy, f y - g y) x = fderiv k f x - fderiv k g x :=
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

theorem has_fderiv_within_at.continuous_at_within
  (h : has_fderiv_within_at f f' s x) : continuous_at_within f x s :=
has_fderiv_at_filter.tendsto_nhds lattice.inf_le_left h

theorem has_fderiv_at.continuous_at (h : has_fderiv_at f f' x) :
  continuous_at f x :=
has_fderiv_at_filter.tendsto_nhds (le_refl _) h

lemma differentiable_within_at.continuous_at_within (h : differentiable_within_at k f s x) :
  continuous_at_within f x s :=
let ⟨f', hf'⟩ := h in hf'.continuous_at_within

lemma differentiable_at.continuous_at (h : differentiable_at k f x) : continuous_at f x :=
let ⟨f', hf'⟩ := h in hf'.continuous_at

lemma differentiable_on.continuous_on (h : differentiable_on k f s) : continuous_on f s :=
λx hx, (h x hx).continuous_at_within

lemma differentiable.continuous (h : differentiable k f) : continuous f :=
continuous_iff_continuous_at.2 $ λx, (h x).continuous_at

end continuous

/- Bounded bilinear maps -/

section bilinear_map
variables {b : E × F → G} {u : set (E × F) }

lemma is_bounded_bilinear_map.has_fderiv_at (h : is_bounded_bilinear_map k b) (p : E × F) :
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
        continuous.comp (continuous_sub continuous_id continuous_const) continuous_norm,
      exact this.tendsto p },
    simp only [forall_prop_of_false, not_false_iff, one_ne_zero, forall_true_iff] },
  simp only [one_mul, asymptotics.is_o_norm_right] at B,
  exact A.trans_is_o B
end

lemma is_bounded_bilinear_map.has_fderiv_within_at (h : is_bounded_bilinear_map k b) (p : E × F) :
  has_fderiv_within_at b (h.deriv p) u p :=
(h.has_fderiv_at p).has_fderiv_within_at

lemma is_bounded_bilinear_map.differentiable_at (h : is_bounded_bilinear_map k b) (p : E × F) :
  differentiable_at k b p :=
(h.has_fderiv_at p).differentiable_at

lemma is_bounded_bilinear_map.differentiable_within_at (h : is_bounded_bilinear_map k b) (p : E × F) :
  differentiable_within_at k b u p :=
(h.differentiable_at p).differentiable_within_at

lemma is_bounded_bilinear_map.fderiv (h : is_bounded_bilinear_map k b) (p : E × F) :
  fderiv k b p = h.deriv p :=
has_fderiv_at.fderiv (h.has_fderiv_at p)

lemma is_bounded_bilinear_map.fderiv_within (h : is_bounded_bilinear_map k b) (p : E × F)
  (hxs : unique_diff_within_at k u p) : fderiv_within k b u p = h.deriv p :=
begin
  rw differentiable.fderiv_within (h.differentiable_at p) hxs,
  exact h.fderiv p
end

lemma is_bounded_bilinear_map.differentiable (h : is_bounded_bilinear_map k b) :
  differentiable k b :=
λx, h.differentiable_at x

lemma is_bounded_bilinear_map.differentiable_on (h : is_bounded_bilinear_map k b) :
  differentiable_on k b u :=
h.differentiable.differentiable_on

lemma is_bounded_bilinear_map.continuous (h : is_bounded_bilinear_map k b) :
  continuous b :=
h.differentiable.continuous

end bilinear_map


/- Cartesian products -/
section cartesian_product
variables {f₂ : E → G} {f₂' : E →L[k] G}

lemma has_fderiv_at_filter.prod
  (hf₁ : has_fderiv_at_filter f₁ f₁' x L) (hf₂ : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λx, (f₁ x, f₂ x)) (bounded_linear_map.prod f₁' f₂') x L :=
begin
  have : (λ (x' : E), (f₁ x', f₂ x') - (f₁ x, f₂ x) - (bounded_linear_map.prod f₁' f₂') (x' -x)) =
           (λ (x' : E), (f₁ x' - f₁ x - f₁' (x' - x), f₂ x' - f₂ x - f₂' (x' - x))) := rfl,
  rw [has_fderiv_at_filter, this],
  rw [asymptotics.is_o_prod_left],
  exact ⟨hf₁, hf₂⟩
end

lemma has_fderiv_within_at.prod
  (hf₁ : has_fderiv_within_at f₁ f₁' s x) (hf₂ : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λx, (f₁ x, f₂ x)) (bounded_linear_map.prod f₁' f₂') s x :=
hf₁.prod hf₂

lemma has_fderiv_at.prod (hf₁ : has_fderiv_at f₁ f₁' x) (hf₂ : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λx, (f₁ x, f₂ x)) (bounded_linear_map.prod f₁' f₂') x :=
hf₁.prod hf₂

lemma differentiable_within_at.prod
  (hf₁ : differentiable_within_at k f₁ s x) (hf₂ : differentiable_within_at k f₂ s x) :
  differentiable_within_at k (λx:E, (f₁ x, f₂ x)) s x :=
(hf₁.has_fderiv_within_at.prod hf₂.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.prod (hf₁ : differentiable_at k f₁ x) (hf₂ : differentiable_at k f₂ x) :
  differentiable_at k (λx:E, (f₁ x, f₂ x)) x :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).differentiable_at

lemma differentiable_on.prod (hf₁ : differentiable_on k f₁ s) (hf₂ : differentiable_on k f₂ s) :
  differentiable_on k (λx:E, (f₁ x, f₂ x)) s :=
λx hx, differentiable_within_at.prod (hf₁ x hx) (hf₂ x hx)

lemma differentiable.prod (hf₁ : differentiable k f₁) (hf₂ : differentiable k f₂) :
  differentiable k (λx:E, (f₁ x, f₂ x)) :=
λ x, differentiable_at.prod (hf₁ x) (hf₂ x)

lemma differentiable_at.fderiv_prod
  (hf₁ : differentiable_at k f₁ x) (hf₂ : differentiable_at k f₂ x) :
  fderiv k (λx:E, (f₁ x, f₂ x)) x =
    bounded_linear_map.prod (fderiv k f₁ x) (fderiv k f₂ x) :=
has_fderiv_at.fderiv (has_fderiv_at.prod hf₁.has_fderiv_at hf₂.has_fderiv_at)

lemma differentiable_at.fderiv_within_prod
  (hf₁ : differentiable_within_at k f₁ s x) (hf₂ : differentiable_within_at k f₂ s x)
  (hxs : unique_diff_within_at k s x) :
  fderiv_within k (λx:E, (f₁ x, f₂ x)) s x =
    bounded_linear_map.prod (fderiv_within k f₁ s x) (fderiv_within k f₂ s x) :=
begin
  apply has_fderiv_within_at.fderiv_within _ hxs,
  exact has_fderiv_within_at.prod hf₁.has_fderiv_within_at hf₂.has_fderiv_within_at
end

end cartesian_product

/- Composition -/
section composition

theorem has_fderiv_at_filter.comp {g : F → G} {g' : F →L[k] G}
  (hf : has_fderiv_at_filter f f' x L)
  (hg : has_fderiv_at_filter g g' (f x) (L.map f)) :
  has_fderiv_at_filter (g ∘ f) (g'.comp f') x L :=
let eq₁ := (g'.is_O_comp _ _).trans_is_o hf in
let eq₂ := ((hg.comp f).mono le_comap_map).trans_is_O hf.is_O_sub in
by { refine eq₂.tri (eq₁.congr_left (λ x', _)), simp }

/- A readable version of the previous theorem,
   a general form of the chain rule. -/

example {g : F → G} {g' : F →L[k] G}
  (hf : has_fderiv_at_filter f f' x L)
  (hg : has_fderiv_at_filter g g' (f x) (L.map f)) :
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

theorem has_fderiv_within_at.comp {g : F → G} {g' : F →L[k] G}
  (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at g g' (f '' s) (f x)) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
hf.comp (has_fderiv_at_filter.mono hg
  hf.continuous_at_within.tendsto_nhds_within_image)

/-- The chain rule. -/
theorem has_fderiv_at.comp {g : F → G} {g' : F →L[k] G}
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' (f x)) :
  has_fderiv_at (g ∘ f) (g'.comp f') x :=
hf.comp (hg.mono hf.continuous_at)

theorem has_fderiv_within_at.comp_has_fderiv_at {g : F → G} {g' : F →L[k] G}
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_at g g' (f x)) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
begin
  rw ← has_fderiv_within_univ_at at hg,
  exact has_fderiv_within_at.comp hf (hg.mono (subset_univ _))
end

lemma differentiable_within_at.comp {g : F → G} {t : set F}
  (hf : differentiable_within_at k f s x) (hg : differentiable_within_at k g t (f x))
  (h : f '' s ⊆ t) : differentiable_within_at k (g ∘ f) s x :=
begin
  rcases hf with ⟨f', hf'⟩,
  rcases hg with ⟨g', hg'⟩,
  exact ⟨bounded_linear_map.comp g' f', has_fderiv_within_at.comp hf' (hg'.mono h)⟩
end

lemma differentiable_at.comp {g : F → G}
  (hf : differentiable_at k f x) (hg : differentiable_at k g (f x)) :
  differentiable_at k (g ∘ f) x :=
(hf.has_fderiv_at.comp hg.has_fderiv_at).differentiable_at

lemma fderiv_within.comp {g : F → G} {t : set F}
  (hf : differentiable_within_at k f s x) (hg : differentiable_within_at k g t (f x))
  (h : f '' s ⊆ t) (hxs : unique_diff_within_at k s x) :
  fderiv_within k (g ∘ f) s x =
    bounded_linear_map.comp (fderiv_within k g t (f x)) (fderiv_within k f s x) :=
begin
  apply has_fderiv_within_at.fderiv_within _ hxs,
  apply has_fderiv_within_at.comp (hf.has_fderiv_within_at),
  apply hg.has_fderiv_within_at.mono h
end

lemma fderiv.comp {g : F → G}
  (hf : differentiable_at k f x) (hg : differentiable_at k g (f x)) :
  fderiv k (g ∘ f) x = bounded_linear_map.comp (fderiv k g (f x)) (fderiv k f x) :=
begin
  apply has_fderiv_at.fderiv,
  exact has_fderiv_at.comp hf.has_fderiv_at hg.has_fderiv_at
end

lemma differentiable_on.comp {g : F → G} {t : set F}
  (hf : differentiable_on k f s) (hg : differentiable_on k g t) (st : f '' s ⊆ t) :
  differentiable_on k (g ∘ f) s :=
λx hx, differentiable_within_at.comp (hf x hx) (hg (f x) (st (mem_image_of_mem _ hx))) st

end composition

/- Multiplication by a scalar function -/
section smul
variables {c : E → k} {c' : E →L[k] k}

theorem has_fderiv_within_at.smul'
  (hc : has_fderiv_within_at c c' s x) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ y, c y • f y) (c x • f' + c'.scalar_prod_space_iso (f x)) s x :=
begin
  have : is_bounded_bilinear_map k (λ (p : k × F), p.1 • p.2) := is_bounded_bilinear_map_smul,
  exact (hc.prod hf).comp_has_fderiv_at (this.has_fderiv_at (c x, f x))
end

theorem has_fderiv_at.smul' (hc : has_fderiv_at c c' x) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ y, c y • f y) (c x • f' + c'.scalar_prod_space_iso (f x)) x :=
begin
  have : is_bounded_bilinear_map k (λ (p : k × F), p.1 • p.2) := is_bounded_bilinear_map_smul,
  exact (hc.prod hf).comp (this.has_fderiv_at (c x, f x))
end

lemma differentiable_within_at.smul'
  (hc : differentiable_within_at k c s x) (hf : differentiable_within_at k f s x) :
  differentiable_within_at k (λ y, c y • f y) s x :=
(hc.has_fderiv_within_at.smul' hf.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.smul' (hc : differentiable_at k c x) (hf : differentiable_at k f x) :
  differentiable_at k (λ y, c y • f y) x :=
(hc.has_fderiv_at.smul' hf.has_fderiv_at).differentiable_at

lemma differentiable_on.smul' (hc : differentiable_on k c s) (hf : differentiable_on k f s) :
  differentiable_on k (λ y, c y • f y) s :=
λx hx, (hc x hx).smul' (hf x hx)

lemma differentiable.smul' (hc : differentiable k c) (hf : differentiable k f) :
  differentiable k (λ y, c y • f y) :=
λx, (hc x).smul' (hf x)

lemma fderiv_within_smul' (hxs : unique_diff_within_at k s x)
  (hc : differentiable_within_at k c s x) (hf : differentiable_within_at k f s x) :
  fderiv_within k (λ y, c y • f y) s x =
    c x • fderiv_within k f s x + (fderiv_within k c s x).scalar_prod_space_iso (f x) :=
(hc.has_fderiv_within_at.smul' hf.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_smul' (hc : differentiable_at k c x) (hf : differentiable_at k f x) :
  fderiv k (λ y, c y • f y) x =
    c x • fderiv k f x + (fderiv k c x).scalar_prod_space_iso (f x) :=
(hc.has_fderiv_at.smul' hf.has_fderiv_at).fderiv

end smul


/- Multiplication of scalar functions -/

section mul
variables {c d : E → k} {c' d' : E →L[k] k}

theorem has_fderiv_within_at.mul
  (hc : has_fderiv_within_at c c' s x) (hd : has_fderiv_within_at d d' s x) :
  has_fderiv_within_at (λ y, c y * d y) (c x • d' + d x • c') s x :=
begin
  have : is_bounded_bilinear_map k (λ (p : k × k), p.1 * p.2) := is_bounded_bilinear_map_mul,
  convert (hc.prod hd).comp_has_fderiv_at (this.has_fderiv_at (c x, d x)),
  ext z,
  change c x * d' z + d x * c' z = c x * d' z + c' z * d x,
  ring
end

theorem has_fderiv_at.mul (hc : has_fderiv_at c c' x) (hd : has_fderiv_at d d' x) :
  has_fderiv_at (λ y, c y * d y) (c x • d' + d x • c') x :=
begin
  have : is_bounded_bilinear_map k (λ (p : k × k), p.1 * p.2) := is_bounded_bilinear_map_mul,
  convert (hc.prod hd).comp (this.has_fderiv_at (c x, d x)),
  ext z,
  change c x * d' z + d x * c' z = c x * d' z + c' z * d x,
  ring
end

lemma differentiable_within_at.mul
  (hc : differentiable_within_at k c s x) (hd : differentiable_within_at k d s x) :
  differentiable_within_at k (λ y, c y * d y) s x :=
(hc.has_fderiv_within_at.mul hd.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.mul (hc : differentiable_at k c x) (hd : differentiable_at k d x) :
  differentiable_at k (λ y, c y * d y) x :=
(hc.has_fderiv_at.mul hd.has_fderiv_at).differentiable_at

lemma differentiable_on.mul (hc : differentiable_on k c s) (hd : differentiable_on k d s) :
  differentiable_on k (λ y, c y * d y) s :=
λx hx, (hc x hx).mul (hd x hx)

lemma differentiable.mul (hc : differentiable k c) (hd : differentiable k d) :
  differentiable k (λ y, c y * d y) :=
λx, (hc x).mul (hd x)

lemma fderiv_within_mul (hxs : unique_diff_within_at k s x)
  (hc : differentiable_within_at k c s x) (hd : differentiable_within_at k d s x) :
  fderiv_within k (λ y, c y * d y) s x =
    c x • fderiv_within k d s x + d x • fderiv_within k c s x :=
(hc.has_fderiv_within_at.mul hd.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_mul (hc : differentiable_at k c x) (hd : differentiable_at k d x) :
  fderiv k (λ y, c y * d y) x =
    c x • fderiv k d x + d x • fderiv k c x :=
(hc.has_fderiv_at.mul hd.has_fderiv_at).fderiv

end mul

end
/-
  In the special case of a normed space over the reals,
  we can use  scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/

section

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]
variables {G : Type*} [normed_space ℝ G]

set_option class.instance_max_depth 34

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
