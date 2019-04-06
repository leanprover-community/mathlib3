/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The Fréchet derivative.

Let `E` and `F` be normed spaces, and `f : E → F`. Then

  `has_fderiv_at_within f f' x s`

says that the function `f' : E → F` is a bounded linear map and `f` has derivative `f'` at
`x`, where the domain of interest is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_at_within f f' x univ`

The derivative is defined in terms of the `is_o` relation, but also characterized in terms of
the `tendsto` relation.
-/
import analysis.normed_space.bounded_linear_maps analysis.asymptotics
import topology.basic tactic.abel
open filter asymptotics bounded_linear_map

section

variables (k : Type*) [normed_field k]
variables {E : Type*} [normed_space k E]
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]
include k

def has_fderiv_at_filter (f : E → F) (f' : E →L[k] F) (x : E) (L : filter E) :=
  is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L

def has_fderiv_at_within (f : E → F) (f' : E →L[k] F) (x : E) (s : set E) :=
has_fderiv_at_filter k f f' x (nhds_within x s)

def has_fderiv_at (f : E → F) (f' : E →L[k] F) (x : E) :=
has_fderiv_at_filter k f f' x (nhds x)

variable {k}

variables {f  f₀  f₁  : E → F}     {g  : E → F}
variables {f' f₀' f₁' : E →L[k] F} {g' : E →L[k] F}
variables {x : E} {s t : set E} {L L₁ L₂: filter E}

theorem has_fderiv_at_filter_iff_tendsto : has_fderiv_at_filter k f f' x L ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) L (nhds 0) :=
begin
  suffices t : is_o (λ x', f x' - f x - f' (x' - x)) (λ x', x' - x) L ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) L (nhds 0), from
  (iff_congr ⟨id, id⟩ ⟨id, id⟩).1 t,

  have h : ∀ x', ∥x' - x∥ = 0 → ∥f x' - f x - f' (x' - x)∥ = 0, from
  λ x' hx', by rw [norm_eq_zero, sub_eq_zero_iff_eq] at hx'; rw hx'; simp,

  rw [←is_o_norm_left, ←is_o_norm_right, is_o_iff_tendsto h],
  exact tendsto.congr'r (λ x', mul_comm _ _),
end

theorem has_fderiv_at_within_iff_tendsto :
  has_fderiv_at_within k f f' x s ↔ tendsto
  (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds_within x s) (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_tendsto :
  has_fderiv_at k f f' x ↔ tendsto
  (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) (nhds x) (nhds 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_filter.mono (hst : L₁ ≤ L₂) :
  has_fderiv_at_filter k f f' x L₂ → has_fderiv_at_filter k f f' x L₁ :=
(is_o.mono hst)

theorem has_fderiv_at_within.mono (hst : s ⊆ t) :
  has_fderiv_at_within k f f' x t → has_fderiv_at_within k f f' x s :=
has_fderiv_at_filter.mono (nhds_within_mono _ hst)

theorem has_fderiv_at_filter_of_has_fderiv_at
  (hL : L ≤ nhds x) (h : has_fderiv_at k f f' x) :
  has_fderiv_at_filter k f f' x L :=
h.mono hL

theorem has_fderiv_at_within_of_has_fderiv_at :
  has_fderiv_at k f f' x → has_fderiv_at_within k f f' x s :=
has_fderiv_at_filter_of_has_fderiv_at lattice.inf_le_left

theorem has_fderiv_at_filter_congr'
  (hx : f₀ x = f₁ x) (h₀ : {x | f₀ x = f₁ x} ∈ L) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter k f₀ f₀' x L ↔ has_fderiv_at_filter k f₁ f₁' x L :=
by rw (ext h₁); exact is_o_congr
  (by filter_upwards [h₀] λ _, by simp [hx])
  (univ_mem_sets' $ λ _, rfl)

theorem has_fderiv_at_filter_congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter k f₀ f₀' x L ↔ has_fderiv_at_filter k f₁ f₁' x L :=
has_fderiv_at_filter_congr' (h₀ _) (univ_mem_sets' h₀) h₁

theorem has_fderiv_at_filter.congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter k f₀ f₀' x L → has_fderiv_at_filter k f₁ f₁' x L :=
(has_fderiv_at_filter_congr h₀ h₁).1

theorem has_fderiv_at_within_congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_within k f₀ f₀' x s ↔ has_fderiv_at_within k f₁ f₁' x s :=
has_fderiv_at_filter_congr h₀ h₁

theorem has_fderiv_at_within.congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_within k f₀ f₀' x s → has_fderiv_at_within k f₁ f₁' x s :=
(has_fderiv_at_within_congr h₀ h₁).1

theorem has_fderiv_at_congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at k f₀ f₀' x ↔ has_fderiv_at k f₁ f₁' x :=
has_fderiv_at_filter_congr h₀ h₁

theorem has_fderiv_at.congr
  (h₀ : ∀ x, f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at k f₀ f₀' x → has_fderiv_at k f₁ f₁' x :=
(has_fderiv_at_congr h₀ h₁).1

theorem has_fderiv_at_filter_id (x : E) (L : filter E) :
  has_fderiv_at_filter k id 1 x L := (is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_at_within_id (x : E) (s : set E) :
  has_fderiv_at_within k id 1 x s :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_id (x : E) : has_fderiv_at k id 1 x :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_filter_const (c : F) (x : E) (L : filter E) :
  has_fderiv_at_filter k (λ x, c) 0 x L :=
(is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_at_within_const (c : F) (x : E) (s : set E) :
  has_fderiv_at_within k (λ x, c) 0 x s :=
has_fderiv_at_filter_const _ _ _

theorem has_fderiv_at_const (c : F) (x : E) :
  has_fderiv_at k (λ x, c) 0 x :=
has_fderiv_at_filter_const _ _ _

set_option class.instance_max_depth 43

theorem has_fderiv_at_filter_smul
  (c : k) (h : has_fderiv_at_filter k f f' x L) :
  has_fderiv_at_filter k (λ x, c • f x) (c • f') x L :=
(is_o_const_smul_left h c).congr_left $ by simp [smul_neg, smul_add]

theorem has_fderiv_at_within_smul
  (c : k) : has_fderiv_at_within k f f' x s →
  has_fderiv_at_within k (λ x, c • f x) (c • f') x s :=
has_fderiv_at_filter_smul _

theorem has_fderiv_at_smul
  (c : k) : has_fderiv_at k f f' x →
  has_fderiv_at k (λ x, c • f x) (c • f') x :=
has_fderiv_at_filter_smul _

theorem has_fderiv_at_filter_add
  (hf : has_fderiv_at_filter k f f' x L)
  (hg : has_fderiv_at_filter k g g' x L) :
  has_fderiv_at_filter k (λ x, f x + g x) (f' + g') x L :=
(hf.add hg).congr_left $ by simp


theorem has_fderiv_at_within_add :
  has_fderiv_at_within k f f' x s → has_fderiv_at_within k g g' x s →
  has_fderiv_at_within k (λ x, f x + g x) (f' + g') x s :=
has_fderiv_at_filter_add

theorem has_fderiv_at_add :
  has_fderiv_at k f f' x → has_fderiv_at k g g' x →
  has_fderiv_at k (λ x, f x + g x) (f' + g') x :=
has_fderiv_at_filter_add

theorem has_fderiv_at_filter_neg (h : has_fderiv_at_filter k f f' x L) :
  has_fderiv_at_filter k (λ x, -f x) (-f') x L :=
(has_fderiv_at_filter_smul (-1 : k) h).congr (by simp) (by simp)

theorem has_fderiv_at_within_neg :
  has_fderiv_at_within k f f' x s →
  has_fderiv_at_within k (λ x, -f x) (-f') x s :=
has_fderiv_at_filter_neg

theorem has_fderiv_at_neg :
  has_fderiv_at k f f' x → has_fderiv_at k (λ x, -f x) (-f') x :=
has_fderiv_at_filter_neg

theorem has_fderiv_at_filter_sub
  (hf : has_fderiv_at_filter k f f' x L)
  (hg : has_fderiv_at_filter k g g' x L) :
  has_fderiv_at_filter k (λ x, f x - g x) (f' - g') x L :=
has_fderiv_at_filter_add hf (has_fderiv_at_filter_neg hg)

theorem has_fderiv_at_within_sub :
  has_fderiv_at_within k f f' x s → has_fderiv_at_within k g g' x s →
  has_fderiv_at_within k (λ x, f x - g x) (f' - g') x s :=
has_fderiv_at_filter_sub

theorem has_fderiv_at_sub :
  has_fderiv_at k f f' x → has_fderiv_at k g g' x →
  has_fderiv_at k (λ x, f x - g x) (f' - g') x :=
has_fderiv_at_filter_sub

theorem has_fderiv_at_filter.is_O_sub (h : has_fderiv_at_filter k f f' x L) :
  is_O (λ x', f x' - f x) (λ x', x' - x) L :=
  h.to_is_O.congr_of_sub.2 (f'.is_O_sub _ _)

theorem has_fderiv_at_filter.tendsto_nhds (hL : L ≤ nhds x)
  (h : has_fderiv_at_filter k f f' x L) : tendsto f L (nhds (f x)) :=
begin
have : tendsto (λ x', f x' - f x) L (nhds 0),
  { refine h.is_O_sub.trans_tendsto (tendsto_le_left hL _),
    rw ← sub_self x, exact tendsto_sub tendsto_id tendsto_const_nhds },
  have := tendsto_add this tendsto_const_nhds,
  rw zero_add (f x) at this,
  exact this.congr (by simp)
end

theorem has_fderiv_at_within.continuous_at_within :
  has_fderiv_at_within k f f' x s → continuous_at_within f x s :=
has_fderiv_at_filter.tendsto_nhds lattice.inf_le_left

theorem has_fderiv_at.continuous_at :
  has_fderiv_at k f f' x → continuous_at f x :=
has_fderiv_at_filter.tendsto_nhds (le_refl _)

theorem has_fderiv_at_filter.comp
  {g : F → G} {g' : F →L[k] G} {f : E → F} {f' :  E →L[k] F}
  {L : filter E} {x : E}
  (hf : has_fderiv_at_filter k f f' x L)
  (hg : has_fderiv_at_filter k g g' (f x) (L.map f)) :
  has_fderiv_at_filter k (g ∘ f) (g'.comp f') x L := sorry

theorem has_fderiv_at_within.comp
  {g : F → G} {g' : F →L[k] G} {f : E → F} {f' : E →L[k] F} {s : set E} {x : E}
  (hf : has_fderiv_at_within k f f' x s)
  (hg : has_fderiv_at_within k g g' (f x) (f '' s)) :
  has_fderiv_at_within k (g ∘ f) (g'.comp f') x s :=
hf.comp $ has_fderiv_at_filter.mono
  hf.continuous_at_within.tendsto_nhds_within_image hg

/-- The chain rule. -/
theorem has_fderiv_at.comp
  {g : F → G} {g' : F →L[k] G} {f : E → F} {f' : E →L[k] F} {x : E}
  (hf : has_fderiv_at k f f' x) (hg : has_fderiv_at k g g' (f x)) :
  has_fderiv_at k (g ∘ f) (g'.comp f') x :=
hf.comp $ hg.mono hf.continuous_at

end

/-
In the special case of a normed space over the reals, we can use scalar multiplication in the
`tendsto` characterization of the Fréchet derivative.
-/

section

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]
variables {G : Type*} [normed_space ℝ G]

set_option class.instance_max_depth 34

theorem has_fderiv_at_filter_real_equiv {f : E → F} {f' : E → F} {x : E} {L : filter E}
    (bf' : is_bounded_linear_map ℝ f') :
  tendsto (λ x' : E, ∥x' - x∥⁻¹ * ∥f x' - f x - f' (x' - x)∥) L (nhds 0) ↔
  tendsto (λ x' : E, ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x))) L (nhds 0) :=
begin
  have f'0 : f' 0 = 0 := (bf'.to_linear_map _).map_zero,
  symmetry, rw [tendsto_iff_norm_tendsto_zero], refine tendsto.congr'r (λ x', _),
  have : ∥x' + -x∥⁻¹ ≥ 0, from inv_nonneg.mpr (norm_nonneg _),
  simp [norm_smul, real.norm_eq_abs, abs_of_nonneg this]
end

end
