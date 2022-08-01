/-
Copyright (c) 2022 Heather Macbeth, Filippo Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Filippo Nuccio
-/
import analysis.mean_inequalities_pow

/-! # Changing the norm on a normed group by a power

This file contains the construction of a variant normed group structure, given an existing such
structure.  For each `0 < r ≤ 1`, there is a normed group structure with the norm `∥x∥ ^ r`.  The
only nontrivial point mathematically is the mean inequality `(a + b) ^ r ≤ a ^ r + b ^ r`.

The construction is `exponentiate_norm` (TODO: rename).  We are careful in the construction to
preserve the original `uniform_space` structure on the normed group.
-/

noncomputable theory
open_locale nnreal

-- TODO change `i` assumption to pseudo_metric_space
/-- Adjust the pseudo-metric-space structure on a normed group by raising the associated norm to the
power of `r`, with `r ≤ 1`, while keeping the uniformity intact. -/
def exponentiate_norm' {r : ℝ≥0} (hr₀ : 0 < r) (hr : r ≤ 1) (α : Type*)
  (i : seminormed_add_comm_group α) :
  pseudo_metric_space α :=
{ dist := λ x y, ∥x - y∥ ^ (r:ℝ),
  dist_self := λ x, begin
    have : (r:ℝ) ≠ 0 := by exact_mod_cast hr₀.ne',
    change (@has_norm.norm _ i.to_has_norm (x - x)) ^ (r:ℝ) = 0,
    rw [sub_self, _root_.norm_zero, real.zero_rpow this],
  end,
  dist_comm := λ x y, begin
    change (@has_norm.norm _ i.to_has_norm (x - y)) ^ (r:ℝ)
      = (@has_norm.norm _ i.to_has_norm (y - x)) ^ (r:ℝ),
    rw norm_sub_rev,
  end,
  dist_triangle := λ x y z, begin
    let i₂ : has_nnnorm α := @seminormed_add_comm_group.to_has_nnnorm _ i,
    let dxz := @has_nnnorm.nnnorm _ i₂ (x - z),
    let dxy := @has_nnnorm.nnnorm _ i₂ (x - y),
    let dyz := @has_nnnorm.nnnorm _ i₂ (y - z),
    have H₁ : dxz ≤ dxy + dyz,
    { dsimp [dxz],
      convert @nnnorm_add_le _ i (x - y) (y - z),
      abel },
    have : 0 ≤ (r:ℝ) := by exact_mod_cast hr₀.le,
    exact (nnreal.rpow_le_rpow H₁ this).trans (nnreal.rpow_add_le_add_rpow dxy dyz hr₀ hr)
  end }

lemma _root_.nnreal.lt_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) :
  x < y ^ (1 / z) ↔ x ^ z < y :=
sorry


-- TODO extract a lemma about `infi_eq_infi_iff` for this situation
/-- Adjust the pseudo-metric-space structure on a normed group by raising the associated norm to the
power of `r`, with `r ≤ 1`, while keeping the uniformity intact. -/
def exponentiate_norm.pseudo_metric_space {r : ℝ≥0} (hr₀ : 0 < r) (hr : r ≤ 1) (α : Type*)
  (i : seminormed_add_comm_group α) :
  pseudo_metric_space α :=
pseudo_metric_space.replace_uniformity (exponentiate_norm' hr₀ hr α i)
begin
  have : uniformity α = _ := pseudo_metric_space.uniformity_dist,
  rw this,
  let D₁ : α → α → ℝ≥0 := @has_nndist.nndist _
    (@pseudo_metric_space.to_has_nndist _ i.to_pseudo_metric_space),
  let D₂ : α → α → ℝ≥0 := @has_nndist.nndist _
    (@pseudo_metric_space.to_has_nndist _ (exponentiate_norm' hr₀ hr α i)),
  have hD₁D₂ : ∀ x y, D₂ x y = (D₁ x y) ^ (r:ℝ),
  { intros x y,
    change ∥x - y∥₊ ^ (r:ℝ) = _,
    rw ← nndist_eq_nnnorm },
  change (⨅ (ε : ℝ) (H : ε > 0), filter.principal {p : α × α | (D₁ p.1 p.2:ℝ) < ε})
    = ⨅ (ε : ℝ) (H : ε > 0), filter.principal {p : α × α | (D₂ p.1 p.2:ℝ) < ε},
  simp only [hD₁D₂],
  refine le_antisymm _ _,
  { rw infi_le_iff,
    intros b hb,
    refine le_infi _,
    intros ε,
    refine le_infi _,
    intros hε,
    refine ((hb (ε ^ (1/r:ℝ))).trans (infi_le _ _)).trans _,
    { sorry }, -- ε ^ (↑r)⁻¹ > 0
    rintros _ H,
    refine set.subset.trans _ H,
    intros p hp,
    dsimp at ⊢ hp,
    let ε' : ℝ≥0 := ⟨ε, le_of_lt hε⟩,
    have hε' : ε = (ε':ℝ) := rfl,
    rw hε' at ⊢ hp,
    norm_cast,
    have hp' : D₁ p.fst p.snd < ε' ^ (1 / (r:ℝ)) := by exact_mod_cast hp,
    rwa nnreal.lt_rpow_one_div_iff at hp',
    exact_mod_cast hr₀ },
  { sorry } -- SAME AGAIN
end

/-- Adjust the pseudo-metric-space structure on a normed group by raising the associated norm to the
power of `r`, with `r ≤ 1`, while keeping the uniformity intact. -/
def exponentiate_norm.seminormed_add_comm_group {r : ℝ≥0} (hr₀ : 0 < r) (hr : r ≤ 1) (α : Type*)
  (i : seminormed_add_comm_group α) :
  seminormed_add_comm_group α :=
{ norm := λ x, @has_norm.norm _ i.to_has_norm x ^ (r:ℝ),
  dist_eq := λ x y, rfl,
  .. exponentiate_norm.pseudo_metric_space hr₀ hr α i,
  .. i.to_add_comm_group }

-- TODO probably not all the boilerplate is needed
/-- Adjust the pseudo-metric-space structure on a normed group by raising the associated norm to the
power of `r`, with `r ≤ 1`, while keeping the uniformity intact. -/
def exponentiate_norm.normed_add_comm_group {r : ℝ≥0} (hr₀ : 0 < r) (hr : r ≤ 1) (α : Type*)
  (i : normed_add_comm_group α) :
  normed_add_comm_group α :=
{ eq_of_dist_eq_zero := λ x y h, begin
    let i₁ : seminormed_add_comm_group α := @normed_add_comm_group.to_seminormed_add_comm_group _ i,
    let D₁ : α → α → ℝ := @has_dist.dist _
      (@pseudo_metric_space.to_has_dist _ i₁.to_pseudo_metric_space),
    let D₂ : α → α → ℝ := @has_dist.dist _
      (@pseudo_metric_space.to_has_dist _ (exponentiate_norm' hr₀ hr α i₁)),
    have hD₁D₂ : ∀ x y, D₂ x y = (D₁ x y) ^ (r:ℝ),
    { intros x y,
      change ∥x - y∥ ^ (r:ℝ) = _,
      rw ← dist_eq_norm },
    change D₂ x y = 0 at h,
    rw [hD₁D₂, real.rpow_eq_zero_iff_of_nonneg] at h,
    { exact eq_of_dist_eq_zero h.1 },
    { exact dist_nonneg }
  end,
  .. exponentiate_norm.seminormed_add_comm_group hr₀ hr α
      (@normed_add_comm_group.to_seminormed_add_comm_group _ i) }
