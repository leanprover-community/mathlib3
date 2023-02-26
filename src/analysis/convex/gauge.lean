/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.basic
import analysis.normed_space.pointwise
import analysis.seminorm
import data.is_R_or_C.basic
import tactic.congrm

/-!
# The Minkowksi functional

This file defines the Minkowski functional, aka gauge.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a real vector space,
* `gauge`: Aka Minkowksi functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gauge_seminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

Minkowski functional, gauge
-/

open normed_field set
open_locale pointwise

noncomputable theory

variables {𝕜 E F : Type*}

section add_comm_group
variables [add_comm_group E] [module ℝ E]

/--The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : set E) (x : E) : ℝ := Inf {r : ℝ | 0 < r ∧ x ∈ r • s}

variables {s t : set E} {a : ℝ} {x : E}

lemma gauge_def : gauge s x = Inf {r ∈ set.Ioi 0 | x ∈ r • s} := rfl

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
lemma gauge_def' : gauge s x = Inf {r ∈ set.Ioi 0 | r⁻¹ • x ∈ s} :=
begin
  congrm Inf (λ r, _),
  exact and_congr_right (λ hr, mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _),
end

private lemma gauge_set_bdd_below : bdd_below {r : ℝ | 0 < r ∧ x ∈ r • s} := ⟨0, λ r hr, hr.1.le⟩

/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
lemma absorbent.gauge_set_nonempty (absorbs : absorbent ℝ s) :
  {r : ℝ | 0 < r ∧ x ∈ r • s}.nonempty :=
let ⟨r, hr₁, hr₂⟩ := absorbs x in ⟨r, hr₁, hr₂ r (real.norm_of_nonneg hr₁.le).ge⟩

lemma gauge_mono (hs : absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s :=
λ x, cInf_le_cInf gauge_set_bdd_below hs.gauge_set_nonempty $ λ r hr, ⟨hr.1, smul_set_mono h hr.2⟩

lemma exists_lt_of_gauge_lt (absorbs : absorbent ℝ s) (h : gauge s x < a) :
  ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s :=
begin
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_cInf_lt absorbs.gauge_set_nonempty h,
  exact ⟨b, hb, hba, hx⟩,
end

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp] lemma gauge_zero : gauge s 0 = 0 :=
begin
  rw gauge_def',
  by_cases (0 : E) ∈ s,
  { simp only [smul_zero, sep_true, h, cInf_Ioi] },
  { simp only [smul_zero, sep_false, h, real.Inf_empty] }
end

@[simp] lemma gauge_zero' : gauge (0 : set E) = 0 :=
begin
  ext,
  rw gauge_def',
  obtain rfl | hx := eq_or_ne x 0,
  { simp only [cInf_Ioi, mem_zero, pi.zero_apply, eq_self_iff_true, sep_true, smul_zero] },
  { simp only [mem_zero, pi.zero_apply, inv_eq_zero, smul_eq_zero],
    convert real.Inf_empty,
    exact eq_empty_iff_forall_not_mem.2 (λ r hr, hr.2.elim (ne_of_gt hr.1) hx) }
end

@[simp] lemma gauge_empty : gauge (∅ : set E) = 0 :=
by { ext, simp only [gauge_def', real.Inf_empty, mem_empty_iff_false, pi.zero_apply, sep_false] }

lemma gauge_of_subset_zero (h : s ⊆ 0) : gauge s = 0 :=
by { obtain rfl | rfl := subset_singleton_iff_eq.1 h, exacts [gauge_empty, gauge_zero'] }

/-- The gauge is always nonnegative. -/
lemma gauge_nonneg (x : E) : 0 ≤ gauge s x := real.Inf_nonneg _ $ λ x hx, hx.1.le

lemma gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) : gauge s (-x) = gauge s x :=
begin
  have : ∀ x, -x ∈ s ↔ x ∈ s := λ x, ⟨λ h, by simpa using symmetric _ h, symmetric x⟩,
  simp_rw [gauge_def', smul_neg, this]
end

lemma gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s x :=
by simp_rw [gauge_def', smul_neg, neg_mem_neg]

lemma gauge_neg_set_eq_gauge_neg (x : E) : gauge (-s) x = gauge s (-x) :=
by rw [← gauge_neg_set_neg, neg_neg]

lemma gauge_le_of_mem (ha : 0 ≤ a) (hx : x ∈ a • s) : gauge s x ≤ a :=
begin
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero] },
  { exact cInf_le gauge_set_bdd_below ⟨ha', hx⟩ }
end

lemma gauge_le_eq (hs₁ : convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : absorbent ℝ s) (ha : 0 ≤ a) :
  {x | gauge s x ≤ a} = ⋂ (r : ℝ) (H : a < r), r • s :=
begin
  ext,
  simp_rw [set.mem_Inter, set.mem_set_of_eq],
  refine ⟨λ h r hr, _, λ h, le_of_forall_pos_lt_add (λ ε hε, _)⟩,
  { have hr' := ha.trans_lt hr,
    rw mem_smul_set_iff_inv_smul_mem₀ hr'.ne',
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr),
    suffices : (r⁻¹ * δ) • δ⁻¹ • x ∈ s,
    { rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this },
    rw mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne' at hδ,
    refine hs₁.smul_mem_of_zero_mem hs₀ hδ ⟨by positivity, _⟩,
    rw [inv_mul_le_iff hr', mul_one],
    exact hδr.le },
  { have hε' := (lt_add_iff_pos_right a).2 (half_pos hε),
    exact (gauge_le_of_mem (ha.trans hε'.le) $ h _ hε').trans_lt
      (add_lt_add_left (half_lt_self hε) _) }
end

lemma gauge_lt_eq' (absorbs : absorbent ℝ s) (a : ℝ) :
  {x | gauge s x < a} = ⋃ (r : ℝ) (H : 0 < r) (H : r < a), r • s :=
begin
  ext,
  simp_rw [mem_set_of_eq, mem_Union, exists_prop],
  exact ⟨exists_lt_of_gauge_lt absorbs,
    λ ⟨r, hr₀, hr₁, hx⟩, (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩,
end

lemma gauge_lt_eq (absorbs : absorbent ℝ s) (a : ℝ) :
  {x | gauge s x < a} = ⋃ (r ∈ set.Ioo 0 (a : ℝ)), r • s :=
begin
  ext,
  simp_rw [mem_set_of_eq, mem_Union, exists_prop, mem_Ioo, and_assoc],
  exact ⟨exists_lt_of_gauge_lt absorbs,
    λ ⟨r, hr₀, hr₁, hx⟩, (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩,
end

lemma gauge_lt_one_subset_self (hs : convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} ⊆ s :=
begin
  rw gauge_lt_eq absorbs,
  refine set.Union₂_subset (λ r hr _, _),
  rintro ⟨y, hy, rfl⟩,
  exact hs.smul_mem_of_zero_mem h₀ hy (Ioo_subset_Icc_self hr),
end

lemma gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
gauge_le_of_mem zero_le_one $ by rwa one_smul

lemma self_subset_gauge_le_one : s ⊆ {x | gauge s x ≤ 1} := λ x, gauge_le_one_of_mem

lemma convex.gauge_le (hs : convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : absorbent ℝ s) (a : ℝ) :
  convex ℝ {x | gauge s x ≤ a} :=
begin
  by_cases ha : 0 ≤ a,
  { rw gauge_le_eq hs h₀ absorbs ha,
    exact convex_Inter (λ i, convex_Inter (λ hi, hs.smul _)) },
  { convert convex_empty,
    exact eq_empty_iff_forall_not_mem.2 (λ x hx, ha $ (gauge_nonneg _).trans hx) }
end

lemma balanced.star_convex (hs : balanced ℝ s) : star_convex ℝ 0 s :=
star_convex_zero_iff.2 $ λ x hx a ha₀ ha₁,
  hs _ (by rwa real.norm_of_nonneg ha₀) (smul_mem_smul_set hx)

lemma le_gauge_of_not_mem (hs₀ : star_convex ℝ 0 s) (hs₂ : absorbs ℝ s {x}) (hx : x ∉ a • s) :
  a ≤ gauge s x :=
begin
  rw star_convex_zero_iff at hs₀,
  obtain ⟨r, hr, h⟩ := hs₂,
  refine le_cInf ⟨r, hr, singleton_subset_iff.1 $ h _ (real.norm_of_nonneg hr.le).ge⟩ _,
  rintro b ⟨hb, x, hx', rfl⟩,
  refine not_lt.1 (λ hba, hx _),
  have ha := hb.trans hba,
  refine ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) _, _⟩,
  { rw ←div_eq_inv_mul,
    exact div_le_one_of_le hba.le ha.le },
  { rw [←mul_smul, mul_inv_cancel_left₀ ha.ne'] }
end

lemma one_le_gauge_of_not_mem (hs₁ : star_convex ℝ 0 s) (hs₂ : absorbs ℝ s {x}) (hx : x ∉ s) :
  1 ≤ gauge s x :=
le_gauge_of_not_mem hs₁ hs₂ $ by rwa one_smul

section linear_ordered_field
variables {α : Type*} [linear_ordered_field α] [mul_action_with_zero α ℝ] [ordered_smul α ℝ]

lemma gauge_smul_of_nonneg [mul_action_with_zero α E] [is_scalar_tower α ℝ (set E)] {s : set E}
  {a : α} (ha : 0 ≤ a) (x : E) :
  gauge s (a • x) = a • gauge s x :=
begin
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_smul, gauge_zero, zero_smul] },
  rw [gauge_def', gauge_def', ←real.Inf_smul_of_nonneg ha],
  congr' 1,
  ext r,
  simp_rw [set.mem_smul_set, set.mem_sep_iff],
  split,
  { rintro ⟨hr, hx⟩,
    simp_rw mem_Ioi at ⊢ hr,
    rw ←mem_smul_set_iff_inv_smul_mem₀ hr.ne' at hx,
    have := smul_pos (inv_pos.2 ha') hr,
    refine ⟨a⁻¹ • r, ⟨this, _⟩, smul_inv_smul₀ ha'.ne' _⟩,
    rwa [←mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc,
      mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha'.ne'), inv_inv] },
  { rintro ⟨r, ⟨hr, hx⟩, rfl⟩,
    rw mem_Ioi at ⊢ hr,
    rw ←mem_smul_set_iff_inv_smul_mem₀ hr.ne' at hx,
    have := smul_pos ha' hr,
    refine ⟨this, _⟩,
    rw [←mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc],
    exact smul_mem_smul_set hx }
end

lemma gauge_smul_left_of_nonneg [mul_action_with_zero α E] [smul_comm_class α ℝ ℝ]
  [is_scalar_tower α ℝ ℝ] [is_scalar_tower α ℝ E] {s : set E} {a : α} (ha : 0 ≤ a) :
  gauge (a • s) = a⁻¹ • gauge s :=
begin
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)] },
  ext,
  rw [gauge_def', pi.smul_apply, gauge_def', ←real.Inf_smul_of_nonneg (inv_nonneg.2 ha)],
  congr' 1,
  ext r,
  simp_rw [set.mem_smul_set, set.mem_sep_iff],
  split,
  { rintro ⟨hr, y, hy, h⟩,
    simp_rw [mem_Ioi] at ⊢ hr,
    refine ⟨a • r, ⟨smul_pos ha' hr, _⟩, inv_smul_smul₀ ha'.ne' _⟩,
    rwa [smul_inv₀, smul_assoc, ←h, inv_smul_smul₀ ha'.ne'] },
  { rintro ⟨r, ⟨hr, hx⟩, rfl⟩,
    rw mem_Ioi at ⊢ hr,
    have := smul_pos ha' hr,
    refine ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, _⟩,
    rw [smul_inv₀, smul_assoc, inv_inv] }
end

lemma gauge_smul_left [module α E] [smul_comm_class α ℝ ℝ] [is_scalar_tower α ℝ ℝ]
  [is_scalar_tower α ℝ E] {s : set E} (symmetric : ∀ x ∈ s, -x ∈ s) (a : α) :
  gauge (a • s) = |a|⁻¹ • gauge s :=
begin
  rw ←gauge_smul_left_of_nonneg (abs_nonneg a),
  obtain h | h := abs_choice a,
  { rw h },
  { rw [h, set.neg_smul_set, ←set.smul_set_neg],
    congr,
    ext y,
    refine ⟨symmetric _, λ hy, _⟩,
    rw ←neg_neg y,
    exact symmetric _ hy },
  { apply_instance }
end

end linear_ordered_field

section is_R_or_C
variables [is_R_or_C 𝕜] [module 𝕜 E] [is_scalar_tower ℝ 𝕜 E]

lemma gauge_norm_smul (hs : balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (‖r‖ • x) = gauge s (r • x) :=
begin
  rw @is_R_or_C.real_smul_eq_coe_smul 𝕜,
  obtain rfl | hr := eq_or_ne r 0,
  { simp only [norm_zero, is_R_or_C.of_real_zero] },
  unfold gauge,
  congr' with θ,
  refine and_congr_right (λ hθ, (hs.smul _).mem_smul_iff _),
  rw [is_R_or_C.norm_of_real, norm_norm],
end

/-- If `s` is balanced, then the Minkowski functional is ℂ-homogeneous. -/
lemma gauge_smul (hs : balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r • x) = ‖r‖ * gauge s x :=
by { rw [←smul_eq_mul, ←gauge_smul_of_nonneg (norm_nonneg r), gauge_norm_smul hs], apply_instance }

end is_R_or_C

section topological_space
variables [topological_space E] [has_continuous_smul ℝ E]

lemma interior_subset_gauge_lt_one (s : set E) : interior s ⊆ {x | gauge s x < 1} :=
begin
  intros x hx,
  let f : ℝ → E := λ t, t • x,
  have hf : continuous f,
  { continuity },
  let s' := f ⁻¹' (interior s),
  have hs' : is_open s' := hf.is_open_preimage _ is_open_interior,
  have one_mem : (1 : ℝ) ∈ s',
  { simpa only [s', f, set.mem_preimage, one_smul] },
  obtain ⟨ε, hε₀, hε⟩ := (metric.nhds_basis_closed_ball.1 _).1
    (is_open_iff_mem_nhds.1 hs' 1 one_mem),
  rw real.closed_ball_eq_Icc at hε,
  have hε₁ : 0 < 1 + ε := hε₀.trans (lt_one_add ε),
  have : (1 + ε)⁻¹ < 1,
  { rw inv_lt_one_iff,
    right,
    linarith },
  refine (gauge_le_of_mem (inv_nonneg.2 hε₁.le) _).trans_lt this,
  rw mem_inv_smul_set_iff₀ hε₁.ne',
  exact interior_subset
    (hε ⟨(sub_le_self _ hε₀.le).trans ((le_add_iff_nonneg_right _).2 hε₀.le), le_rfl⟩),
end

lemma gauge_lt_one_eq_self_of_open (hs₁ : convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : is_open s) :
  {x | gauge s x < 1} = s :=
begin
  refine (gauge_lt_one_subset_self hs₁ ‹_› $ absorbent_nhds_zero $ hs₂.mem_nhds hs₀).antisymm _,
  convert interior_subset_gauge_lt_one s,
  exact hs₂.interior_eq.symm,
end

lemma gauge_lt_one_of_mem_of_open (hs₁ : convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : is_open s)
  {x : E} (hx : x ∈ s) :
  gauge s x < 1 :=
by rwa ←gauge_lt_one_eq_self_of_open hs₁ hs₀ hs₂ at hx

lemma gauge_lt_of_mem_smul (x : E) (ε : ℝ) (hε : 0 < ε) (hs₀ : (0 : E) ∈ s)
  (hs₁ : convex ℝ s) (hs₂ : is_open s) (hx : x ∈ ε • s) :
  gauge s x < ε :=
begin
  have : ε⁻¹ • x ∈ s,
  { rwa ←mem_smul_set_iff_inv_smul_mem₀ hε.ne' },
  have h_gauge_lt := gauge_lt_one_of_mem_of_open hs₁ hs₀ hs₂ this,
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff hε, mul_one]
    at h_gauge_lt,
  apply_instance
end

end topological_space

lemma gauge_add_le (hs : convex ℝ s) (absorbs : absorbent ℝ s) (x y : E) :
  gauge s (x + y) ≤ gauge s x + gauge s y :=
begin
  refine le_of_forall_pos_lt_add (λ ε hε, _),
  obtain ⟨a, ha, ha', hx⟩ := exists_lt_of_gauge_lt absorbs
    (lt_add_of_pos_right (gauge s x) (half_pos hε)),
  obtain ⟨b, hb, hb', hy⟩ := exists_lt_of_gauge_lt absorbs
    (lt_add_of_pos_right (gauge s y) (half_pos hε)),
  rw mem_smul_set_iff_inv_smul_mem₀ ha.ne' at hx,
  rw mem_smul_set_iff_inv_smul_mem₀ hb.ne' at hy,
  suffices : gauge s (x + y) ≤ a + b,
  { linarith },
  have hab : 0 < a + b := add_pos ha hb,
  apply gauge_le_of_mem hab.le,
  have := convex_iff_div.1 hs hx hy ha.le hb.le hab,
  rwa [smul_smul, smul_smul, ←mul_div_right_comm, ←mul_div_right_comm, mul_inv_cancel ha.ne',
    mul_inv_cancel hb.ne', ←smul_add, one_div, ←mem_smul_set_iff_inv_smul_mem₀ hab.ne'] at this,
end

section is_R_or_C
variables [is_R_or_C 𝕜] [module 𝕜 E] [is_scalar_tower ℝ 𝕜 E]

/-- `gauge s` as a seminorm when `s` is  balanced, convex and absorbent. -/
@[simps] def gauge_seminorm (hs₀ : balanced 𝕜 s)  (hs₁ : convex ℝ s) (hs₂ : absorbent ℝ s) :
  seminorm 𝕜 E :=
seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)

variables {hs₀ : balanced 𝕜 s} {hs₁ : convex ℝ s} {hs₂ : absorbent ℝ s} [topological_space E]
  [has_continuous_smul ℝ E]

lemma gauge_seminorm_lt_one_of_open (hs : is_open s) {x : E} (hx : x ∈ s) :
  gauge_seminorm hs₀ hs₁ hs₂ x < 1 :=
gauge_lt_one_of_mem_of_open hs₁ hs₂.zero_mem hs hx

lemma gauge_seminorm_ball_one (hs : is_open s) :
  (gauge_seminorm hs₀ hs₁ hs₂).ball 0 1 = s :=
begin
  rw seminorm.ball_zero_eq,
  exact gauge_lt_one_eq_self_of_open hs₁ hs₂.zero_mem hs
end

end is_R_or_C

/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp] protected lemma seminorm.gauge_ball (p : seminorm ℝ E) : gauge (p.ball 0 1) = p :=
begin
  ext,
  obtain hp | hp := {r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1}.eq_empty_or_nonempty,
  { rw [gauge, hp, real.Inf_empty],
    by_contra,
    have hpx : 0 < p x := (map_nonneg _ _).lt_of_ne h,
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx,
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, _, smul_inv_smul₀ hpx₂.ne' _⟩,
    rw [p.mem_ball_zero, map_smul_eq_mul, real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂),
      inv_mul_lt_iff hpx₂, mul_one],
    exact lt_mul_of_one_lt_left hpx one_lt_two },
  refine is_glb.cInf_eq ⟨λ r, _, λ r hr, le_of_forall_pos_le_add $ λ ε hε, _⟩ hp,
  { rintro ⟨hr, y, hy, rfl⟩,
    rw p.mem_ball_zero at hy,
    rw [map_smul_eq_mul, real.norm_eq_abs, abs_of_pos hr],
    exact mul_le_of_le_one_right hr.le hy.le },
  { have hpε : 0 < p x + ε := by positivity,
    refine hr ⟨hpε, (p x + ε)⁻¹ • x, _, smul_inv_smul₀ hpε.ne' _⟩,
    rw [p.mem_ball_zero, map_smul_eq_mul, real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε),
      inv_mul_lt_iff hpε, mul_one],
    exact lt_add_of_pos_right _ hε }
end

lemma seminorm.gauge_seminorm_ball (p : seminorm ℝ E) :
  gauge_seminorm (p.balanced_ball_zero 1) (p.convex_ball 0 1)
    (p.absorbent_ball_zero zero_lt_one) = p := fun_like.coe_injective p.gauge_ball

end add_comm_group

section norm
variables [seminormed_add_comm_group E] [normed_space ℝ E] {s : set E} {r : ℝ} {x : E}

lemma gauge_unit_ball (x : E) : gauge (metric.ball (0 : E) 1) x = ‖x‖ :=
begin
  obtain rfl | hx := eq_or_ne x 0,
  { rw [norm_zero, gauge_zero] },
  refine (le_of_forall_pos_le_add $ λ ε hε, _).antisymm _,
  { have : 0 < ‖x‖ + ε := by positivity,
    refine gauge_le_of_mem this.le _,
    rw [smul_ball this.ne', smul_zero, real.norm_of_nonneg this.le, mul_one, mem_ball_zero_iff],
    exact lt_add_of_pos_right _ hε },
  refine le_gauge_of_not_mem balanced_ball_zero.star_convex
    (absorbent_ball_zero zero_lt_one).absorbs (λ h, _),
  obtain hx' | hx' := eq_or_ne (‖x‖) 0,
  { rw hx' at h,
    exact hx (zero_smul_set_subset _ h) },
  { rw [mem_smul_set_iff_inv_smul_mem₀ hx', mem_ball_zero_iff, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel hx'] at h,
    exact lt_irrefl _ h }
end

lemma gauge_ball (hr : 0 < r) (x : E) : gauge (metric.ball (0 : E) r) x = ‖x‖ / r :=
begin
  rw [←smul_unit_ball_of_pos hr, gauge_smul_left, pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul],
  simp_rw [mem_ball_zero_iff, norm_neg],
  exact λ _, id,
end

lemma mul_gauge_le_norm (hs : metric.ball (0 : E) r ⊆ s) : r * gauge s x ≤ ‖x‖ :=
begin
  obtain hr | hr := le_or_lt r 0,
  { exact (mul_nonpos_of_nonpos_of_nonneg hr $ gauge_nonneg _).trans (norm_nonneg _) },
  rw [mul_comm, ←le_div_iff hr, ←gauge_ball hr],
  exact gauge_mono (absorbent_ball_zero hr) hs x,
end

end norm
