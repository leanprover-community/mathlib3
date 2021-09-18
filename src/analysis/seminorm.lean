/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta
-/

import algebra.pointwise
import analysis.convex.basic
import analysis.normed_space.basic
import data.set.intervals

/-!
# Seminorms and Local Convexity

This file introduces the following notions, defined for a vector space
over a normed field:
* `absorbent`:
* `balanced`: The subset properties of being `absorbent` and `balanced`
* `seminorm`: A function to the reals that is positive-semidefinite,
  absolutely homogeneous, and subadditive.
* `gauge`: Aka Minkowksi functional. `gauge s x` is the smallest (actually, an infimum) `θ` such
  that `x ∈ θ • s`.

We prove related properties.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over ℝ or ℂ: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

Prove the properties of balanced and absorbent sets of a real vector space.

Generalize `gauge` to conditionally complete ordered fields, once we have them.

## Tags

absorbent, balanced, seminorm, Minkowski functional, gauge, locally convex, LCTVS
-/

/-!
### Subset Properties

Absorbent and balanced sets in a vector space over a
nondiscrete normed field.
-/

open normed_field set
open_locale pointwise topological_space

section stuff
variables {α : Type*} (β : Type*) [linear_ordered_field α] [ordered_add_comm_group β]
 [mul_action_with_zero α β] [ordered_smul α β]

@[simps] def order_iso.smul_left {a : α} (ha : 0 < a) : β ≃o β :=
{ to_fun := λ b, a • b,
  inv_fun := λ b, a⁻¹ • b,
  left_inv := inv_smul_smul' ha.ne',
  right_inv := smul_inv_smul' ha.ne',
  map_rel_iff' := λ b₁ b₂, smul_le_smul_iff_of_pos ha }

end stuff

section
variables {α : Type*} [linear_ordered_field α] [module α ℝ] [ordered_smul α ℝ]

lemma real.Inf_smul_of_nonneg {a : α} (ha : 0 ≤ a) (s : set ℝ) :
  Inf (a • s) = a • Inf s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [smul_set_empty, real.Inf_empty, smul_zero] },
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_smul_set hs, zero_smul],
    exact cInf_singleton 0 },
  by_cases bdd_below s,
  { rw [←order_iso.smul_left_apply _ ha', (order_iso.smul_left ℝ ha').map_cInf hs h],
  simp,
    sorry
    },
  sorry
end

lemma real.Sup_smul_of_nonneg {a : α} (ha : 0 ≤ a) (s : set ℝ) :
  Sup (a • s) = a • Sup s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [smul_set_empty, real.Sup_empty, smul_zero] },
  by_cases bdd_above s,
  { rw [←set.image_smul, eq_comm],
    exact map_cSup_of_continuous_at_of_monotone (continuous_id.const_smul _).continuous_at
      (smul_mono_right ha) hs h },
  { rw [real.Sup_of_not_bdd_above h, smul_zero],
    obtain rfl | ha' := ha.eq_or_lt,
    { rw zero_smul_set hs,
      exact cSup_singleton 0 },
    { sorry
     -- exact real.Inf_of_not_bdd_below (mt (bdd_above_smul_iff_of_pos ha).2 _)
    } }
end

end

section
variables
(𝕜 : Type*) [nondiscrete_normed_field 𝕜]
{E : Type*} [add_comm_group E] [module 𝕜 E]

/-- A set `A` absorbs another set `B` if `B` is contained in all scalings of
`A` by elements of sufficiently large norms. -/
def absorbs (A B : set E) := ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → B ⊆ a • A

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) := ∀ x, ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → x ∈ a • A

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a`
has norm less than one. -/
def balanced (A : set E) := ∀ a : 𝕜, ∥a∥ ≤ 1 → a • A ⊆ A

variables {𝕜} (a : 𝕜) {A : set E}

/-- A balanced set absorbs itself. -/
lemma balanced.absorbs_self (hA : balanced 𝕜 A) : absorbs 𝕜 A A :=
begin
  use [1, zero_lt_one],
  intros a ha x hx,
  rw mem_smul_set_iff_inv_smul_mem,
  { apply hA a⁻¹,
    { rw norm_inv, exact inv_le_one ha },
    { rw mem_smul_set, use [x, hx] }},
  { rw ←norm_pos_iff, calc 0 < 1 : zero_lt_one ... ≤ ∥a∥ : ha, }
end

lemma balanced.univ : balanced 𝕜 (univ : set E) :=
λ a ha, subset_univ _

lemma balanced.union {A₁ A₂ : set E} (hA₁ : balanced 𝕜 A₁) (hA₂ : balanced 𝕜 A₂) :
  balanced 𝕜 (A₁ ∪ A₂) :=
begin
  intros a ha t ht,
  rw [smul_set_union] at ht,
  exact ht.imp (λ x, hA₁ _ ha x) (λ x, hA₂ _ ha x),
end

lemma balanced.inter {A₁ A₂ : set E} (hA₁ : balanced 𝕜 A₁) (hA₂ : balanced 𝕜 A₂) :
  balanced 𝕜 (A₁ ∩ A₂) :=
begin
  rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩,
  exact ⟨hA₁ _ ha ⟨_, hx₁, rfl⟩, hA₂ _ ha ⟨_, hx₂, rfl⟩⟩,
end

lemma balanced.add {A₁ A₂ : set E} (hA₁ : balanced 𝕜 A₁) (hA₂ : balanced 𝕜 A₂) :
  balanced 𝕜 (A₁ + A₂) :=
begin
  rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩,
  rw smul_add,
  exact ⟨_, _, hA₁ _ ha ⟨_, hx, rfl⟩, hA₂ _ ha ⟨_, hy, rfl⟩, rfl⟩,
end

lemma balanced.smul (hA : balanced 𝕜 A) : balanced 𝕜 (a • A) :=
begin
  rintro b hb _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩,
  exact ⟨b • x, hA _ hb ⟨_, hx, rfl⟩, smul_comm _ _ _⟩,
end

lemma absorbent_iff_forall_absorbs_singleton :
  absorbent 𝕜 A ↔ ∀ x, absorbs 𝕜 A {x} :=
by simp [absorbs, absorbent]

/-!
Properties of balanced and absorbent sets in a topological vector space:
-/
variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
lemma absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : absorbent 𝕜 A :=
begin
  intro x,
  rcases mem_nhds_iff.mp hA with ⟨w, hw₁, hw₂, hw₃⟩,
  have hc : continuous (λ t : 𝕜, t • x), from continuous_id.smul continuous_const,
  rcases metric.is_open_iff.mp (hw₂.preimage hc) 0 (by rwa [mem_preimage, zero_smul])
    with ⟨r, hr₁, hr₂⟩,
  have hr₃, from inv_pos.mpr (half_pos hr₁),
  use [(r/2)⁻¹, hr₃],
  intros a ha₁,
  have ha₂ : 0 < ∥a∥ := hr₃.trans_le ha₁,
  have ha₃ : a ⁻¹ • x ∈ w,
  { apply hr₂,
    rw [metric.mem_ball, dist_zero_right, norm_inv],
    calc ∥a∥⁻¹ ≤ r/2 : (inv_le (half_pos hr₁) ha₂).mp ha₁
    ...       < r : half_lt_self hr₁ },
  rw [mem_smul_set_iff_inv_smul_mem (norm_pos_iff.mp ha₂)],
  exact hw₁ ha₃,
end

/-- The union of `{0}` with the interior of a balanced set
    is balanced. -/
lemma balanced_zero_union_interior (hA : balanced 𝕜 A) :
  balanced 𝕜 ({(0 : E)} ∪ interior A) :=
begin
  intros a ha, by_cases a = 0,
  { rw [h, zero_smul_set],
    exacts [subset_union_left _ _, ⟨0, or.inl rfl⟩] },
  { rw [←image_smul, image_union],
    apply union_subset_union,
    { rw [image_singleton, smul_zero] },
    { calc a • interior A ⊆ interior (a • A) : (is_open_map_smul' h).image_interior_subset A
                      ... ⊆ interior A       : interior_mono (hA _ ha) } }
end

/-- The interior of a balanced set is balanced if it contains the origin. -/
lemma balanced.interior (hA : balanced 𝕜 A) (h : (0 : E) ∈ interior A) :
  balanced 𝕜 (interior A) :=
begin
  rw ←singleton_subset_iff at h,
  rw [←union_eq_self_of_subset_left h],
  exact balanced_zero_union_interior hA,
end

/-- The closure of a balanced set is balanced. -/
lemma balanced.closure (hA : balanced 𝕜 A) : balanced 𝕜 (closure A) :=
assume a ha,
calc _ ⊆ closure (a • A) : image_closure_subset_closure_image (continuous_id.const_smul _)
...    ⊆ _ : closure_mono (hA _ ha)

end

/-!
### Seminorms
-/

/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*)
  [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] :=
(to_fun    : E → ℝ)
(smul'     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace seminorm
variables
{𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [add_comm_group E] [module 𝕜 E]

instance : inhabited (seminorm 𝕜 E) :=
⟨{ to_fun     := λ _, 0,
   smul'     := λ _ _, (mul_zero _).symm,
   triangle' := λ x y, by rw add_zero }⟩

instance : has_coe_to_fun (seminorm 𝕜 E) := ⟨_, λ p, p.to_fun⟩

variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected lemma smul : p (c • x) = ∥c∥ * p x := p.smul' _ _
protected lemma triangle : p (x + y) ≤ p x + p y := p.triangle' _ _

@[simp]
protected lemma zero : p 0 = 0 :=
calc p 0 = p ((0 : 𝕜) • 0) : by rw zero_smul
...      = 0 : by rw [p.smul, norm_zero, zero_mul]

@[simp]
protected lemma neg : p (-x) = p x :=
calc p (-x) = p ((-1 : 𝕜) • x) : by rw neg_one_smul
...         = p x : by rw [p.smul, norm_neg, norm_one, one_mul]

lemma nonneg : 0 ≤ p x :=
have h: 0 ≤ 2 * p x, from
calc 0 = p (x + (- x)) : by rw [add_neg_self, p.zero]
...    ≤ p x + p (-x)  : p.triangle _ _
...    = 2 * p x : by rw [p.neg, two_mul],
nonneg_of_mul_nonneg_left h zero_lt_two

lemma sub_rev : p (x - y) = p (y - x) :=
by rw [←neg_sub, p.neg]

/-- The ball of radius `r` at `x` with respect to seminorm `p`
    is the set of elements `y` with `p (y - x) < `r`. -/
def ball (p : seminorm 𝕜 E) (x : E) (r : ℝ) := { y : E | p (y - x) < r }

lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
iff.rfl

lemma mem_ball_zero : y ∈ ball p 0 r ↔ p y < r :=
by rw [mem_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
set.ext $ λ x,by { rw mem_ball_zero, exact iff.rfl }

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero : balanced 𝕜 (ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero, ←hx, p.smul],
  calc _ ≤ p y : mul_le_of_le_one_left (p.nonneg _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

-- TODO: convexity and absorbent/balanced sets in vector spaces over ℝ

end seminorm

section gauge
noncomputable theory
variables {E : Type*} [add_comm_group E] [module ℝ E]

/--
Given a subset `s` of a real vector space, we have a functional (sometimes called the Minkowski
functional) which sends `x : E` to `Inf {y ∈ set.Ioi 0 | x ∈ y • s}`, essentially the smallest
`y` such that `x` is in `s` expanded by `y`.
-/
def gauge (s : set E) (x : E) : ℝ :=
Inf {y : ℝ | 0 < y ∧ x ∈ y • s}

variables {s : set E} {x : E}

lemma gauge_def : gauge s x = Inf {y ∈ set.Ioi 0 | x ∈ y • s} := rfl

/-- An alternate definition of the gauge which can be useful in certain situations. -/
lemma gauge_def' : gauge s x = Inf {y ∈ set.Ioi 0 | y⁻¹ • x ∈ s} :=
begin
  rw gauge_def,
  congr' 1,
  ext y,
  apply and_congr_right,
  intro hy,
  apply mem_smul_set_iff_inv_smul_mem (ne_of_gt hy),
end

private lemma gauge_set_bdd_below :
  bdd_below {y : ℝ | 0 < y ∧ x ∈ y • s} :=
⟨0, λ y hy, hy.1.le⟩

lemma gauge_le_of_mem {θ : ℝ} (hθ : 0 < θ) {x : E} (hx : x ∈ θ • s) :
  gauge s x ≤ θ :=
cInf_le gauge_set_bdd_below ⟨hθ, hx⟩

/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
lemma gauge_set_nonempty_of_absorbent (absorbs : absorbent ℝ s) :
  {y : ℝ | 0 < y ∧ x ∈ y • s}.nonempty :=
let ⟨θ, hθ₁, hθ₂⟩ := absorbs x in ⟨θ, hθ₁, hθ₂ θ (real.norm_of_nonneg hθ₁.le).ge⟩

lemma exists_lt_of_gauge_lt (absorbs : absorbent ℝ s) {x : E} {a : ℝ} (h : gauge s x < a) :
  ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s :=
begin
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_cInf_lt (gauge_set_nonempty_of_absorbent absorbs) h,
  exact ⟨b, hb, hba, hx⟩,
end

/-- The gauge evaluated at `0` is always zero (mathematically this requires that `0` is in the
subset `s`, but as the real infimum of the empty set in Lean is defined to be `0`, it holds
unconditionally). -/
@[simp] lemma gauge_zero : gauge s 0 = 0 :=
begin
  rw gauge_def',
  by_cases (0 : E) ∈ s,
  { simp only [smul_zero, sep_true, h, cInf_Ioi] },
  { simp only [smul_zero, sep_false, h, real.Inf_empty] }
end

/-- The gauge is always nonnegative. -/
lemma gauge_nonneg (x : E) :
  0 ≤ gauge s x :=
real.Inf_nonneg _ (λ x hx, hx.1.le)

lemma gauge_le_one_eq' (hs : convex s) (zero_mem : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x ≤ 1} = ⋂ (θ : ℝ) (H : 1 < θ), θ • s :=
begin
  ext,
  simp_rw [set.mem_Inter, set.mem_set_of_eq],
  split,
  { intros h θ hθ,
    have hθ' := zero_lt_one.trans hθ,
    rw mem_smul_set_iff_inv_smul_mem hθ'.ne',
    obtain ⟨δ, δ_pos, hδθ, hδ⟩ := exists_lt_of_gauge_lt absorbs (h.trans_lt hθ),
    suffices : (θ⁻¹ * δ) • δ⁻¹ • x ∈ s,
    { rwa [smul_smul, mul_inv_cancel_right' δ_pos.ne'] at this },
    rw mem_smul_set_iff_inv_smul_mem δ_pos.ne' at hδ,
    refine hs.smul_mem_of_zero_mem zero_mem hδ
      ⟨mul_nonneg (inv_nonneg.2 hθ'.le) δ_pos.le, _⟩,
    rw [inv_mul_le_iff hθ', mul_one],
    exact hδθ.le },
  { refine λ h, le_of_forall_pos_lt_add (λ ε hε, _),
    have hε' := (lt_add_iff_pos_right 1).2 (half_pos hε),
    exact (gauge_le_of_mem (zero_lt_one.trans hε') $ h _ hε').trans_lt
      (add_lt_add_left (half_lt_self hε) _) }
end

lemma gauge_le_one_eq (hs : convex s) (zero_mem : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x ≤ 1} = ⋂ (θ ∈ set.Ioi (1 : ℝ)), θ • s :=
gauge_le_one_eq' hs zero_mem absorbs

lemma gauge_lt_one_eq' (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} = ⋃ (θ : ℝ) (H : 0 < θ) (H : θ < 1), θ • s :=
begin
  ext,
  simp_rw [set.mem_set_of_eq, set.mem_Union],
  split,
  { intro h,
    obtain ⟨θ, hθ₀, hθ₁, hx⟩ := exists_lt_of_gauge_lt absorbs h,
    exact ⟨θ, hθ₀, hθ₁, hx⟩ },
  { exact λ ⟨θ, hθ₀, hθ₁, hx⟩, (gauge_le_of_mem hθ₀ hx).trans_lt hθ₁ }
end

lemma gauge_lt_one_eq (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} = ⋃ (θ ∈ set.Ioo 0 (1 : ℝ)), θ • s :=
begin
  ext,
  simp_rw [set.mem_set_of_eq, set.mem_Union],
  split,
  { intro h,
    obtain ⟨θ, hθ₀, hθ₁, hx⟩ := exists_lt_of_gauge_lt absorbs h,
    exact ⟨θ, ⟨hθ₀, hθ₁⟩, hx⟩ },
  { exact λ ⟨θ, ⟨hθ₀, hθ₁⟩, hx⟩, (gauge_le_of_mem hθ₀ hx).trans_lt hθ₁ }
end

lemma gauge_lt_one_subset_self (hs : convex s) (zero_mem : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} ⊆ s :=
begin
  rw gauge_lt_one_eq absorbs,
  apply set.bUnion_subset,
  rintro θ hθ _ ⟨y, hy, rfl⟩,
  exact hs.smul_mem_of_zero_mem zero_mem hy (Ioo_subset_Icc_self hθ),
end

lemma gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
gauge_le_of_mem zero_lt_one (by rwa one_smul)

lemma self_subset_gauge_le_one : s ⊆ {x | gauge s x ≤ 1} :=
λ x, gauge_le_one_of_mem

lemma convex.gauge_le_one (hs : convex s) (zero_mem : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  convex {x | gauge s x ≤ 1} :=
begin
  rw gauge_le_one_eq hs zero_mem absorbs,
  refine convex_Inter (λ i, convex_Inter (λ (hi : _ < _), convex.smul _ hs)),
end

lemma interior_subset_gauge_lt_one [topological_space E] [has_continuous_smul ℝ E] (s : set E) :
  interior s ⊆ {x | gauge s x < 1} :=
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
  rw real.closed_ball_eq at hε,
  have hε₁ : 0 < 1 + ε := hε₀.trans (lt_one_add ε),
  have : (1 + ε)⁻¹ < 1,
  { rw inv_lt_one_iff,
    right,
    linarith },
  refine (gauge_le_of_mem (inv_pos.2 hε₁) _).trans_lt this,
  rw mem_inv_smul_set_iff hε₁.ne',
  exact interior_subset
    (hε ⟨(sub_le_self _ hε₀.le).trans ((le_add_iff_nonneg_right _).2 hε₀.le), le_rfl⟩),
end

lemma gauge_lt_one_eq_self_of_open [topological_space E] [has_continuous_smul ℝ E] {s : set E}
  (hs : convex s) (zero_mem : (0 : E) ∈ s) (hs₂ : is_open s) :
  {x | gauge s x < 1} = s :=
begin
  apply (gauge_lt_one_subset_self hs ‹_› $ absorbent_nhds_zero $ hs₂.mem_nhds zero_mem).antisymm,
  convert interior_subset_gauge_lt_one s,
  exact hs₂.interior_eq.symm,
end

lemma gauge_lt_one_of_mem_of_open [topological_space E] [has_continuous_smul ℝ E] {s : set E}
  (hs : convex s) (zero_mem : (0 : E) ∈ s) (hs₂ : is_open s) (x : E) (hx : x ∈ s) :
  gauge s x < 1 :=
by rwa ←gauge_lt_one_eq_self_of_open hs zero_mem hs₂ at hx

lemma one_le_gauge_of_not_mem [topological_space E] [has_continuous_smul ℝ E] {s : set E}
  (hs : convex s) (zero_mem : (0 : E) ∈ s) (hs₂ : is_open s) {x : E} (hx : x ∉ s) :
  1 ≤ gauge s x :=
begin
  rw ←gauge_lt_one_eq_self_of_open hs zero_mem hs₂ at hx,
  exact le_of_not_lt hx
end

lemma gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) :
  gauge s (-x) = gauge s x :=
begin
  have : ∀ x, -x ∈ s ↔ x ∈ s := λ x, ⟨λ h, by simpa using symmetric _ h, symmetric x⟩,
  rw [gauge_def', gauge_def'],
  simp_rw [smul_neg, this],
end.

variables {α : Type*} [linear_ordered_field α] [topological_space α] [module α ℝ]
  [has_continuous_smul α ℝ] [ordered_smul α ℝ]

lemma gauge_smul [mul_action_with_zero α E] [is_scalar_tower α ℝ (set E)] {s : set E} {θ : α}
  (hθ : 0 ≤ θ)
  (x : E) :
  gauge s (θ • x) = θ • gauge s x :=
begin
  obtain rfl | hθ' := hθ.eq_or_lt,
  { rw [zero_smul, gauge_zero, zero_smul] },
  rw [gauge_def', gauge_def', ←real.Inf_smul_of_nonneg hθ],
  congr' 1,
  ext β,
  simp_rw [set.mem_smul_set, set.mem_sep_eq],
  split,
  { rintro ⟨hβ, hx⟩,
    simp_rw [mem_Ioi] at ⊢ hβ,
    have := smul_pos (inv_pos.2 hθ') hβ,
    refine ⟨θ⁻¹ • β, ⟨this, _⟩, smul_inv_smul' hθ'.ne' _⟩,
    rw ←mem_smul_set_iff_inv_smul_mem at ⊢ hx,
    rwa [smul_assoc, mem_smul_set_iff_inv_smul_mem (inv_ne_zero hθ'.ne'), inv_inv'],
    { exact this.ne' },
    { exact hβ.ne' } },
  { rintro ⟨β, ⟨hβ, hx⟩, rfl⟩,
    rw mem_Ioi at ⊢ hβ,
    have := smul_pos hθ' hβ,
    refine ⟨this, _⟩,
    rw ←mem_smul_set_iff_inv_smul_mem at ⊢ hx,
    rw smul_assoc,
    exact smul_mem_smul_set hx,
    { exact this.ne' },
    { exact hβ.ne'} }
end

lemma gauge_homogeneous [module α E] [is_scalar_tower α ℝ (set E)] {s : set E}
  (symmetric : ∀ x ∈ s, -x ∈ s) (θ : α) (x : E) :
  gauge s (θ • x) = abs θ • gauge s x :=
begin
  rw ←gauge_smul (abs_nonneg θ),
  obtain h | h := abs_choice θ,
  { rw h },
  { rw [h, neg_smul, gauge_neg symmetric] },
  { apply_instance }
end

lemma gauge_subadditive (hs : convex s) (absorbs : absorbent ℝ s) (x y : E) :
  gauge s (x + y) ≤ gauge s x + gauge s y :=
begin
  refine le_of_forall_pos_lt_add (λ ε hε, _),
  obtain ⟨a, ha, ha', hx⟩ := exists_lt_of_gauge_lt absorbs
    (lt_add_of_pos_right (gauge s x) (half_pos hε)),
  obtain ⟨b, hb, hb', hy⟩ := exists_lt_of_gauge_lt absorbs
    (lt_add_of_pos_right (gauge s y) (half_pos hε)),
  rw mem_smul_set_iff_inv_smul_mem ha.ne' at hx,
  rw mem_smul_set_iff_inv_smul_mem hb.ne' at hy,
  suffices : gauge s (x + y) ≤ a + b,
  { linarith },
  have hab : 0 < a + b := add_pos ha hb,
  apply gauge_le_of_mem hab,
  have := convex_iff_div.1 hs hx hy ha.le hb.le hab,
  rwa [smul_smul, smul_smul, mul_comm_div', mul_comm_div', ←mul_div_assoc, ←mul_div_assoc,
    mul_inv_cancel ha.ne', mul_inv_cancel hb.ne', ←smul_add, one_div,
    ←mem_smul_set_iff_inv_smul_mem hab.ne'] at this,
end

/-- If `s` is symmetric, convex and absorbent, its `gauge` is a seminorm. -/
def gauge_seminorm (symmetric : ∀ x ∈ s, -x ∈ s) (hs : convex s) (hs' : absorbent ℝ s) :
  seminorm ℝ E :=
{ to_fun := gauge s,
  smul' := λ θ x, by rw [gauge_homogeneous symmetric, real.norm_eq_abs, smul_eq_mul];
    apply_instance,
  triangle' := gauge_subadditive hs hs' }

end gauge

-- TODO: topology induced by family of seminorms, local convexity.
