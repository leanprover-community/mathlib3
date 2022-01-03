/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
import analysis.convex.function
import analysis.normed_space.ordered
import data.real.pointwise

/-!
# Seminorms and Local Convexity

This file defines absorbent sets, balanced sets, seminorms and the Minkowski functional.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a vector space over a normed field:
* `absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.
* `seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `gauge`: Aka Minkowksi functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gauge_seminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over ℝ or ℂ: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

Prove the properties of balanced and absorbent sets of a real vector space.

## Tags

absorbent, balanced, seminorm, Minkowski functional, gauge, locally convex, LCTVS
-/

/-!
### Set Properties

Absorbent and balanced sets in a vector space over a normed field.
-/

open normed_field set
open_locale pointwise topological_space

variables {𝕜 E : Type*}

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E]

/-- A set `A` absorbs another set `B` if `B` is contained in all scalings of
`A` by elements of sufficiently large norms. -/
def absorbs (A B : set E) := ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → B ⊆ a • A

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) := ∀ x, ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → x ∈ a • A

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a`
has norm less than or equal to one. -/
def balanced (A : set E) := ∀ a : 𝕜, ∥a∥ ≤ 1 → a • A ⊆ A

variables {𝕜} {A B : set E}

lemma balanced.univ : balanced 𝕜 (univ : set E) := λ a ha, subset_univ _

lemma balanced.union (hA : balanced 𝕜 A) (hB : balanced 𝕜 B) : balanced 𝕜 (A ∪ B) :=
begin
  intros a ha t ht,
  rw [smul_set_union] at ht,
  exact ht.imp (λ x, hA _ ha x) (λ x, hB _ ha x),
end

end has_scalar

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] {A B : set E}

lemma balanced.inter (hA : balanced 𝕜 A) (hB : balanced 𝕜 B) : balanced 𝕜 (A ∩ B) :=
begin
  rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩,
  exact ⟨hA _ ha ⟨_, hx₁, rfl⟩, hB _ ha ⟨_, hx₂, rfl⟩⟩,
end

lemma balanced.add (hA₁ : balanced 𝕜 A) (hA₂ : balanced 𝕜 B) : balanced 𝕜 (A + B) :=
begin
  rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩,
  rw smul_add,
  exact ⟨_, _, hA₁ _ ha ⟨_, hx, rfl⟩, hA₂ _ ha ⟨_, hy, rfl⟩, rfl⟩,
end

lemma absorbent.subset (hA : absorbent 𝕜 A) (hAB : A ⊆ B) : absorbent 𝕜 B :=
begin
  rintro x,
  obtain ⟨r, hr, hx⟩ := hA x,
  exact ⟨r, hr, λ a ha, set.smul_set_mono hAB $ hx a ha⟩,
end

lemma absorbent_iff_forall_absorbs_singleton : absorbent 𝕜 A ↔ ∀ x, absorbs 𝕜 A {x} :=
by simp_rw [absorbs, absorbent, singleton_subset_iff]

lemma absorbent_iff_nonneg_lt : absorbent 𝕜 A ↔ ∀ x, ∃ r, 0 ≤ r ∧ ∀ a : 𝕜, r < ∥a∥ → x ∈ a • A :=
begin
  split,
  { rintro hA x,
    obtain ⟨r, hr, hx⟩ := hA x,
    exact ⟨r, hr.le, λ a ha, hx a ha.le⟩ },
  { rintro hA x,
    obtain ⟨r, hr, hx⟩ := hA x,
    exact ⟨r + 1, add_pos_of_nonneg_of_pos hr zero_lt_one,
      λ a ha, hx a ((lt_add_of_pos_right r zero_lt_one).trans_le ha)⟩ }
end

end add_comm_group
end semi_normed_ring

section normed_comm_ring
variables [normed_comm_ring 𝕜] [add_comm_monoid E] [module 𝕜 E] {A B : set E} (a : 𝕜)

lemma balanced.smul (hA : balanced 𝕜 A) : balanced 𝕜 (a • A) :=
begin
  rintro b hb _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩,
  exact ⟨b • x, hA _ hb ⟨_, hx, rfl⟩, smul_comm _ _ _⟩,
end

end normed_comm_ring

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] {A B : set E} {a : 𝕜}

/-- A balanced set absorbs itself. -/
lemma balanced.absorbs_self (hA : balanced 𝕜 A) : absorbs 𝕜 A A :=
begin
  use [1, zero_lt_one],
  intros a ha x hx,
  rw mem_smul_set_iff_inv_smul_mem₀,
  { apply hA a⁻¹,
    { rw norm_inv, exact inv_le_one ha },
    { rw mem_smul_set, use [x, hx] }},
  { rw ←norm_pos_iff, calc 0 < 1 : zero_lt_one ... ≤ ∥a∥ : ha, }
end

lemma balanced.subset_smul (hA : balanced 𝕜 A) (ha : 1 ≤ ∥a∥) : A ⊆ a • A :=
begin
  refine (subset_set_smul_iff₀ _).2 (hA (a⁻¹) _),
  { rintro rfl,
    rw norm_zero at ha,
    exact zero_lt_one.not_le ha },
  { rw norm_inv,
    exact inv_le_one ha }
end

lemma balanced.smul_eq (hA : balanced 𝕜 A) (ha : ∥a∥ = 1) : a • A = A :=
(hA _ ha.le).antisymm $ hA.subset_smul ha.ge

/-! #### Topological vector space -/

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
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp ha₂)],
  refine hw₁ (hr₂ _),
  rw [metric.mem_ball, dist_zero_right, norm_inv],
  calc ∥a∥⁻¹ ≤ r/2 : (inv_le (half_pos hr₁) ha₂).mp ha₁
  ...       < r : half_lt_self hr₁,
end

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
lemma balanced_zero_union_interior (hA : balanced 𝕜 A) : balanced 𝕜 ({(0 : E)} ∪ interior A) :=
begin
  intros a ha, by_cases a = 0,
  { rw [h, zero_smul_set],
    exacts [subset_union_left _ _, ⟨0, or.inl rfl⟩] },
  { rw [←image_smul, image_union],
    apply union_subset_union,
    { rw [image_singleton, smul_zero] },
    { calc a • interior A ⊆ interior (a • A) : (is_open_map_smul₀ h).image_interior_subset A
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

end normed_field

/-!
### Seminorms
-/

/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*) [semi_normed_ring 𝕜] [add_monoid E] [has_scalar 𝕜 E] :=
(to_fun    : E → ℝ)
(smul'     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace seminorm
section semi_normed_ring
variables [semi_normed_ring 𝕜]

section add_monoid
variables [add_monoid E]

section has_scalar
variables [has_scalar 𝕜 E]

instance : inhabited (seminorm 𝕜 E) :=
⟨{ to_fun    := λ _, 0,
   smul'     := λ _ _, (mul_zero _).symm,
   triangle' := λ x y, by rw add_zero }⟩

instance : has_coe_to_fun (seminorm 𝕜 E) (λ _, E → ℝ) := ⟨λ p, p.to_fun⟩

@[ext] lemma ext {p q : seminorm 𝕜 E} (h : (p : E → ℝ) = q) : p = q :=
begin
  cases p,
  cases q,
  have : p_to_fun = q_to_fun := h,
  simp_rw this,
end

variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected lemma smul : p (c • x) = ∥c∥ * p x := p.smul' _ _
protected lemma triangle : p (x + y) ≤ p x + p y := p.triangle' _ _

end has_scalar

section smul_with_zero
variables [smul_with_zero 𝕜 E] (p : seminorm 𝕜 E)

@[simp]
protected lemma zero : p 0 = 0 :=
calc p 0 = p ((0 : 𝕜) • 0) : by rw zero_smul
...      = 0 : by rw [p.smul, norm_zero, zero_mul]

end smul_with_zero
end add_monoid

section norm_one_class
variables [norm_one_class 𝕜] [add_comm_group E] [module 𝕜 E] (p : seminorm 𝕜 E) (x y : E) (r : ℝ)

@[simp]
protected lemma neg : p (-x) = p x :=
calc p (-x) = p ((-1 : 𝕜) • x) : by rw neg_one_smul
...         = p x : by rw [p.smul, norm_neg, norm_one, one_mul]

protected lemma sub_le : p (x - y) ≤ p x + p y :=
calc
  p (x - y)
      = p (x + -y) : by rw sub_eq_add_neg
  ... ≤ p x + p (-y) : p.triangle x (-y)
  ... = p x + p y : by rw p.neg

lemma nonneg : 0 ≤ p x :=
have h: 0 ≤ 2 * p x, from
calc 0 = p (x + (- x)) : by rw [add_neg_self, p.zero]
...    ≤ p x + p (-x)  : p.triangle _ _
...    = 2 * p x : by rw [p.neg, two_mul],
nonneg_of_mul_nonneg_left h zero_lt_two

lemma sub_rev : p (x - y) = p (y - x) := by rw [←neg_sub, p.neg]

end norm_one_class

/-! ### Seminorm ball -/

section add_comm_group
variables [add_comm_group E]

section has_scalar
variables [has_scalar 𝕜 E] (p : seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def ball (x : E) (r : ℝ) := { y : E | p (y - x) < r }

variables {x y : E} {r : ℝ}

lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r := iff.rfl

lemma mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } := set.ext $ λ x, p.mem_ball_zero

end has_scalar

section module
variables [norm_one_class 𝕜] [module 𝕜 E] (p : seminorm 𝕜 E)

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero (r : ℝ): balanced 𝕜 (ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero, ←hx, p.smul],
  calc _ ≤ p y : mul_le_of_le_one_left (p.nonneg _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

end module
end add_comm_group
end semi_normed_ring

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] (p : seminorm 𝕜 E) {A B : set E}
  {a : 𝕜} {r : ℝ} {x : E}

/-- Seminorm-balls at the origin are absorbent. -/
lemma absorbent_ball_zero (hr : 0 < r) : absorbent 𝕜 (ball p (0 : E) r) :=
begin
  rw absorbent_iff_nonneg_lt,
  rintro x,
  have hxr : 0 ≤ p x/r := div_nonneg (p.nonneg _) hr.le,
  refine ⟨p x/r, hxr, λ a ha, _⟩,
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha,
  refine ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩,
  rwa [mem_ball_zero, p.smul, norm_inv, inv_mul_lt_iff ha₀, ←div_lt_iff hr],
end

/-- Seminorm-balls containing the origin are absorbent. -/
lemma absorbent_ball (hpr : p x < r) : absorbent 𝕜 (ball p x r) :=
begin
  refine (p.absorbent_ball_zero $ sub_pos.2 hpr).subset (λ y hy, _),
  rw p.mem_ball_zero at hy,
  exact p.mem_ball.2 ((p.sub_le _ _).trans_lt $ add_lt_of_lt_sub_right hy),
end

lemma symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
balanced_ball_zero p r (-1) (by rw [norm_neg, norm_one]) ⟨x, hx, by rw [neg_smul, one_smul]⟩

end normed_field

section normed_linear_ordered_field
variables [normed_linear_ordered_field 𝕜] [add_comm_group E] [semi_normed_space ℝ 𝕜] [module 𝕜 E]

section has_scalar
variables [has_scalar ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected lemma convex_on : convex_on ℝ univ p :=
begin
  refine ⟨convex_univ, λ x y _ _ a b ha hb hab, _⟩,
  calc p (a • x + b • y) ≤ p (a • x) + p (b • y) : p.triangle _ _
    ... = ∥a • (1 : 𝕜)∥ * p x + ∥b • (1 : 𝕜)∥ * p y
        : by rw [←p.smul, ←p.smul, smul_one_smul, smul_one_smul]
    ... = a * p x + b * p y
        : by rw [norm_smul, norm_smul, norm_one, mul_one, mul_one, real.norm_of_nonneg ha,
            real.norm_of_nonneg hb],
end

end has_scalar

section module
variables [module ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
lemma convex_ball : convex ℝ (ball p x r) :=
begin
  convert (p.convex_on.translate_left (-x)).convex_lt r,
  ext y,
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg],
  refl,
end

end module
end normed_linear_ordered_field

-- TODO: convexity and absorbent/balanced sets in vector spaces over ℝ

end seminorm

section gauge
noncomputable theory
variables [add_comm_group E] [module ℝ E]

/--The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : set E) (x : E) : ℝ := Inf {r : ℝ | 0 < r ∧ x ∈ r • s}

variables {s : set E} {x : E}

lemma gauge_def : gauge s x = Inf {r ∈ set.Ioi 0 | x ∈ r • s} := rfl

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
lemma gauge_def' : gauge s x = Inf {r ∈ set.Ioi 0 | r⁻¹ • x ∈ s} :=
begin
  unfold gauge,
  congr' 1,
  ext r,
  exact and_congr_right (λ hr, mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _),
end

private lemma gauge_set_bdd_below : bdd_below {r : ℝ | 0 < r ∧ x ∈ r • s} := ⟨0, λ r hr, hr.1.le⟩

/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
lemma absorbent.gauge_set_nonempty (absorbs : absorbent ℝ s) :
  {r : ℝ | 0 < r ∧ x ∈ r • s}.nonempty :=
let ⟨r, hr₁, hr₂⟩ := absorbs x in ⟨r, hr₁, hr₂ r (real.norm_of_nonneg hr₁.le).ge⟩

lemma exists_lt_of_gauge_lt (absorbs : absorbent ℝ s) {x : E} {a : ℝ} (h : gauge s x < a) :
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

/-- The gauge is always nonnegative. -/
lemma gauge_nonneg (x : E) : 0 ≤ gauge s x := real.Inf_nonneg _ $ λ x hx, hx.1.le

lemma gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) : gauge s (-x) = gauge s x :=
begin
  have : ∀ x, -x ∈ s ↔ x ∈ s := λ x, ⟨λ h, by simpa using symmetric _ h, symmetric x⟩,
  rw [gauge_def', gauge_def'],
  simp_rw [smul_neg, this],
end

lemma gauge_le_of_mem {r : ℝ} (hr : 0 ≤ r) {x : E} (hx : x ∈ r • s) : gauge s x ≤ r :=
begin
  obtain rfl | hr' := hr.eq_or_lt,
  { rw [mem_singleton_iff.1 (zero_smul_subset _ hx), gauge_zero] },
  { exact cInf_le gauge_set_bdd_below ⟨hr', hx⟩ }
end

lemma gauge_le_one_eq' (hs : convex ℝ s) (zero_mem : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x ≤ 1} = ⋂ (r : ℝ) (H : 1 < r), r • s :=
begin
  ext,
  simp_rw [set.mem_Inter, set.mem_set_of_eq],
  split,
  { intros h r hr,
    have hr' := zero_lt_one.trans hr,
    rw mem_smul_set_iff_inv_smul_mem₀ hr'.ne',
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt absorbs (h.trans_lt hr),
    suffices : (r⁻¹ * δ) • δ⁻¹ • x ∈ s,
    { rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this },
    rw mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne' at hδ,
    refine hs.smul_mem_of_zero_mem zero_mem hδ
      ⟨mul_nonneg (inv_nonneg.2 hr'.le) δ_pos.le, _⟩,
    rw [inv_mul_le_iff hr', mul_one],
    exact hδr.le },
  { refine λ h, le_of_forall_pos_lt_add (λ ε hε, _),
    have hε' := (lt_add_iff_pos_right 1).2 (half_pos hε),
    exact (gauge_le_of_mem (zero_le_one.trans hε'.le) $ h _ hε').trans_lt
      (add_lt_add_left (half_lt_self hε) _) }
end

lemma gauge_le_one_eq (hs : convex ℝ s) (zero_mem : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x ≤ 1} = ⋂ (r ∈ set.Ioi (1 : ℝ)), r • s :=
gauge_le_one_eq' hs zero_mem absorbs

lemma gauge_lt_one_eq' (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} = ⋃ (r : ℝ) (H : 0 < r) (H : r < 1), r • s :=
begin
  ext,
  simp_rw [set.mem_set_of_eq, set.mem_Union],
  split,
  { intro h,
    obtain ⟨r, hr₀, hr₁, hx⟩ := exists_lt_of_gauge_lt absorbs h,
    exact ⟨r, hr₀, hr₁, hx⟩ },
  { exact λ ⟨r, hr₀, hr₁, hx⟩, (gauge_le_of_mem hr₀.le hx).trans_lt hr₁ }
end

lemma gauge_lt_one_eq (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} = ⋃ (r ∈ set.Ioo 0 (1 : ℝ)), r • s :=
begin
  ext,
  simp_rw [set.mem_set_of_eq, set.mem_Union],
  split,
  { intro h,
    obtain ⟨r, hr₀, hr₁, hx⟩ := exists_lt_of_gauge_lt absorbs h,
    exact ⟨r, ⟨hr₀, hr₁⟩, hx⟩ },
  { exact λ ⟨r, ⟨hr₀, hr₁⟩, hx⟩, (gauge_le_of_mem hr₀.le hx).trans_lt hr₁ }
end

lemma gauge_lt_one_subset_self (hs : convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} ⊆ s :=
begin
  rw gauge_lt_one_eq absorbs,
  apply set.bUnion_subset,
  rintro r hr _ ⟨y, hy, rfl⟩,
  exact hs.smul_mem_of_zero_mem h₀ hy (Ioo_subset_Icc_self hr),
end

lemma gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
gauge_le_of_mem zero_le_one $ by rwa one_smul

lemma self_subset_gauge_le_one : s ⊆ {x | gauge s x ≤ 1} := λ x, gauge_le_one_of_mem

lemma convex.gauge_le_one (hs : convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  convex ℝ {x | gauge s x ≤ 1} :=
begin
  rw gauge_le_one_eq hs h₀ absorbs,
  exact convex_Inter (λ i, convex_Inter (λ (hi : _ < _), hs.smul _)),
end

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

lemma gauge_lt_one_eq_self_of_open {s : set E} (hs : convex ℝ s) (zero_mem : (0 : E) ∈ s)
  (hs₂ : is_open s) :
  {x | gauge s x < 1} = s :=
begin
  apply (gauge_lt_one_subset_self hs ‹_› $ absorbent_nhds_zero $ hs₂.mem_nhds zero_mem).antisymm,
  convert interior_subset_gauge_lt_one s,
  exact hs₂.interior_eq.symm,
end

lemma gauge_lt_one_of_mem_of_open {s : set E} (hs : convex ℝ s) (zero_mem : (0 : E) ∈ s)
  (hs₂ : is_open s) (x : E) (hx : x ∈ s) :
  gauge s x < 1 :=
by rwa ←gauge_lt_one_eq_self_of_open hs zero_mem hs₂ at hx

lemma one_le_gauge_of_not_mem {s : set E} (hs : convex ℝ s) (zero_mem : (0 : E) ∈ s)
  (hs₂ : is_open s) {x : E} (hx : x ∉ s) :
  1 ≤ gauge s x :=
begin
  rw ←gauge_lt_one_eq_self_of_open hs zero_mem hs₂ at hx,
  exact le_of_not_lt hx
end

end topological_space

variables {α : Type*} [linear_ordered_field α] [mul_action_with_zero α ℝ] [ordered_smul α ℝ]

lemma gauge_smul_of_nonneg [mul_action_with_zero α E] [is_scalar_tower α ℝ (set E)] {s : set E}
  {r : α} (hr : 0 ≤ r) (x : E) :
  gauge s (r • x) = r • gauge s x :=
begin
  obtain rfl | hr' := hr.eq_or_lt,
  { rw [zero_smul, gauge_zero, zero_smul] },
  rw [gauge_def', gauge_def', ←real.Inf_smul_of_nonneg hr],
  congr' 1,
  ext β,
  simp_rw [set.mem_smul_set, set.mem_sep_eq],
  split,
  { rintro ⟨hβ, hx⟩,
    simp_rw [mem_Ioi] at ⊢ hβ,
    have := smul_pos (inv_pos.2 hr') hβ,
    refine ⟨r⁻¹ • β, ⟨this, _⟩, smul_inv_smul₀ hr'.ne' _⟩,
    rw ←mem_smul_set_iff_inv_smul_mem₀ at ⊢ hx,
    rwa [smul_assoc, mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr'.ne'), inv_inv₀],
    { exact this.ne' },
    { exact hβ.ne' } },
  { rintro ⟨β, ⟨hβ, hx⟩, rfl⟩,
    rw mem_Ioi at ⊢ hβ,
    have := smul_pos hr' hβ,
    refine ⟨this, _⟩,
    rw ←mem_smul_set_iff_inv_smul_mem₀ at ⊢ hx,
    rw smul_assoc,
    exact smul_mem_smul_set hx,
    { exact this.ne' },
    { exact hβ.ne'} }
end

/-- In textbooks, this is the homogeneity of the Minkowksi functional. -/
lemma gauge_smul [module α E] [is_scalar_tower α ℝ (set E)] {s : set E}
  (symmetric : ∀ x ∈ s, -x ∈ s) (r : α) (x : E) :
  gauge s (r • x) = abs r • gauge s x :=
begin
  rw ←gauge_smul_of_nonneg (abs_nonneg r),
  obtain h | h := abs_choice r,
  { rw h },
  { rw [h, neg_smul, gauge_neg symmetric] },
  { apply_instance }
end

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
  rwa [smul_smul, smul_smul, mul_comm_div', mul_comm_div', ←mul_div_assoc, ←mul_div_assoc,
    mul_inv_cancel ha.ne', mul_inv_cancel hb.ne', ←smul_add, one_div,
    ←mem_smul_set_iff_inv_smul_mem₀ hab.ne'] at this,
end

/-- `gauge s` as a seminorm when `s` is symmetric, convex and absorbent. -/
@[simps] def gauge_seminorm (symmetric : ∀ x ∈ s, -x ∈ s) (hs : convex ℝ s) (hs' : absorbent ℝ s) :
  seminorm ℝ E :=
{ to_fun := gauge s,
  smul' := λ r x, by rw [gauge_smul symmetric, real.norm_eq_abs, smul_eq_mul];
    apply_instance,
  triangle' := gauge_add_le hs hs' }

/-- Any seminorm arises a the gauge of its unit ball. -/
lemma seminorm.gauge_ball (p : seminorm ℝ E) : gauge (p.ball 0 1) = p :=
begin
  ext,
  obtain hp | hp := {r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1}.eq_empty_or_nonempty,
  { rw [gauge, hp, real.Inf_empty],
    by_contra,
    have hpx : 0 < p x := (p.nonneg x).lt_of_ne h,
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx,
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, _, smul_inv_smul₀ hpx₂.ne' _⟩,
    rw [p.mem_ball_zero, p.smul, real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂), inv_mul_lt_iff hpx₂,
      mul_one],
    exact lt_mul_of_one_lt_left hpx one_lt_two },
  refine is_glb.cInf_eq ⟨λ r, _, λ r hr, le_of_forall_pos_le_add $ λ ε hε, _⟩ hp,
  { rintro ⟨hr, y, hy, rfl⟩,
    rw p.mem_ball_zero at hy,
    rw [p.smul, real.norm_eq_abs, abs_of_pos hr],
    exact mul_le_of_le_one_right hr.le hy.le },
  { have hpε : 0 < p x + ε := add_pos_of_nonneg_of_pos (p.nonneg _) hε,
    refine hr ⟨hpε, (p x + ε)⁻¹ • x, _, smul_inv_smul₀ hpε.ne' _⟩,
    rw [p.mem_ball_zero, p.smul, real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε), inv_mul_lt_iff hpε,
      mul_one],
    exact lt_add_of_pos_right _ hε }
end

lemma seminorm.gauge_seminorm_ball (p : seminorm ℝ E) :
  gauge_seminorm (λ x, p.symmetric_ball_zero 1) (p.convex_ball 0 1)
    (p.absorbent_ball_zero zero_lt_one) = p :=
seminorm.ext p.gauge_ball

end gauge

-- TODO: topology induced by family of seminorms, local convexity.
