/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import order.liminf_limsup
import topology.algebra.uniform_group
import topology.metric_space.algebra
import topology.metric_space.isometry
import topology.sequences

/-!
# Normed (semi)groups

In this file we define four classes:

* `has_norm`, `has_nnnorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `∥x∥`) and `nnnorm : α → ℝ≥0` (notation: `∥x∥₊`), respectively;
* `semi_normed_group`: a seminormed group is an additive group with a norm and a pseudo metric space
  structures that agree with each other: `∀ x y, dist x y = ∥x - y∥`;
* `normed_group`: a normed group is an additive group with a norm and a metric space structures that
  agree with each other: `∀ x y, dist x y = ∥x - y∥`.

We also prove basic properties of (semi)normed groups and provide some instances.

## Tags

normed group
-/

variables {α ι E F : Type*}

open filter metric
open_locale topological_space big_operators nnreal ennreal uniformity pointwise

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ`. This class is designed to
be extended in more interesting classes specifying the properties of the norm. -/
class has_norm (E : Type*) := (norm : E → ℝ)

export has_norm (norm)

notation `∥` e `∥` := norm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class semi_normed_group (E : Type*) extends has_norm E, add_comm_group E, pseudo_metric_space E :=
(dist_eq : ∀ x y : E, dist x y = norm (x - y))

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines
a metric space structure. -/
class normed_group (E : Type*) extends has_norm E, add_comm_group E, metric_space E :=
(dist_eq : ∀ x y : E, dist x y = norm (x - y))

/-- A normed group is a seminormed group. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_group.to_semi_normed_group [h : normed_group E] : semi_normed_group E :=
{ .. h }

/-- Construct a seminormed group from a translation invariant pseudodistance. -/
def semi_normed_group.of_add_dist [has_norm E] [add_comm_group E] [pseudo_metric_space E]
  (H1 : ∀ x : E, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : E, dist x y ≤ dist (x + z) (y + z)) : semi_normed_group E :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 },
    { have := H2 (x - y) 0 y, rwa [sub_add_cancel, zero_add] at this }
  end }

/-- Construct a seminormed group from a translation invariant pseudodistance -/
def semi_normed_group.of_add_dist' [has_norm E] [add_comm_group E] [pseudo_metric_space E]
  (H1 : ∀ x : E, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : E, dist (x + z) (y + z) ≤ dist x y) : semi_normed_group E :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { have := H2 (x - y) 0 y, rwa [sub_add_cancel, zero_add] at this },
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 }
  end }

/-- A seminormed group can be built from a seminorm that satisfies algebraic properties. This is
formalised in this structure. -/
structure semi_normed_group.core (E : Type*) [add_comm_group E] [has_norm E] : Prop :=
(norm_zero : ∥(0 : E)∥ = 0)
(triangle : ∀ x y : E, ∥x + y∥ ≤ ∥x∥ + ∥y∥)
(norm_neg : ∀ x : E, ∥-x∥ = ∥x∥)

/-- Constructing a seminormed group from core properties of a seminorm, i.e., registering the
pseudodistance and the pseudometric space structure from the seminorm properties. Note that in most
cases this instance creates bad definitional equalities (e.g., it does not take into account
a possibly existing `uniform_space` instance on `E`). -/
def semi_normed_group.of_core (E : Type*) [add_comm_group E] [has_norm E]
  (C : semi_normed_group.core E) : semi_normed_group E :=
{ dist := λ x y, ∥x - y∥,
  dist_eq := assume x y, by refl,
  dist_self := assume x, by simp [C.norm_zero],
  dist_triangle := assume x y z,
    calc ∥x - z∥ = ∥x - y + (y - z)∥ : by rw sub_add_sub_cancel
            ... ≤ ∥x - y∥ + ∥y - z∥  : C.triangle _ _,
  dist_comm := assume x y,
    calc ∥x - y∥ = ∥ -(y - x)∥ : by simp
             ... = ∥y - x∥ : by { rw [C.norm_neg] } }

instance : normed_group punit :=
{ norm := function.const _ 0,
  dist_eq := λ _ _, rfl, }

@[simp] lemma punit.norm_eq_zero (r : punit) : ∥r∥ = 0 := rfl

noncomputable instance : normed_group ℝ :=
{ norm := λ x, |x|,
  dist_eq := assume x y, rfl }

lemma real.norm_eq_abs (r : ℝ) : ∥r∥ = |r| := rfl

section semi_normed_group
variables [semi_normed_group E] [semi_normed_group F]

lemma dist_eq_norm (g h : E) : dist g h = ∥g - h∥ :=
semi_normed_group.dist_eq _ _

lemma dist_eq_norm' (g h : E) : dist g h = ∥h - g∥ :=
by rw [dist_comm, dist_eq_norm]

@[simp] lemma dist_zero_right (g : E) : dist g 0 = ∥g∥ :=
by rw [dist_eq_norm, sub_zero]

@[simp] lemma dist_zero_left : dist (0 : E) = norm :=
funext $ λ g, by rw [dist_comm, dist_zero_right]

lemma tendsto_norm_cocompact_at_top [proper_space E] :
  tendsto norm (cocompact E) at_top :=
by simpa only [dist_zero_right] using tendsto_dist_right_cocompact_at_top (0 : E)

lemma norm_sub_rev (g h : E) : ∥g - h∥ = ∥h - g∥ :=
by simpa only [dist_eq_norm] using dist_comm g h

@[simp] lemma norm_neg (g : E) : ∥-g∥ = ∥g∥ :=
by simpa using norm_sub_rev 0 g

@[simp] lemma dist_add_left (g h₁ h₂ : E) : dist (g + h₁) (g + h₂) = dist h₁ h₂ :=
by simp [dist_eq_norm]

@[simp] lemma dist_add_right (g₁ g₂ h : E) : dist (g₁ + h) (g₂ + h) = dist g₁ g₂ :=
by simp [dist_eq_norm]

@[simp] lemma dist_neg_neg (g h : E) : dist (-g) (-h) = dist g h :=
by simp only [dist_eq_norm, neg_sub_neg, norm_sub_rev]

@[simp] lemma dist_sub_left (g h₁ h₂ : E) : dist (g - h₁) (g - h₂) = dist h₁ h₂ :=
by simp only [sub_eq_add_neg, dist_add_left, dist_neg_neg]

@[simp] lemma dist_sub_right (g₁ g₂ h : E) : dist (g₁ - h) (g₂ - h) = dist g₁ g₂ :=
by simpa only [sub_eq_add_neg] using dist_add_right _ _ _

/-- **Triangle inequality** for the norm. -/
lemma norm_add_le (g h : E) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
by simpa [dist_eq_norm] using dist_triangle g 0 (-h)

lemma norm_add_le_of_le {g₁ g₂ : E} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) :
  ∥g₁ + g₂∥ ≤ n₁ + n₂ :=
le_trans (norm_add_le g₁ g₂) (add_le_add H₁ H₂)

lemma dist_add_add_le (g₁ g₂ h₁ h₂ : E) :
  dist (g₁ + g₂) (h₁ + h₂) ≤ dist g₁ h₁ + dist g₂ h₂ :=
by simpa only [dist_add_left, dist_add_right] using dist_triangle (g₁ + g₂) (h₁ + g₂) (h₁ + h₂)

lemma dist_add_add_le_of_le {g₁ g₂ h₁ h₂ : E} {d₁ d₂ : ℝ}
  (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁ + g₂) (h₁ + h₂) ≤ d₁ + d₂ :=
le_trans (dist_add_add_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

lemma dist_sub_sub_le (g₁ g₂ h₁ h₂ : E) :
  dist (g₁ - g₂) (h₁ - h₂) ≤ dist g₁ h₁ + dist g₂ h₂ :=
by simpa only [sub_eq_add_neg, dist_neg_neg] using dist_add_add_le g₁ (-g₂) h₁ (-h₂)

lemma dist_sub_sub_le_of_le {g₁ g₂ h₁ h₂ : E} {d₁ d₂ : ℝ}
  (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁ - g₂) (h₁ - h₂) ≤ d₁ + d₂ :=
le_trans (dist_sub_sub_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

lemma abs_dist_sub_le_dist_add_add (g₁ g₂ h₁ h₂ : E) :
  |dist g₁ h₁ - dist g₂ h₂| ≤ dist (g₁ + g₂) (h₁ + h₂) :=
by simpa only [dist_add_left, dist_add_right, dist_comm h₂]
  using abs_dist_sub_le (g₁ + g₂) (h₁ + h₂) (h₁ + g₂)

@[simp] lemma norm_nonneg (g : E) : 0 ≤ ∥g∥ :=
by { rw[←dist_zero_right], exact dist_nonneg }

@[simp] lemma norm_zero : ∥(0 : E)∥ = 0 :=  by rw [← dist_zero_right, dist_self]

@[nontriviality] lemma norm_of_subsingleton [subsingleton E] (x : E) : ∥x∥ = 0 :=
by rw [subsingleton.elim x 0, norm_zero]

lemma norm_sum_le (s : finset ι) (f : ι → E) : ∥∑ i in s, f i∥ ≤ ∑ i in s, ∥f i∥ :=
s.le_sum_of_subadditive norm norm_zero norm_add_le f

lemma norm_sum_le_of_le (s : finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ∥f b∥ ≤ n b) :
  ∥∑ b in s, f b∥ ≤ ∑ b in s, n b :=
le_trans (norm_sum_le s f) (finset.sum_le_sum h)

lemma dist_sum_sum_le_of_le (s : finset ι) {f g : ι → E} {d : ι → ℝ}
  (h : ∀ b ∈ s, dist (f b) (g b) ≤ d b) :
  dist (∑ b in s, f b) (∑ b in s, g b) ≤ ∑ b in s, d b :=
begin
  simp only [dist_eq_norm, ← finset.sum_sub_distrib] at *,
  exact norm_sum_le_of_le s h
end

lemma dist_sum_sum_le (s : finset ι) (f g : ι → E) :
  dist (∑ b in s, f b) (∑ b in s, g b) ≤ ∑ b in s, dist (f b) (g b) :=
dist_sum_sum_le_of_le s (λ _ _, le_rfl)

lemma norm_sub_le (g h : E) : ∥g - h∥ ≤ ∥g∥ + ∥h∥ :=
by simpa [dist_eq_norm] using dist_triangle g 0 h

lemma norm_sub_le_of_le {g₁ g₂ : E} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) :
  ∥g₁ - g₂∥ ≤ n₁ + n₂ :=
le_trans (norm_sub_le g₁ g₂) (add_le_add H₁ H₂)

lemma dist_le_norm_add_norm (g h : E) : dist g h ≤ ∥g∥ + ∥h∥ :=
by { rw dist_eq_norm, apply norm_sub_le }

lemma abs_norm_sub_norm_le (g h : E) : |∥g∥ - ∥h∥| ≤ ∥g - h∥ :=
by simpa [dist_eq_norm] using abs_dist_sub_le g h 0

lemma norm_sub_norm_le (g h : E) : ∥g∥ - ∥h∥ ≤ ∥g - h∥ :=
le_trans (le_abs_self _) (abs_norm_sub_norm_le g h)

lemma dist_norm_norm_le (g h : E) : dist ∥g∥ ∥h∥ ≤ ∥g - h∥ :=
abs_norm_sub_norm_le g h

lemma norm_le_insert (u v : E) : ∥v∥ ≤ ∥u∥ + ∥u - v∥ :=
calc ∥v∥ = ∥u - (u - v)∥ : by abel
... ≤ ∥u∥ + ∥u - v∥ : norm_sub_le u _

lemma norm_le_insert' (u v : E) : ∥u∥ ≤ ∥v∥ + ∥u - v∥ :=
by { rw norm_sub_rev, exact norm_le_insert v u }

lemma norm_le_add_norm_add (u v : E) :
  ∥u∥ ≤ ∥u + v∥ + ∥v∥ :=
calc ∥u∥ = ∥u + v - v∥ : by rw add_sub_cancel
... ≤ ∥u + v∥ + ∥v∥ : norm_sub_le _ _

lemma ball_zero_eq (ε : ℝ) : ball (0 : E) ε = {x | ∥x∥ < ε} :=
set.ext $ assume a, by simp

lemma mem_ball_iff_norm {g h : E} {r : ℝ} :
  h ∈ ball g r ↔ ∥h - g∥ < r :=
by rw [mem_ball, dist_eq_norm]

lemma add_mem_ball_iff_norm {g h : E} {r : ℝ} :
  g + h ∈ ball g r ↔ ∥h∥ < r :=
by rw [mem_ball_iff_norm, add_sub_cancel']

lemma mem_ball_iff_norm' {g h : E} {r : ℝ} :
  h ∈ ball g r ↔ ∥g - h∥ < r :=
by rw [mem_ball', dist_eq_norm]

@[simp] lemma mem_ball_zero_iff {ε : ℝ} {x : E} : x ∈ ball (0 : E) ε ↔ ∥x∥ < ε :=
by rw [mem_ball, dist_zero_right]

lemma mem_closed_ball_iff_norm {g h : E} {r : ℝ} :
  h ∈ closed_ball g r ↔ ∥h - g∥ ≤ r :=
by rw [mem_closed_ball, dist_eq_norm]

@[simp] lemma mem_closed_ball_zero_iff {ε : ℝ} {x : E} : x ∈ closed_ball (0 : E) ε ↔ ∥x∥ ≤ ε :=
by rw [mem_closed_ball, dist_zero_right]

lemma add_mem_closed_ball_iff_norm {g h : E} {r : ℝ} :
  g + h ∈ closed_ball g r ↔ ∥h∥ ≤ r :=
by rw [mem_closed_ball_iff_norm, add_sub_cancel']

lemma mem_closed_ball_iff_norm' {g h : E} {r : ℝ} :
  h ∈ closed_ball g r ↔ ∥g - h∥ ≤ r :=
by rw [mem_closed_ball', dist_eq_norm]

lemma norm_le_of_mem_closed_ball {g h : E} {r : ℝ} (H : h ∈ closed_ball g r) :
  ∥h∥ ≤ ∥g∥ + r :=
calc
  ∥h∥ = ∥g + (h - g)∥ : by rw [add_sub_cancel'_right]
  ... ≤ ∥g∥ + ∥h - g∥  : norm_add_le _ _
  ... ≤ ∥g∥ + r : by { apply add_le_add_left, rw ← dist_eq_norm, exact H }

lemma norm_le_norm_add_const_of_dist_le {a b : E} {c : ℝ} (h : dist a b ≤ c) :
  ∥a∥ ≤ ∥b∥ + c :=
norm_le_of_mem_closed_ball h

lemma norm_lt_of_mem_ball {g h : E} {r : ℝ} (H : h ∈ ball g r) :
  ∥h∥ < ∥g∥ + r :=
calc
  ∥h∥ = ∥g + (h - g)∥ : by rw [add_sub_cancel'_right]
  ... ≤ ∥g∥ + ∥h - g∥  : norm_add_le _ _
  ... < ∥g∥ + r : by { apply add_lt_add_left, rw ← dist_eq_norm, exact H }

lemma norm_lt_norm_add_const_of_dist_lt {a b : E} {c : ℝ} (h : dist a b < c) :
  ∥a∥ < ∥b∥ + c :=
norm_lt_of_mem_ball h

lemma bounded_iff_forall_norm_le {s : set E} : bounded s ↔ ∃ C, ∀ x ∈ s, ∥x∥ ≤ C :=
by simpa only [set.subset_def, mem_closed_ball_iff_norm, sub_zero]
  using bounded_iff_subset_ball (0 : E)

@[simp] lemma preimage_add_ball (x y : E) (r : ℝ) : ((+) y) ⁻¹' (ball x r) = ball (x - y) r :=
begin
  ext z,
  simp only [dist_eq_norm, set.mem_preimage, mem_ball],
  abel
end

@[simp] lemma preimage_add_closed_ball (x y : E) (r : ℝ) :
  ((+) y) ⁻¹' (closed_ball x r) = closed_ball (x - y) r :=
begin
  ext z,
  simp only [dist_eq_norm, set.mem_preimage, mem_closed_ball],
  abel
end

@[simp] lemma mem_sphere_iff_norm (v w : E) (r : ℝ) : w ∈ sphere v r ↔ ∥w - v∥ = r :=
by simp [dist_eq_norm]

@[simp] lemma mem_sphere_zero_iff_norm {w : E} {r : ℝ} : w ∈ sphere (0:E) r ↔ ∥w∥ = r :=
by simp [dist_eq_norm]

@[simp] lemma norm_eq_of_mem_sphere {r : ℝ} (x : sphere (0:E) r) : ∥(x:E)∥ = r :=
mem_sphere_zero_iff_norm.mp x.2

lemma preimage_add_sphere (x y : E) (r : ℝ) :
  ((+) y) ⁻¹' (sphere x r) = sphere (x - y) r :=
begin
  ext z,
  simp only [set.mem_preimage, mem_sphere_iff_norm],
  abel
end

lemma ne_zero_of_norm_pos {g : E} : 0 < ∥ g ∥ → g ≠ 0 :=
begin
  intros hpos hzero,
  rw [hzero, norm_zero] at hpos,
  exact lt_irrefl 0 hpos,
end

lemma nonzero_of_mem_sphere {r : ℝ} (hr : 0 < r) (x : sphere (0:E) r) : (x:E) ≠ 0 :=
begin
  refine ne_zero_of_norm_pos _,
  rwa norm_eq_of_mem_sphere x,
end

lemma nonzero_of_mem_unit_sphere (x : sphere (0:E) 1) : (x:E) ≠ 0 :=
by { apply nonzero_of_mem_sphere, norm_num }

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_neg (sphere (0:E) r) :=
{ neg := λ w, ⟨-↑w, by simp⟩ }

@[simp] lemma coe_neg_sphere {r : ℝ} (v : sphere (0:E) r) :
  (((-v) : sphere _ _) : E) = - (v:E) :=
rfl

namespace isometric
-- TODO This material is superseded by similar constructions such as
-- `affine_isometry_equiv.const_vadd`; deduplicate

/-- Addition `y ↦ y + x` as an `isometry`. -/
protected def add_right (x : E) : E ≃ᵢ E :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ y z, dist_add_right _ _ _,
  .. equiv.add_right x }

@[simp] lemma add_right_to_equiv (x : E) :
  (isometric.add_right x).to_equiv = equiv.add_right x := rfl

@[simp] lemma coe_add_right (x : E) : (isometric.add_right x : E → E) = λ y, y + x := rfl

lemma add_right_apply (x y : E) : (isometric.add_right x : E → E) y = y + x := rfl

@[simp] lemma add_right_symm (x : E) :
  (isometric.add_right x).symm = isometric.add_right (-x) :=
ext $ λ y, rfl

/-- Addition `y ↦ x + y` as an `isometry`. -/
protected def add_left (x : E) : E ≃ᵢ E :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ y z, dist_add_left _ _ _,
  to_equiv := equiv.add_left x }

@[simp] lemma add_left_to_equiv (x : E) :
  (isometric.add_left x).to_equiv = equiv.add_left x := rfl

@[simp] lemma coe_add_left (x : E) : ⇑(isometric.add_left x) = (+) x := rfl

@[simp] lemma add_left_symm (x : E) :
  (isometric.add_left x).symm = isometric.add_left (-x) :=
ext $ λ y, rfl

variable (E)

/-- Negation `x ↦ -x` as an `isometry`. -/
protected def neg : E ≃ᵢ E :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ x y, dist_neg_neg _ _,
  to_equiv := equiv.neg E }

variable {E}

@[simp] lemma neg_symm : (isometric.neg E).symm = isometric.neg E := rfl

@[simp] lemma neg_to_equiv : (isometric.neg E).to_equiv = equiv.neg E := rfl

@[simp] lemma coe_neg : ⇑(isometric.neg E) = has_neg.neg := rfl

end isometric

theorem normed_group.tendsto_nhds_zero {f : α → E} {l : filter α} :
  tendsto f l (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in l, ∥ f x ∥ < ε :=
metric.tendsto_nhds.trans $ by simp only [dist_zero_right]

lemma normed_group.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
  tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ∥x' - x∥ < δ → ∥f x' - y∥ < ε :=
by simp_rw [metric.tendsto_nhds_nhds, dist_eq_norm]

lemma normed_group.cauchy_seq_iff [nonempty α] [semilattice_sup α] {u : α → E} :
  cauchy_seq u ↔ ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ∥u m - u n∥ < ε :=
by simp [metric.cauchy_seq_iff, dist_eq_norm]

lemma normed_group.uniformity_basis_dist :
  (𝓤 E).has_basis (λ (ε : ℝ), 0 < ε) (λ ε, {p : E × E | ∥p.fst - p.snd∥ < ε}) :=
begin
  convert metric.uniformity_basis_dist,
  simp [dist_eq_norm]
end

open finset

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`. -/
lemma add_monoid_hom.lipschitz_of_bound (f : E →+ F) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  lipschitz_with (real.to_nnreal C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

lemma lipschitz_on_with_iff_norm_sub_le {f : E → F} {C : ℝ≥0} {s : set E} :
  lipschitz_on_with C f s ↔  ∀ (x ∈ s) (y ∈ s), ∥f x - f y∥ ≤ C * ∥x - y∥ :=
by simp only [lipschitz_on_with_iff_dist_le_mul, dist_eq_norm]

lemma lipschitz_on_with.norm_sub_le {f : E → F} {C : ℝ≥0} {s : set E} (h : lipschitz_on_with C f s)
  {x y : E} (x_in : x ∈ s) (y_in : y ∈ s) : ∥f x - f y∥ ≤ C * ∥x - y∥ :=
lipschitz_on_with_iff_norm_sub_le.mp h x x_in y y_in

lemma lipschitz_on_with.norm_sub_le_of_le {f : E → F} {C : ℝ≥0} {s : set E}
  (h : lipschitz_on_with C f s){x y : E} (x_in : x ∈ s) (y_in : y ∈ s) {d : ℝ} (hd : ∥x - y∥ ≤ d) :
  ∥f x - f y∥ ≤ C * d :=
(h.norm_sub_le x_in y_in).trans $ mul_le_mul_of_nonneg_left hd C.2

lemma lipschitz_with_iff_norm_sub_le {f : E → F} {C : ℝ≥0} :
  lipschitz_with C f ↔ ∀ x y, ∥f x - f y∥ ≤ C * ∥x - y∥ :=
by simp only [lipschitz_with_iff_dist_le_mul, dist_eq_norm]

alias lipschitz_with_iff_norm_sub_le ↔ lipschitz_with.norm_sub_le _

lemma lipschitz_with.norm_sub_le_of_le {f : E → F} {C : ℝ≥0} (h : lipschitz_with C f)
  {x y : E} {d : ℝ} (hd : ∥x - y∥ ≤ d) :
  ∥f x - f y∥ ≤ C * d :=
(h.norm_sub_le x y).trans $ mul_le_mul_of_nonneg_left hd C.2

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`.
The analogous condition for a linear map of normed spaces is in `normed_space.operator_norm`. -/
lemma add_monoid_hom.continuous_of_bound (f : E →+ F) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  continuous f :=
(f.lipschitz_of_bound C h).continuous

lemma is_compact.exists_bound_of_continuous_on [topological_space α]
  {s : set α} (hs : is_compact s) {f : α → E} (hf : continuous_on f s) :
  ∃ C, ∀ x ∈ s, ∥f x∥ ≤ C :=
begin
  have : bounded (f '' s) := (hs.image_of_continuous_on hf).bounded,
  rcases bounded_iff_forall_norm_le.1 this with ⟨C, hC⟩,
  exact ⟨C, λ x hx, hC _ (set.mem_image_of_mem _ hx)⟩,
end

lemma add_monoid_hom.isometry_iff_norm (f : E →+ F) : isometry f ↔ ∀ x, ∥f x∥ = ∥x∥ :=
begin
  simp only [isometry_emetric_iff_metric, dist_eq_norm, ← f.map_sub],
  refine ⟨λ h x, _, λ h x y, h _⟩,
  simpa using h x 0
end

lemma add_monoid_hom.isometry_of_norm (f : E →+ F) (hf : ∀ x, ∥f x∥ = ∥x∥) : isometry f :=
f.isometry_iff_norm.2 hf

lemma controlled_sum_of_mem_closure {s : add_subgroup E} {g : E}
  (hg : g ∈ closure (s : set E)) {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ v : ℕ → E,
    tendsto (λ n, ∑ i in range (n+1), v i) at_top (𝓝 g) ∧
    (∀ n, v n ∈ s) ∧
    ∥v 0 - g∥ < b 0 ∧
    ∀ n > 0, ∥v n∥ < b n :=
begin
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : tendsto u at_top (𝓝 g)⟩ :=
    mem_closure_iff_seq_limit.mp hg,
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ∥u n - g∥ < b 0,
  { have : {x | ∥x - g∥ < b 0} ∈ 𝓝 g,
    { simp_rw ← dist_eq_norm,
      exact metric.ball_mem_nhds _ (b_pos _) },
    exact filter.tendsto_at_top'.mp lim_u _ this },
  set z : ℕ → E := λ n, u (n + n₀),
  have lim_z : tendsto z at_top (𝓝 g) := lim_u.comp (tendsto_add_at_top_nat n₀),
  have mem_𝓤 : ∀ n, {p : E × E | ∥p.1 - p.2∥ < b (n + 1)} ∈ 𝓤 E :=
  λ n, by simpa [← dist_eq_norm] using metric.dist_mem_uniformity (b_pos $ n+1),
  obtain ⟨φ : ℕ → ℕ, φ_extr : strict_mono φ,
          hφ : ∀ n, ∥z (φ $ n + 1) - z (φ n)∥ < b (n + 1)⟩ :=
    lim_z.cauchy_seq.subseq_mem mem_𝓤,
  set w : ℕ → E := z ∘ φ,
  have hw : tendsto w at_top (𝓝 g),
    from lim_z.comp φ_extr.tendsto_at_top,
  set v : ℕ → E := λ i, if i = 0 then w 0 else w i - w (i - 1),
  refine ⟨v, tendsto.congr (finset.eq_sum_range_sub' w) hw , _,
          hn₀ _ (n₀.le_add_left _), _⟩,
  { rintro ⟨⟩,
    { change w 0 ∈ s,
      apply u_in },
    { apply s.sub_mem ; apply u_in }, },
  { intros l hl,
    obtain ⟨k, rfl⟩ : ∃ k, l = k+1, exact nat.exists_eq_succ_of_ne_zero (ne_of_gt hl),
    apply hφ },
end

lemma controlled_sum_of_mem_closure_range {j : E →+ F} {h : F}
  (Hh : h ∈ (closure $ (j.range : set F))) {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ g : ℕ → E,
    tendsto (λ n, ∑ i in range (n+1), j (g i)) at_top (𝓝 h) ∧
    ∥j (g 0) - h∥ < b 0 ∧
    ∀ n > 0, ∥j (g n)∥ < b n :=
begin
  rcases controlled_sum_of_mem_closure Hh b_pos with ⟨v, sum_v, v_in, hv₀, hv_pos⟩,
  choose g hg using v_in,
  change ∀ (n : ℕ), j (g n) = v n at hg,
  refine ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀, λ n hn,
          by simpa [hg] using hv_pos n hn⟩
end

section nnnorm

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0`. -/
class has_nnnorm (E : Type*) := (nnnorm : E → ℝ≥0)

export has_nnnorm (nnnorm)

notation `∥`e`∥₊` := nnnorm e

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_group.to_has_nnnorm : has_nnnorm E := ⟨λ a, ⟨norm a, norm_nonneg a⟩⟩

@[simp, norm_cast] lemma coe_nnnorm (a : E) : (∥a∥₊ : ℝ) = norm a := rfl

lemma norm_to_nnreal {a : E} : ∥a∥.to_nnreal = ∥a∥₊ :=
@real.to_nnreal_coe ∥a∥₊

lemma nndist_eq_nnnorm (a b : E) : nndist a b = ∥a - b∥₊ := nnreal.eq $ dist_eq_norm _ _

@[simp] lemma nnnorm_zero : ∥(0 : E)∥₊ = 0 :=
nnreal.eq norm_zero

lemma nnnorm_add_le (g h : E) : ∥g + h∥₊ ≤ ∥g∥₊ + ∥h∥₊ :=
nnreal.coe_le_coe.1 $ norm_add_le g h

@[simp] lemma nnnorm_neg (g : E) : ∥-g∥₊ = ∥g∥₊ :=
nnreal.eq $ norm_neg g

lemma nndist_nnnorm_nnnorm_le (g h : E) : nndist ∥g∥₊ ∥h∥₊ ≤ ∥g - h∥₊ :=
nnreal.coe_le_coe.1 $ dist_norm_norm_le g h

lemma of_real_norm_eq_coe_nnnorm (x : E) : ennreal.of_real ∥x∥ = (∥x∥₊ : ℝ≥0∞) :=
ennreal.of_real_eq_coe_nnreal _

lemma edist_eq_coe_nnnorm_sub (x y : E) : edist x y = (∥x - y∥₊ : ℝ≥0∞) :=
by rw [edist_dist, dist_eq_norm, of_real_norm_eq_coe_nnnorm]

lemma edist_eq_coe_nnnorm (x : E) : edist x 0 = (∥x∥₊ : ℝ≥0∞) :=
by rw [edist_eq_coe_nnnorm_sub, _root_.sub_zero]

lemma mem_emetric_ball_zero_iff {x : E} {r : ℝ≥0∞} : x ∈ emetric.ball (0 : E) r ↔ ↑∥x∥₊ < r :=
by rw [emetric.mem_ball, edist_eq_coe_nnnorm]

lemma nndist_add_add_le (g₁ g₂ h₁ h₂ : E) :
  nndist (g₁ + g₂) (h₁ + h₂) ≤ nndist g₁ h₁ + nndist g₂ h₂ :=
nnreal.coe_le_coe.1 $ dist_add_add_le g₁ g₂ h₁ h₂

lemma edist_add_add_le (g₁ g₂ h₁ h₂ : E) :
  edist (g₁ + g₂) (h₁ + h₂) ≤ edist g₁ h₁ + edist g₂ h₂ :=
by { simp only [edist_nndist], norm_cast, apply nndist_add_add_le }

lemma nnnorm_sum_le (s : finset ι) (f : ι → E) :
  ∥∑ a in s, f a∥₊ ≤ ∑ a in s, ∥f a∥₊ :=
s.le_sum_of_subadditive nnnorm nnnorm_zero nnnorm_add_le f

lemma add_monoid_hom.lipschitz_of_bound_nnnorm (f : E →+ F) (C : ℝ≥0) (h : ∀ x, ∥f x∥₊ ≤ C * ∥x∥₊) :
  lipschitz_with C f :=
@real.to_nnreal_coe C ▸ f.lipschitz_of_bound C h

end nnnorm

namespace lipschitz_with

variables [pseudo_emetric_space α] {K Kf Kg : ℝ≥0} {f g : α → E}

lemma neg (hf : lipschitz_with K f) : lipschitz_with K (λ x, -f x) :=
λ x y, by simpa only [edist_dist, dist_neg_neg] using hf x y

lemma add (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x + g x) :=
λ x y,
calc edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_add_add_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma sub (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x - g x) :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

end lipschitz_with

namespace antilipschitz_with

variables [pseudo_emetric_space α] {K Kf Kg : ℝ≥0} {f g : α → E}

lemma add_lipschitz_with (hf : antilipschitz_with Kf f) (hg : lipschitz_with Kg g)
  (hK : Kg < Kf⁻¹) : antilipschitz_with (Kf⁻¹ - Kg)⁻¹ (λ x, f x + g x) :=
begin
  letI : pseudo_metric_space α := pseudo_emetric_space.to_pseudo_metric_space hf.edist_ne_top,
  refine antilipschitz_with.of_le_mul_dist (λ x y, _),
  rw [nnreal.coe_inv, ← div_eq_inv_mul],
  rw le_div_iff (nnreal.coe_pos.2 $ tsub_pos_iff_lt.2 hK),
  rw [mul_comm, nnreal.coe_sub hK.le, sub_mul],
  calc ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :
    sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
  ... ≤ _ : le_trans (le_abs_self _) (abs_dist_sub_le_dist_add_add _ _ _ _)
end

lemma add_sub_lipschitz_with (hf : antilipschitz_with Kf f) (hg : lipschitz_with Kg (g - f))
  (hK : Kg < Kf⁻¹) : antilipschitz_with (Kf⁻¹ - Kg)⁻¹ g :=
by simpa only [pi.sub_apply, add_sub_cancel'_right] using hf.add_lipschitz_with hg hK

end antilipschitz_with

/-- A group homomorphism from an `add_comm_group` to a `semi_normed_group` induces a
`semi_normed_group` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def semi_normed_group.induced {E} [add_comm_group E] (f : E →+ F) : semi_normed_group E :=
{ norm    := λ x, ∥f x∥,
  dist_eq := λ x y, by simpa only [add_monoid_hom.map_sub, ← dist_eq_norm],
  .. pseudo_metric_space.induced f semi_normed_group.to_pseudo_metric_space, }

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
instance add_subgroup.semi_normed_group (s : add_subgroup E) : semi_normed_group s :=
semi_normed_group.induced s.subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[simp] lemma coe_norm_subgroup {E : Type*} [semi_normed_group E] {s : add_subgroup E} (x : s) :
  ∥x∥ = ∥(x:E)∥ :=
rfl

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance submodule.semi_normed_group {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} (s : submodule 𝕜 E) : semi_normed_group s :=
{ norm := λx, norm (x : E),
  dist_eq := λx y, dist_eq_norm (x : E) (y : E) }

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

See note [implicit instance arguments]. -/
@[simp, norm_cast] lemma submodule.norm_coe {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} {s : submodule 𝕜 E} (x : s) :
  ∥(x : E)∥ = ∥x∥ :=
rfl

@[simp] lemma submodule.norm_mk {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} {s : submodule 𝕜 E} (x : E) (hx : x ∈ s) :
  ∥(⟨x, hx⟩ : s)∥ = ∥x∥ :=
rfl

/-- seminormed group instance on the product of two seminormed groups, using the sup norm. -/
noncomputable instance prod.semi_normed_group : semi_normed_group (E × F) :=
{ norm := λx, max ∥x.1∥ ∥x.2∥,
  dist_eq := assume (x y : E × F),
    show max (dist x.1 y.1) (dist x.2 y.2) = (max ∥(x - y).1∥ ∥(x - y).2∥), by simp [dist_eq_norm] }

lemma prod.semi_norm_def (x : E × F) : ∥x∥ = (max ∥x.1∥ ∥x.2∥) := rfl

lemma prod.nnsemi_norm_def (x : E × F) : ∥x∥₊ = max (∥x.1∥₊) (∥x.2∥₊) :=
by { have := x.semi_norm_def, simp only [← coe_nnnorm] at this, exact_mod_cast this }

lemma semi_norm_fst_le (x : E × F) : ∥x.1∥ ≤ ∥x∥ :=
le_max_left _ _

lemma semi_norm_snd_le (x : E × F) : ∥x.2∥ ≤ ∥x∥ :=
le_max_right _ _

lemma semi_norm_prod_le_iff {x : E × F} {r : ℝ} :
  ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
max_le_iff

/-- seminormed group instance on the product of finitely many seminormed groups,
using the sup norm. -/
noncomputable instance pi.semi_normed_group {π : ι → Type*} [fintype ι]
  [Π i, semi_normed_group (π i)] : semi_normed_group (Π i, π i) :=
{ norm := λf, ((finset.sup finset.univ (λ b, ∥f b∥₊) : ℝ≥0) : ℝ),
  dist_eq := assume x y,
    congr_arg (coe : ℝ≥0 → ℝ) $ congr_arg (finset.sup finset.univ) $ funext $ assume a,
    show nndist (x a) (y a) = ∥x a - y a∥₊, from nndist_eq_nnnorm _ _ }

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
lemma pi_semi_norm_le_iff {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] {r : ℝ}
  (hr : 0 ≤ r) {x : Πi, π i} : ∥x∥ ≤ r ↔ ∀i, ∥x i∥ ≤ r :=
by simp only [← dist_zero_right, dist_pi_le_iff hr, pi.zero_apply]

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
lemma pi_semi_norm_lt_iff {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] {r : ℝ}
  (hr : 0 < r) {x : Πi, π i} : ∥x∥ < r ↔ ∀i, ∥x i∥ < r :=
by simp only [← dist_zero_right, dist_pi_lt_iff hr, pi.zero_apply]

lemma semi_norm_le_pi_norm {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] (x : Πi, π i)
  (i : ι) : ∥x i∥ ≤ ∥x∥ :=
(pi_semi_norm_le_iff (norm_nonneg x)).1 (le_refl _) i

@[simp] lemma pi_semi_norm_const [nonempty ι] [fintype ι] (a : E) : ∥(λ i : ι, a)∥ = ∥a∥ :=
by simpa only [← dist_zero_right] using dist_pi_const a 0

@[simp] lemma pi_nnsemi_norm_const [nonempty ι] [fintype ι] (a : E) :
  ∥(λ i : ι, a)∥₊ = ∥a∥₊ :=
nnreal.eq $ pi_semi_norm_const a

lemma tendsto_iff_norm_tendsto_zero {f : α → E} {a : filter α} {b : E} :
  tendsto f a (𝓝 b) ↔ tendsto (λ e, ∥f e - b∥) a (𝓝 0) :=
by { convert tendsto_iff_dist_tendsto_zero, simp [dist_eq_norm] }

lemma is_bounded_under_of_tendsto {l : filter α} {f : α → E} {c : E}
  (h : filter.tendsto f l (𝓝 c)) : is_bounded_under (≤) l (λ x, ∥f x∥) :=
⟨∥c∥ + 1, @tendsto.eventually α E f _ _ (λ k, ∥k∥ ≤ ∥c∥ + 1) h (filter.eventually_iff_exists_mem.mpr
  ⟨metric.closed_ball c 1, metric.closed_ball_mem_nhds c zero_lt_one,
    λ y hy, norm_le_norm_add_const_of_dist_le hy⟩)⟩

lemma tendsto_zero_iff_norm_tendsto_zero {f : α → E} {a : filter α} :
  tendsto f a (𝓝 0) ↔ tendsto (λ e, ∥f e∥) a (𝓝 0) :=
by { rw [tendsto_iff_norm_tendsto_zero], simp only [sub_zero] }

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `g` which tends to `0`, then `f` tends to `0`.
In this pair of lemmas (`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of
similar lemmas in `topology.metric_space.basic` and `topology.algebra.ordered`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
lemma squeeze_zero_norm' {f : α → E} {g : α → ℝ} {t₀ : filter α}
  (h : ∀ᶠ n in t₀, ∥f n∥ ≤ g n)
  (h' : tendsto g t₀ (𝓝 0)) : tendsto f t₀ (𝓝 0) :=
tendsto_zero_iff_norm_tendsto_zero.mpr
  (squeeze_zero' (eventually_of_forall (λ n, norm_nonneg _)) h h')

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `g` which
tends to `0`, then `f` tends to `0`.  -/
lemma squeeze_zero_norm {f : α → E} {g : α → ℝ} {t₀ : filter α}
  (h : ∀ n, ∥f n∥ ≤ g n) (h' : tendsto g t₀ (𝓝 0)) :
  tendsto f t₀ (𝓝 0) :=
squeeze_zero_norm' (eventually_of_forall h) h'

lemma tendsto_norm_sub_self (x : E) : tendsto (λ g : E, ∥g - x∥) (𝓝 x) (𝓝 0) :=
by simpa [dist_eq_norm] using tendsto_id.dist (tendsto_const_nhds : tendsto (λ g, (x:E)) (𝓝 x) _)

lemma tendsto_norm {x : E} : tendsto (λg : E, ∥g∥) (𝓝 x) (𝓝 ∥x∥) :=
by simpa using tendsto_id.dist (tendsto_const_nhds : tendsto (λ g, (0:E)) _ _)

lemma tendsto_norm_zero : tendsto (λg : E, ∥g∥) (𝓝 0) (𝓝 0) :=
by simpa using tendsto_norm_sub_self (0:E)

@[continuity]
lemma continuous_norm : continuous (λg:E, ∥g∥) :=
by simpa using continuous_id.dist (continuous_const : continuous (λ g, (0:E)))

@[continuity]
lemma continuous_nnnorm : continuous (λ (a : E), ∥a∥₊) :=
continuous_subtype_mk _ continuous_norm

lemma lipschitz_with_one_norm : lipschitz_with 1 (norm : E → ℝ) :=
by simpa only [dist_zero_left] using lipschitz_with.dist_right (0 : E)

lemma uniform_continuous_norm : uniform_continuous (norm : E → ℝ) :=
lipschitz_with_one_norm.uniform_continuous

lemma uniform_continuous_nnnorm : uniform_continuous (λ (a : E), ∥a∥₊) :=
uniform_continuous_subtype_mk uniform_continuous_norm _

section

variables {l : filter α} {f : α → E} {a : E}

lemma filter.tendsto.norm (h : tendsto f l (𝓝 a)) : tendsto (λ x, ∥f x∥) l (𝓝 ∥a∥) :=
tendsto_norm.comp h

lemma filter.tendsto.nnnorm (h : tendsto f l (𝓝 a)) :
  tendsto (λ x, ∥f x∥₊) l (𝓝 (∥a∥₊)) :=
tendsto.comp continuous_nnnorm.continuous_at h

end

section

variables [topological_space α] {f : α → E} {s : set α} {a : α} {b : E}

lemma continuous.norm (h : continuous f) : continuous (λ x, ∥f x∥) := continuous_norm.comp h

lemma continuous.nnnorm (h : continuous f) : continuous (λ x, ∥f x∥₊) :=
continuous_nnnorm.comp h

lemma continuous_at.norm (h : continuous_at f a) : continuous_at (λ x, ∥f x∥) a := h.norm

lemma continuous_at.nnnorm (h : continuous_at f a) : continuous_at (λ x, ∥f x∥₊) a := h.nnnorm

lemma continuous_within_at.norm (h : continuous_within_at f s a) :
  continuous_within_at (λ x, ∥f x∥) s a :=
h.norm

lemma continuous_within_at.nnnorm (h : continuous_within_at f s a) :
  continuous_within_at (λ x, ∥f x∥₊) s a :=
h.nnnorm

lemma continuous_on.norm (h : continuous_on f s) : continuous_on (λ x, ∥f x∥) s :=
λ x hx, (h x hx).norm

lemma continuous_on.nnnorm (h : continuous_on f s) : continuous_on (λ x, ∥f x∥₊) s :=
λ x hx, (h x hx).nnnorm

end

/-- If `∥y∥→∞`, then we can assume `y≠x` for any fixed `x`. -/
lemma eventually_ne_of_tendsto_norm_at_top {l : filter α} {f : α → E}
  (h : tendsto (λ y, ∥f y∥) l at_top) (x : E) :
  ∀ᶠ y in l, f y ≠ x :=
begin
  have : ∀ᶠ y in l, 1 + ∥x∥ ≤ ∥f y∥ := h (mem_at_top (1 + ∥x∥)),
  refine this.mono (λ y hy hxy, _),
  subst x,
  exact not_le_of_lt zero_lt_one (add_le_iff_nonpos_left.1 hy)
end

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_group.has_lipschitz_add : has_lipschitz_add E :=
{ lipschitz_add := ⟨2, lipschitz_with.prod_fst.add lipschitz_with.prod_snd⟩ }

/-- A seminormed group is a uniform additive group, i.e., addition and subtraction are uniformly
continuous. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_uniform_group : uniform_add_group E :=
⟨(lipschitz_with.prod_fst.sub lipschitz_with.prod_snd).uniform_continuous⟩

@[priority 100] -- see Note [lower instance priority]
instance normed_top_group : topological_add_group E :=
by apply_instance -- short-circuit type class inference

lemma nat.norm_cast_le [has_one E] : ∀ n : ℕ, ∥(n : E)∥ ≤ n * ∥(1 : E)∥
| 0 := by simp
| (n + 1) := by { rw [n.cast_succ, n.cast_succ, add_mul, one_mul],
                  exact norm_add_le_of_le (nat.norm_cast_le n) le_rfl }

lemma semi_normed_group.mem_closure_iff {s : set E} {x : E} :
  x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, ∥x - y∥ < ε :=
by simp [metric.mem_closure_iff, dist_eq_norm]

lemma norm_le_zero_iff' [separated_space E] {g : E} :
  ∥g∥ ≤ 0 ↔ g = 0 :=
begin
  letI : normed_group E := { to_metric_space := of_t2_pseudo_metric_space ‹_›,
    .. ‹semi_normed_group E› },
  rw [← dist_zero_right], exact dist_le_zero
end

lemma norm_eq_zero_iff' [separated_space E] {g : E} : ∥g∥ = 0 ↔ g = 0 :=
(norm_nonneg g).le_iff_eq.symm.trans norm_le_zero_iff'

lemma norm_pos_iff' [separated_space E] {g : E} : 0 < ∥g∥ ↔ g ≠ 0 :=
by rw [← not_le, norm_le_zero_iff']

lemma cauchy_seq_sum_of_eventually_eq {u v : ℕ → E} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
  (hv : cauchy_seq (λ n, ∑ k in range (n+1), v k)) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  let d : ℕ → E := λ n, ∑ k in range (n + 1), (u k - v k),
  rw show (λ n, ∑ k in range (n + 1), u k) = d + (λ n, ∑ k in range (n + 1), v k),
    by { ext n, simp [d] },
  have : ∀ n ≥ N, d n = d N,
  { intros n hn,
    dsimp [d],
    rw eventually_constant_sum _ hn,
    intros m hm,
    simp [huv m hm] },
  exact (tendsto_at_top_of_eventually_const this).cauchy_seq.add hv
end

end semi_normed_group

section normed_group

/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist [has_norm E] [add_comm_group E] [metric_space E]
  (H1 : ∀ x : E, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : E, dist x y ≤ dist (x + z) (y + z)) : normed_group E :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 },
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this }
  end }

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure normed_group.core (E : Type*) [add_comm_group E] [has_norm E] : Prop :=
(norm_eq_zero_iff : ∀ x : E, ∥x∥ = 0 ↔ x = 0)
(triangle : ∀ x y : E, ∥x + y∥ ≤ ∥x∥ + ∥y∥)
(norm_neg : ∀ x : E, ∥-x∥ = ∥x∥)

/-- The `semi_normed_group.core` induced by a `normed_group.core`. -/
lemma normed_group.core.to_semi_normed_group.core {E : Type*} [add_comm_group E] [has_norm E]
  (C : normed_group.core E) : semi_normed_group.core E :=
{ norm_zero := (C.norm_eq_zero_iff 0).2 rfl,
  triangle := C.triangle,
  norm_neg := C.norm_neg }

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
def normed_group.of_core (E : Type*) [add_comm_group E] [has_norm E]
  (C : normed_group.core E) : normed_group E :=
{ eq_of_dist_eq_zero := λ x y h,
  begin
    rw [dist_eq_norm] at h,
    exact sub_eq_zero.mp ((C.norm_eq_zero_iff _).1 h)
  end
  ..semi_normed_group.of_core E (normed_group.core.to_semi_normed_group.core C) }

variables [normed_group E] [normed_group F]

@[simp] lemma norm_eq_zero {g : E} : ∥g∥ = 0 ↔ g = 0 := norm_eq_zero_iff'

@[simp] lemma norm_pos_iff {g : E} : 0 < ∥ g ∥ ↔ g ≠ 0 := norm_pos_iff'

@[simp] lemma norm_le_zero_iff {g : E} : ∥g∥ ≤ 0 ↔ g = 0 := norm_le_zero_iff'

lemma norm_sub_eq_zero_iff {u v : E} : ∥u - v∥ = 0 ↔ u = v :=
by rw [norm_eq_zero, sub_eq_zero]

lemma eq_of_norm_sub_le_zero {g h : E} (a : ∥g - h∥ ≤ 0) : g = h :=
by rwa [← sub_eq_zero, ← norm_le_zero_iff]

lemma eq_of_norm_sub_eq_zero {u v : E} (h : ∥u - v∥ = 0) : u = v :=
norm_sub_eq_zero_iff.1 h

@[simp] lemma nnnorm_eq_zero {a : E} : ∥a∥₊ = 0 ↔ a = 0 :=
by rw [← nnreal.coe_eq_zero, coe_nnnorm, norm_eq_zero]

/-- An injective group homomorphism from an `add_comm_group` to a `normed_group` induces a
`normed_group` structure on the domain.

See note [reducible non-instances]. -/
@[reducible]
def normed_group.induced {E} [add_comm_group E]
  (f : E →+ F) (h : function.injective f) : normed_group E :=
{ .. semi_normed_group.induced f,
  .. metric_space.induced f h normed_group.to_metric_space, }

/-- A subgroup of a normed group is also a normed group, with the restriction of the norm. -/
instance add_subgroup.normed_group (s : add_subgroup E) : normed_group s :=
normed_group.induced s.subtype subtype.coe_injective

/-- A submodule of a normed group is also a normed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance submodule.normed_group {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [normed_group E] {_ : module 𝕜 E} (s : submodule 𝕜 E) : normed_group s :=
{ ..submodule.semi_normed_group s }

/-- normed group instance on the product of two normed groups, using the sup norm. -/
noncomputable instance prod.normed_group : normed_group (E × F) := { ..prod.semi_normed_group }

lemma prod.norm_def (x : E × F) : ∥x∥ = (max ∥x.1∥ ∥x.2∥) := rfl

lemma prod.nnnorm_def (x : E × F) : ∥x∥₊ = max (∥x.1∥₊) (∥x.2∥₊) :=
by { have := x.norm_def, simp only [← coe_nnnorm] at this, exact_mod_cast this }

lemma norm_fst_le (x : E × F) : ∥x.1∥ ≤ ∥x∥ :=
le_max_left _ _

lemma norm_snd_le (x : E × F) : ∥x.2∥ ≤ ∥x∥ :=
le_max_right _ _

lemma norm_prod_le_iff {x : E × F} {r : ℝ} :
  ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
max_le_iff

/-- normed group instance on the product of finitely many normed groups, using the sup norm. -/
noncomputable instance pi.normed_group {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] :
  normed_group (Πi, π i) := { ..pi.semi_normed_group }

/-- The norm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
lemma pi_norm_le_iff {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] {r : ℝ} (hr : 0 ≤ r)
  {x : Πi, π i} : ∥x∥ ≤ r ↔ ∀i, ∥x i∥ ≤ r :=
by simp only [← dist_zero_right, dist_pi_le_iff hr, pi.zero_apply]

/-- The norm of an element in a product space is `< r` if and only if the norm of each
component is. -/
lemma pi_norm_lt_iff {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] {r : ℝ} (hr : 0 < r)
  {x : Πi, π i} : ∥x∥ < r ↔ ∀i, ∥x i∥ < r :=
by simp only [← dist_zero_right, dist_pi_lt_iff hr, pi.zero_apply]

lemma norm_le_pi_norm {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] (x : Πi, π i) (i : ι) :
  ∥x i∥ ≤ ∥x∥ :=
(pi_norm_le_iff (norm_nonneg x)).1 (le_refl _) i

@[simp] lemma pi_norm_const [nonempty ι] [fintype ι] (a : E) : ∥(λ i : ι, a)∥ = ∥a∥ :=
by simpa only [← dist_zero_right] using dist_pi_const a 0

@[simp] lemma pi_nnnorm_const [nonempty ι] [fintype ι] (a : E) :
  ∥(λ i : ι, a)∥₊ = ∥a∥₊ :=
nnreal.eq $ pi_norm_const a

lemma tendsto_norm_nhds_within_zero : tendsto (norm : E → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
(continuous_norm.tendsto' (0 : E) 0 norm_zero).inf $ tendsto_principal_principal.2 $
  λ x, norm_pos_iff.2

end normed_group
