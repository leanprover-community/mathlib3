/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import analysis.normed.group.basic
import linear_algebra.affine_space.midpoint
import topology.algebra.affine

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.
-/

noncomputable theory
open_locale nnreal topological_space
open filter

/-- A `normed_add_torsor V P` is a torsor of an additive seminormed group
action by a `semi_normed_group V` on points `P`. We bundle the pseudometric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems). -/
class normed_add_torsor (V : out_param $ Type*) (P : Type*)
  [out_param $ semi_normed_group V] [pseudo_metric_space P]
  extends add_torsor V P :=
(dist_eq_norm' : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)

variables {α V P : Type*} [semi_normed_group V] [pseudo_metric_space P] [normed_add_torsor V P]
variables {W Q : Type*} [normed_group W] [metric_space Q] [normed_add_torsor W Q]

/-- A `semi_normed_group` is a `normed_add_torsor` over itself. -/
@[priority 100]
instance semi_normed_group.to_normed_add_torsor : normed_add_torsor V V :=
{ dist_eq_norm' := dist_eq_norm }

include V

section

variables (V W)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
lemma dist_eq_norm_vsub (x y : P) : dist x y = ∥x -ᵥ y∥ := normed_add_torsor.dist_eq_norm' x y

end

@[simp] lemma dist_vadd_cancel_left (v : V) (x y : P) :
  dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
by rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, vadd_vsub_vadd_cancel_left]

@[simp] lemma dist_vadd_cancel_right (v₁ v₂ : V) (x : P) :
  dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ :=
by rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]

@[simp] lemma dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ∥v∥ :=
by simp [dist_eq_norm_vsub V _ x]

@[simp] lemma dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ∥v∥ :=
by rw [dist_comm, dist_vadd_left]

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
addition/subtraction of `x : P`. -/
@[simps] def isometric.vadd_const (x : P) : V ≃ᵢ P :=
{ to_equiv := equiv.vadd_const x,
  isometry_to_fun := isometry_emetric_iff_metric.2 $ λ _ _, dist_vadd_cancel_right _ _ _ }

section

variable (P)

/-- Self-isometry of a (semi)normed add torsor given by addition of a constant vector `x`. -/
@[simps] def isometric.const_vadd (x : V) : P ≃ᵢ P :=
{ to_equiv := equiv.const_vadd P x,
  isometry_to_fun := isometry_emetric_iff_metric.2 $ λ _ _, dist_vadd_cancel_left _ _ _ }

end

@[simp] lemma dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z :=
by rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
subtraction from `x : P`. -/
@[simps] def isometric.const_vsub (x : P) : P ≃ᵢ V :=
{ to_equiv := equiv.const_vsub x,
  isometry_to_fun := isometry_emetric_iff_metric.2 $ λ y z, dist_vsub_cancel_left _ _ _ }

@[simp] lemma dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
(isometric.vadd_const z).symm.dist_eq x y

section pointwise

open_locale pointwise

@[simp] lemma vadd_ball (x : V) (y : P) (r : ℝ) :
  x +ᵥ metric.ball y r = metric.ball (x +ᵥ y) r :=
(isometric.const_vadd P x).image_ball y r

@[simp] lemma vadd_closed_ball (x : V) (y : P) (r : ℝ) :
  x +ᵥ metric.closed_ball y r = metric.closed_ball (x +ᵥ y) r :=
(isometric.const_vadd P x).image_closed_ball y r

@[simp] lemma vadd_sphere (x : V) (y : P) (r : ℝ) :
  x +ᵥ metric.sphere y r = metric.sphere (x +ᵥ y) r :=
(isometric.const_vadd P x).image_sphere y r

end pointwise

lemma dist_vadd_vadd_le (v v' : V) (p p' : P) :
  dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v' + dist p p' :=
by simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')

lemma dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
  dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃ + dist p₂ p₄ :=
by { rw [dist_eq_norm, vsub_sub_vsub_comm, dist_eq_norm_vsub V, dist_eq_norm_vsub V],
 exact norm_sub_le _ _ }

lemma nndist_vadd_vadd_le (v v' : V) (p p' : P) :
  nndist (v +ᵥ p) (v' +ᵥ p') ≤ nndist v v' + nndist p p' :=
by simp only [← nnreal.coe_le_coe, nnreal.coe_add, ← dist_nndist, dist_vadd_vadd_le]

lemma nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
  nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ nndist p₁ p₃ + nndist p₂ p₄ :=
by simp only [← nnreal.coe_le_coe, nnreal.coe_add, ← dist_nndist, dist_vsub_vsub_le]

lemma edist_vadd_vadd_le (v v' : V) (p p' : P) :
  edist (v +ᵥ p) (v' +ᵥ p') ≤ edist v v' + edist p p' :=
by { simp only [edist_nndist], apply_mod_cast nndist_vadd_vadd_le }

lemma edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
  edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ edist p₁ p₃ + edist p₂ p₄ :=
by { simp only [edist_nndist], apply_mod_cast nndist_vsub_vsub_le }

omit V

/-- The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def pseudo_metric_space_of_normed_group_of_add_torsor (V P : Type*) [semi_normed_group V]
  [add_torsor V P] : pseudo_metric_space P :=
{ dist := λ x y, ∥(x -ᵥ y : V)∥,
  dist_self := λ x, by simp,
  dist_comm := λ x y, by simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
  dist_triangle := begin
    intros x y z,
    change ∥x -ᵥ z∥ ≤ ∥x -ᵥ y∥ + ∥y -ᵥ z∥,
    rw ←vsub_add_vsub_cancel,
    apply norm_add_le
  end }

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metric_space_of_normed_group_of_add_torsor (V P : Type*) [normed_group V] [add_torsor V P] :
  metric_space P :=
{ dist := λ x y, ∥(x -ᵥ y : V)∥,
  dist_self := λ x, by simp,
  eq_of_dist_eq_zero := λ x y h, by simpa using h,
  dist_comm := λ x y, by simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
  dist_triangle := begin
    intros x y z,
    change ∥x -ᵥ z∥ ≤ ∥x -ᵥ y∥ + ∥y -ᵥ z∥,
    rw ←vsub_add_vsub_cancel,
    apply norm_add_le
  end }

include V

lemma lipschitz_with.vadd [pseudo_emetric_space α] {f : α → V} {g : α → P} {Kf Kg : ℝ≥0}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (f +ᵥ g) :=
λ x y,
calc edist (f x +ᵥ g x) (f y +ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_vadd_vadd_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma lipschitz_with.vsub [pseudo_emetric_space α] {f g : α → P} {Kf Kg : ℝ≥0}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (f -ᵥ g) :=
λ x y,
calc edist (f x -ᵥ g x) (f y -ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_vsub_vsub_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma uniform_continuous_vadd : uniform_continuous (λ x : V × P, x.1 +ᵥ x.2) :=
(lipschitz_with.prod_fst.vadd lipschitz_with.prod_snd).uniform_continuous

lemma uniform_continuous_vsub : uniform_continuous (λ x : P × P, x.1 -ᵥ x.2) :=
(lipschitz_with.prod_fst.vsub lipschitz_with.prod_snd).uniform_continuous

@[priority 100] instance normed_add_torsor.to_topological_add_torsor :
  topological_add_torsor V P :=
{ continuous_vadd := uniform_continuous_vadd.continuous,
  continuous_vsub := uniform_continuous_vsub.continuous }
