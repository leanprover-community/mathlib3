/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import analysis.normed.group.basic
import linear_algebra.affine_space.affine_subspace
import linear_algebra.affine_space.midpoint

/-!
# Torsors of additive normed group actions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.
-/

noncomputable theory
open_locale nnreal topology
open filter

/-- A `normed_add_torsor V P` is a torsor of an additive seminormed group
action by a `seminormed_add_comm_group V` on points `P`. We bundle the pseudometric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems). -/
class normed_add_torsor (V : out_param $ Type*) (P : Type*)
  [out_param $ seminormed_add_comm_group V] [pseudo_metric_space P]
  extends add_torsor V P :=
(dist_eq_norm' : ∀ (x y : P), dist x y = ‖(x -ᵥ y : V)‖)

/-- Shortcut instance to help typeclass inference out. -/
@[priority 100]
instance normed_add_torsor.to_add_torsor' {V P : Type*} [normed_add_comm_group V] [metric_space P]
  [normed_add_torsor V P] : add_torsor V P := normed_add_torsor.to_add_torsor

variables {α V P W Q : Type*} [seminormed_add_comm_group V] [pseudo_metric_space P]
  [normed_add_torsor V P] [normed_add_comm_group W] [metric_space Q] [normed_add_torsor W Q]

@[priority 100]
instance normed_add_torsor.to_has_isometric_vadd : has_isometric_vadd V P :=
⟨λ c, isometry.of_dist_eq $ λ x y, by simp [normed_add_torsor.dist_eq_norm']⟩

/-- A `seminormed_add_comm_group` is a `normed_add_torsor` over itself. -/
@[priority 100]
instance seminormed_add_comm_group.to_normed_add_torsor : normed_add_torsor V V :=
{ dist_eq_norm' := dist_eq_norm }

/-- A nonempty affine subspace of a `normed_add_torsor` is itself a `normed_add_torsor`. -/
@[nolint fails_quickly] -- Because of the add_torsor.nonempty instance.
instance affine_subspace.to_normed_add_torsor {R : Type*} [ring R] [module R V]
  (s : affine_subspace R P) [nonempty s] : normed_add_torsor s.direction s :=
{ dist_eq_norm' := λ x y, normed_add_torsor.dist_eq_norm' ↑x ↑y,
  ..affine_subspace.to_add_torsor s }

include V

section

variables (V W)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
lemma dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖ := normed_add_torsor.dist_eq_norm' x y

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub'` sometimes doesn't work. -/
lemma dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖ :=
(dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)

end

lemma dist_vadd_cancel_left (v : V) (x y : P) :
  dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
dist_vadd _ _ _

@[simp] lemma dist_vadd_cancel_right (v₁ v₂ : V) (x : P) :
  dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ :=
by rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]

@[simp] lemma dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖ :=
by simp [dist_eq_norm_vsub V _ x]

@[simp] lemma dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖ :=
by rw [dist_comm, dist_vadd_left]

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
addition/subtraction of `x : P`. -/
@[simps] def isometry_equiv.vadd_const (x : P) : V ≃ᵢ P :=
{ to_equiv := equiv.vadd_const x,
  isometry_to_fun := isometry.of_dist_eq $ λ _ _, dist_vadd_cancel_right _ _ _ }

@[simp] lemma dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z :=
by rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
subtraction from `x : P`. -/
@[simps] def isometry_equiv.const_vsub (x : P) : P ≃ᵢ V :=
{ to_equiv := equiv.const_vsub x,
  isometry_to_fun := isometry.of_dist_eq $ λ y z, dist_vsub_cancel_left _ _ _ }

@[simp] lemma dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
(isometry_equiv.vadd_const z).symm.dist_eq x y

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
def pseudo_metric_space_of_normed_add_comm_group_of_add_torsor (V P : Type*)
  [seminormed_add_comm_group V] [add_torsor V P] : pseudo_metric_space P :=
{ dist := λ x y, ‖(x -ᵥ y : V)‖,
  dist_self := λ x, by simp,
  dist_comm := λ x y, by simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
  dist_triangle := begin
    intros x y z,
    change ‖x -ᵥ z‖ ≤ ‖x -ᵥ y‖ + ‖y -ᵥ z‖,
    rw ←vsub_add_vsub_cancel,
    apply norm_add_le
  end }

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metric_space_of_normed_add_comm_group_of_add_torsor (V P : Type*)
  [normed_add_comm_group V] [add_torsor V P] :
  metric_space P :=
{ dist := λ x y, ‖(x -ᵥ y : V)‖,
  dist_self := λ x, by simp,
  eq_of_dist_eq_zero := λ x y h, by simpa using h,
  dist_comm := λ x y, by simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
  dist_triangle := begin
    intros x y z,
    change ‖x -ᵥ z‖ ≤ ‖x -ᵥ y‖ + ‖y -ᵥ z‖,
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

@[priority 100] instance normed_add_torsor.to_has_continuous_vadd : has_continuous_vadd V P :=
{ continuous_vadd := uniform_continuous_vadd.continuous }

lemma continuous_vsub : continuous (λ x : P × P, x.1 -ᵥ x.2) :=
uniform_continuous_vsub.continuous

lemma filter.tendsto.vsub {l : filter α} {f g : α → P} {x y : P}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
(continuous_vsub.tendsto (x, y)).comp (hf.prod_mk_nhds hg)

section

variables [topological_space α]

lemma continuous.vsub {f g : α → P} (hf : continuous f) (hg : continuous g) :
  continuous (f -ᵥ g) :=
continuous_vsub.comp (hf.prod_mk hg : _)

lemma continuous_at.vsub {f g : α → P}  {x : α} (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (f -ᵥ g) x :=
hf.vsub hg

lemma continuous_within_at.vsub {f g : α → P} {x : α} {s : set α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (f -ᵥ g) s x :=
hf.vsub hg

end

section

variables {R : Type*} [ring R] [topological_space R] [module R V] [has_continuous_smul R V]

lemma filter.tendsto.line_map {l : filter α} {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (h₂ : tendsto f₂ l (𝓝 p₂)) (hg : tendsto g l (𝓝 c)) :
  tendsto (λ x, affine_map.line_map (f₁ x) (f₂ x) (g x)) l (𝓝 $ affine_map.line_map p₁ p₂ c) :=
(hg.smul (h₂.vsub h₁)).vadd h₁

lemma filter.tendsto.midpoint [invertible (2:R)] {l : filter α} {f₁ f₂ : α → P} {p₁ p₂ : P}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (h₂ : tendsto f₂ l (𝓝 p₂)) :
  tendsto (λ x, midpoint R (f₁ x) (f₂ x)) l (𝓝 $ midpoint R p₁ p₂) :=
h₁.line_map h₂ tendsto_const_nhds

end
