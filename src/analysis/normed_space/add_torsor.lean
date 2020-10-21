/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov.
-/
import linear_algebra.affine_space.affine_equiv
import topology.metric_space.isometry

noncomputable theory

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.

-/

/-- A `normed_add_torsor V P` is a torsor of an additive normed group
action by a `normed_group V` on points `P`. We bundle the metric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a metric space, but
bundling just the distance and using an instance for the metric space
results in type class problems). -/
class normed_add_torsor (V : out_param $ Type*) (P : Type*)
  [out_param $ normed_group V] [metric_space P]
  extends add_torsor V P :=
(dist_eq_norm' : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)

variables {V P : Type*} [normed_group V] [metric_space P] [normed_add_torsor V P]
include V

section

variable (V)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
lemma dist_eq_norm_vsub (x y : P) :
  dist x y = ∥(x -ᵥ y)∥ :=
normed_add_torsor.dist_eq_norm' x y

/-- A `normed_group` is a `normed_add_torsor` over itself. -/
@[priority 100]
instance normed_group.normed_add_torsor : normed_add_torsor V V :=
{ dist_eq_norm' := dist_eq_norm }

end

@[simp] lemma dist_vadd_cancel_left (v : V) (x y : P) :
  dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
by rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, vadd_vsub_vadd_cancel_left]

@[simp] lemma dist_vadd_cancel_right (v₁ v₂ : V) (x : P) :
  dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ :=
by rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]

@[simp] lemma dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z :=
by rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]

@[simp] lemma dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
by rw [dist_eq_norm, vsub_sub_vsub_cancel_right, dist_eq_norm_vsub V]

omit V

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

namespace isometric

/-- The map `v ↦ v +ᵥ p` as an isometric equivalence between `V` and `P`. -/
def vadd_const (p : P) : V ≃ᵢ P :=
⟨equiv.vadd_const p, isometry_emetric_iff_metric.2 $ λ x₁ x₂, dist_vadd_cancel_right x₁ x₂ p⟩

@[simp] lemma coe_vadd_const (p : P) : ⇑(vadd_const p) = λ v, v +ᵥ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : ⇑(vadd_const p).symm = λ p', p' -ᵥ p := rfl

@[simp] lemma vadd_const_to_equiv (p : P) : (vadd_const p).to_equiv = equiv.vadd_const p := rfl

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def const_vsub (p : P) : P ≃ᵢ V :=
⟨equiv.const_vsub p, isometry_emetric_iff_metric.2 $ λ p₁ p₂, dist_vsub_cancel_left _ _ _⟩

@[simp] lemma coe_const_vsub (p : P) : ⇑(const_vsub p) = (-ᵥ) p := rfl

@[simp] lemma coe_const_vsub_symm (p : P) : ⇑(const_vsub p).symm = λ v, -v +ᵥ p := rfl

variables (P)

/-- The map `p ↦ v +ᵥ p` as an isometric automorphism of `P`. -/
def const_vadd (v : V) : P ≃ᵢ P :=
⟨equiv.const_vadd P v, isometry_emetric_iff_metric.2 $ dist_vadd_cancel_left v⟩

@[simp] lemma coe_const_vadd (v : V) : ⇑(const_vadd P v) = (+ᵥ) v := rfl

variable (V)

@[simp] lemma const_vadd_zero : const_vadd P (0:V) = isometric.refl P :=
isometric.to_equiv_inj $ equiv.const_vadd_zero V P

variables {P V}

/-- Point reflection in `x` as an `isometric` homeomorphism. -/
def point_reflection (x : P) : P ≃ᵢ P :=
(const_vsub x).trans (vadd_const x)

lemma point_reflection_apply (x y : P) : point_reflection x y = x -ᵥ y +ᵥ x := rfl

@[simp] lemma point_reflection_to_equiv (x : P) :
  (point_reflection x).to_equiv = equiv.point_reflection x := rfl

@[simp] lemma point_reflection_self (x : P) : point_reflection x x = x :=
equiv.point_reflection_self x

lemma point_reflection_involutive (x : P) : function.involutive (point_reflection x : P → P) :=
equiv.point_reflection_involutive x

@[simp] lemma point_reflection_symm (x : P) : (point_reflection x).symm = point_reflection x :=
to_equiv_inj $ equiv.point_reflection_symm x

@[simp] lemma dist_point_reflection_fixed (x y : P) :
  dist (point_reflection x y) x = dist y x :=
by rw [← (point_reflection x).dist_eq y x, point_reflection_self]

lemma dist_point_reflection_self' (x y : P) :
  dist (point_reflection x y) y = ∥bit0 (x -ᵥ y)∥ :=
by rw [point_reflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]

lemma dist_point_reflection_self (𝕜 : Type*) [normed_field 𝕜] [normed_space 𝕜 V] (x y : P) :
  dist (point_reflection x y) y = ∥(2:𝕜)∥ * dist x y :=
by rw [dist_point_reflection_self', ← two_smul' 𝕜 (x -ᵥ y), norm_smul, ← dist_eq_norm_vsub V]

lemma point_reflection_fixed_iff (𝕜 : Type*) [normed_field 𝕜] [normed_space 𝕜 V] [invertible (2:𝕜)]
  {x y : P} :
  point_reflection x y = y ↔ y = x :=
affine_equiv.point_reflection_fixed_iff_of_module 𝕜

lemma dist_point_reflection_self_real [normed_space ℝ V] (x y : P) :
  dist (point_reflection x y) y = 2 * dist x y :=
by { rw [dist_point_reflection_self ℝ, real.norm_two], apply_instance }

end isometric

variables {V' : Type*} {P' : Type*} [normed_group V'] [metric_space P'] [normed_add_torsor V' P']

/-- The map `g` from `V1` to `V2` corresponding to a map `f` from `P1`
to `P2`, at a base point `p`, is an isometry if `f` is one. -/
lemma isometry.vadd_vsub {f : P → P'} (hf : isometry f) {p : P} {g : V → V'}
  (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) : isometry g :=
begin
  convert (isometric.vadd_const (f p)).symm.isometry.comp
    (hf.comp (isometric.vadd_const p).isometry),
  exact funext hg
end
