/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.add_torsor
import topology.metric_space.isometry

noncomputable theory

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.

-/

universes u v

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A `normed_add_torsor V P` is a torsor of an additive normed group
action by a `normed_group V` on points `P`. We bundle the metric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a metric space, but
bundling just the distance and using an instance for the metric space
results in type class problems). -/
class normed_add_torsor (V : out_param $ Type u) (P : Type v)
  [out_param $ normed_group V] [metric_space P]
  extends add_torsor V P :=
(dist_eq_norm' : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)
end prio

variables (V : Type u) {P : Type v} [normed_group V] [metric_space P] [normed_add_torsor V P]
include V

/-- The distance equals the norm of subtracting two points. This lemma
is needed to make V an explicit rather than implicit argument. -/
lemma dist_eq_norm_vsub (x y : P) :
  dist x y = ∥(x -ᵥ y)∥ :=
normed_add_torsor.dist_eq_norm' x y

variable {V}

@[simp] lemma dist_vadd_cancel_left (v : V) (x y : P) :
  dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
by rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, vadd_vsub_vadd_cancel_left]

@[simp] lemma dist_vadd_cancel_right (v₁ v₂ : V) (x : P) :
  dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ :=
by rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]

/-- A `normed_group` is a `normed_add_torsor` over itself. -/
@[nolint instance_priority] -- false positive
instance normed_group.normed_add_torsor (V : Type u) [normed_group V] :
  normed_add_torsor V V :=
{ dist_eq_norm' := dist_eq_norm }

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metric_space_of_normed_group_of_add_torsor (V : Type u) (P : Type v) [normed_group V]
    [add_torsor V P] : metric_space P :=
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

namespace isometric

/-- The map `v ↦ v +ᵥ p` as an isometric equivalence between `V` and `P`. -/
def vadd_const (p : P) : V ≃ᵢ P :=
⟨equiv.vadd_const V p, isometry_emetric_iff_metric.2 $ λ x₁ x₂, dist_vadd_cancel_right x₁ x₂ p⟩

@[simp] lemma coe_vadd_const (p : P) : ⇑(vadd_const p) = λ v, v +ᵥ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : ⇑(vadd_const p).symm = λ p', p' -ᵥ p := rfl

@[simp] lemma vadd_const_to_equiv (p : P) : (vadd_const p).to_equiv = equiv.vadd_const V p := rfl

variables (P)

/-- The map `p ↦ v +ᵥ p` as an isometric automorphism of `P`. -/
def const_vadd (v : V) : P ≃ᵢ P :=
⟨equiv.const_vadd P v, isometry_emetric_iff_metric.2 $ dist_vadd_cancel_left v⟩

@[simp] lemma coe_const_vadd (v : V) : ⇑(const_vadd P v) = (+ᵥ) v := rfl

variable (V)

@[simp] lemma const_vadd_zero : const_vadd P (0:V) = isometric.refl P :=
isometric.to_equiv_inj $ equiv.const_vadd_zero V P

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
