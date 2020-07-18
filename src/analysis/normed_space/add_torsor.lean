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
class normed_add_torsor (V : Type u) (P : Type v) [normed_group V] [metric_space P]
  extends add_torsor V P :=
(dist_eq_norm' : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)
end prio

/-- The distance equals the norm of subtracting two points. This lemma
is needed to make V an explicit rather than implicit argument. -/
lemma add_torsor.dist_eq_norm (V : Type u) {P : Type v} [normed_group V] [metric_space P]
    [normed_add_torsor V P] (x y : P) :
  dist x y = ∥(x -ᵥ y : V)∥ :=
normed_add_torsor.dist_eq_norm' x y

lemma dist_vadd_cancel_left {V : Type u} {P : Type v} [normed_group V] [metric_space P]
    [normed_add_torsor V P] (v : V) (x y : P) :
  dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
by rw [add_torsor.dist_eq_norm V, add_torsor.dist_eq_norm V, add_torsor.vadd_vsub_vadd_cancel_left]

lemma dist_vadd_cancel_right {V : Type u} {P : Type v} [normed_group V] [metric_space P]
    [normed_add_torsor V P] (v₁ v₂ : V) (x : P) :
  dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ :=
by rw [add_torsor.dist_eq_norm V, dist_eq_norm, add_torsor.vadd_vsub_vadd_cancel_right]

/-- A `normed_group` is a `normed_add_torsor` over itself. -/
instance normed_group.normed_add_torsor (V : Type u) [normed_group V] :
  normed_add_torsor V V :=
{ dist_eq_norm' := dist_eq_norm }

open add_torsor

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metric_space_of_normed_group_of_add_torsor (V : Type u) (P : Type v) [normed_group V]
    [add_torsor V P] : metric_space P :=
{ dist := λ x y, ∥(x -ᵥ y : V)∥,
  dist_self := λ x, by simp,
  eq_of_dist_eq_zero := λ x y h, by simpa using h,
  dist_comm := λ x y, by simp only [←neg_vsub_eq_vsub_rev V y x, norm_neg],
  dist_triangle := begin
    intros x y z,
    change ∥x -ᵥ z∥ ≤ ∥x -ᵥ y∥ + ∥y -ᵥ z∥,
    rw ←vsub_add_vsub_cancel,
    apply norm_add_le
  end }

namespace isometric

variables (V : Type u) {P : Type v} [normed_group V] [metric_space P] [normed_add_torsor V P]

/-- The map `v ↦ v +ᵥ p` as an isometric equivalence between `V` and `P`. -/
def vadd_const (p : P) : V ≃ᵢ P :=
⟨equiv.vadd_const V p, isometry_emetric_iff_metric.2 $ λ x₁ x₂, dist_vadd_cancel_right x₁ x₂ p⟩

@[simp] lemma coe_vadd_const (p : P) : ⇑(vadd_const V p) = λ v, v +ᵥ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : ⇑(vadd_const V p).symm = λ p', p' -ᵥ p := rfl

@[simp] lemma vadd_const_to_equiv (p : P) : (vadd_const V p).to_equiv = equiv.vadd_const V p := rfl

variables {V} (P)

/-- The map `p ↦ v +ᵥ p` as an isometric automorphism of `P`. -/
def const_vadd (v : V) : P ≃ᵢ P :=
⟨equiv.const_vadd P v, isometry_emetric_iff_metric.2 $ dist_vadd_cancel_left v⟩

@[simp] lemma coe_const_vadd (v : V) : ⇑(const_vadd P v) = (+ᵥ) v := rfl

variable (V)

@[simp] lemma const_vadd_zero : const_vadd P (0:V) = isometric.refl P :=
isometric.to_equiv_inj $ equiv.const_vadd_zero V P

end isometric
