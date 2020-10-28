/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov.
-/
import algebra.add_torsor
import topology.metric_space.isometry

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.

-/

noncomputable theory
open_locale nnreal topological_space
open filter

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

variables {α V P : Type*} [normed_group V] [metric_space P] [normed_add_torsor V P]
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

variables (P)

/-- The map `p ↦ v +ᵥ p` as an isometric automorphism of `P`. -/
def const_vadd (v : V) : P ≃ᵢ P :=
⟨equiv.const_vadd P v, isometry_emetric_iff_metric.2 $ dist_vadd_cancel_left v⟩

@[simp] lemma coe_const_vadd (v : V) : ⇑(const_vadd P v) = (+ᵥ) v := rfl

variable (V)

@[simp] lemma const_vadd_zero : const_vadd P (0:V) = isometric.refl P :=
isometric.to_equiv_inj $ equiv.const_vadd_zero V P

end isometric

lemma lipschitz_with.vadd [emetric_space α] {f : α → V} {g : α → P} {Kf Kg : ℝ≥0}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (f +ᵥ g) :=
λ x y,
calc edist (f x +ᵥ g x) (f y +ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_vadd_vadd_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma lipschitz_with.vsub [emetric_space α] {f g : α → P} {Kf Kg : ℝ≥0}
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

lemma continuous_vadd : continuous (λ x : V × P, x.1 +ᵥ x.2) :=
uniform_continuous_vadd.continuous

lemma continuous_vsub : continuous (λ x : P × P, x.1 -ᵥ x.2) :=
uniform_continuous_vsub.continuous

lemma filter.tendsto.vadd {l : filter α} {f : α → V} {g : α → P} {v : V} {p : P}
  (hf : tendsto f l (𝓝 v)) (hg : tendsto g l (𝓝 p)) :
  tendsto (f +ᵥ g) l (𝓝 (v +ᵥ p)) :=
(continuous_vadd.tendsto (v, p)).comp (hf.prod_mk_nhds hg)

lemma filter.tendsto.vsub {l : filter α} {f g : α → P} {x y : P}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
(continuous_vsub.tendsto (x, y)).comp (hf.prod_mk_nhds hg)

section

variables [topological_space α]

lemma continuous.vadd {f : α → V} {g : α → P} (hf : continuous f) (hg : continuous g) :
  continuous (f +ᵥ g) :=
continuous_vadd.comp (hf.prod_mk hg)

lemma continuous.vsub {f g : α → P} (hf : continuous f) (hg : continuous g) :
  continuous (f -ᵥ g) :=
continuous_vsub.comp (hf.prod_mk hg)

lemma continuous_at.vadd {f : α → V} {g : α → P} {x : α} (hf : continuous_at f x)
  (hg : continuous_at g x) :
  continuous_at (f +ᵥ g) x :=
hf.vadd hg

lemma continuous_at.vsub {f g : α → P}  {x : α} (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (f -ᵥ g) x :=
hf.vsub hg

lemma continuous_within_at.vadd {f : α → V} {g : α → P} {x : α} {s : set α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (f +ᵥ g) s x :=
hf.vadd hg

lemma continuous_within_at.vsub {f g : α → P} {x : α} {s : set α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (f -ᵥ g) s x :=
hf.vsub hg

end

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
