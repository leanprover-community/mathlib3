/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.affine_space.affine_map
import topology.continuous_function.basic
import topology.algebra.module.basic

/-!
# Continuous affine maps.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a type of bundled continuous affine maps.

Note that the definition and basic properties established here require minimal assumptions, and do
not even assume compatibility between the topological and algebraic structures. Of course it is
necessary to assume some compatibility in order to obtain a useful theory. Such a theory is
developed elsewhere for affine spaces modelled on _normed_ vector spaces, but not yet for general
topological affine spaces (since we have not defined these yet).

## Main definitions:

 * `continuous_affine_map`

## Notation:

We introduce the notation `P →A[R] Q` for `continuous_affine_map R P Q`. Note that this is parallel
to the notation `E →L[R] F` for `continuous_linear_map R E F`.
-/

/-- A continuous map of affine spaces. -/
structure continuous_affine_map (R : Type*) {V W : Type*} (P Q : Type*) [ring R]
  [add_comm_group V] [module R V] [topological_space P] [add_torsor V P]
  [add_comm_group W] [module R W] [topological_space Q] [add_torsor W Q]
  extends P →ᵃ[R] Q :=
(cont : continuous to_fun)

notation P ` →A[`:25 R `] ` Q := continuous_affine_map R P Q

namespace continuous_affine_map

variables {R V W P Q : Type*} [ring R]
variables [add_comm_group V] [module R V] [topological_space P] [add_torsor V P]
variables [add_comm_group W] [module R W] [topological_space Q] [add_torsor W Q]

include V W

instance : has_coe (P →A[R] Q) (P →ᵃ[R] Q) :=
⟨to_affine_map⟩

lemma to_affine_map_injective {f g : P →A[R] Q} (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) : f = g :=
by { cases f, cases g, congr' }

instance : continuous_map_class (P →A[R] Q) P Q :=
{ coe := λ f, f.to_affine_map,
  coe_injective' := λ f g h, to_affine_map_injective $ fun_like.coe_injective h,
  map_continuous := cont }

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (P →A[R] Q) (λ _, P → Q) := fun_like.has_coe_to_fun

lemma to_fun_eq_coe (f : P →A[R] Q) : f.to_fun = ⇑f := rfl

lemma coe_injective : @function.injective (P →A[R] Q) (P → Q) coe_fn :=
fun_like.coe_injective

@[ext] lemma ext {f g : P →A[R] Q} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext _ _ h

lemma ext_iff {f g : P →A[R] Q} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

lemma congr_fun {f g : P →A[R] Q} (h : f = g) (x : P) : f x = g x :=
fun_like.congr_fun h _

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
def to_continuous_map (f : P →A[R] Q) : C(P, Q) :=
⟨f, f.cont⟩

instance : has_coe (P →A[R] Q) (C(P, Q)) :=
⟨to_continuous_map⟩

@[simp] lemma to_affine_map_eq_coe (f : P →A[R] Q) :
  f.to_affine_map = ↑f :=
rfl

@[simp] lemma to_continuous_map_coe (f : P →A[R] Q) : f.to_continuous_map = ↑f :=
rfl

@[simp, norm_cast] lemma coe_to_affine_map (f : P →A[R] Q) :
  ((f : P →ᵃ[R] Q) : P → Q) = f :=
rfl

@[simp, norm_cast] lemma coe_to_continuous_map (f : P →A[R] Q) :
  ((f : C(P, Q)) : P → Q) = f :=
rfl

lemma to_continuous_map_injective {f g : P →A[R] Q}
  (h : (f : C(P, Q)) = (g : C(P, Q))) : f = g :=
by { ext a, exact continuous_map.congr_fun h a, }

@[norm_cast] lemma coe_affine_map_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : P →ᵃ[R] Q) = f :=
rfl

@[norm_cast] lemma coe_continuous_map_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : C(P, Q)) = ⟨f, h⟩ :=
rfl

@[simp] lemma coe_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : P → Q) = f :=
rfl

@[simp] lemma mk_coe (f : P →A[R] Q) (h) :
  (⟨(f : P →ᵃ[R] Q), h⟩ : P →A[R] Q) = f :=
by { ext, refl, }

@[continuity]
protected lemma continuous (f : P →A[R] Q) : continuous f := f.2

variables (R P)

/-- The constant map is a continuous affine map. -/
def const (q : Q) : P →A[R] Q :=
{ to_fun := affine_map.const R P q,
  cont   := continuous_const,
  .. affine_map.const R P q, }

@[simp] lemma coe_const (q : Q) : (const R P q : P → Q) = function.const P q := rfl

noncomputable instance : inhabited (P →A[R] Q) :=
⟨const R P $ nonempty.some (by apply_instance : nonempty Q)⟩

variables {R P} {W₂ Q₂ : Type*}
variables [add_comm_group W₂] [module R W₂] [topological_space Q₂] [add_torsor W₂ Q₂]

include W₂

/-- The composition of morphisms is a morphism. -/
def comp (f : Q →A[R] Q₂) (g : P →A[R] Q) : P →A[R] Q₂ :=
{ cont := f.cont.comp g.cont,
  .. (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q), }

@[simp, norm_cast] lemma coe_comp (f : Q →A[R] Q₂) (g : P →A[R] Q) :
  (f.comp g : P → Q₂) = (f : Q → Q₂) ∘ (g : P → Q) :=
rfl

lemma comp_apply (f : Q →A[R] Q₂) (g : P →A[R] Q) (x : P) :
  f.comp g x = f (g x) :=
rfl

omit W₂

section module_valued_maps

variables {S : Type*}
variables [topological_space W]

instance : has_zero (P →A[R] W) := ⟨continuous_affine_map.const R P 0⟩

@[norm_cast, simp] lemma coe_zero : ((0 : P →A[R] W) : P → W) = 0 := rfl

lemma zero_apply (x : P) : (0 : P →A[R] W) x = 0 := rfl

section mul_action
variables [monoid S] [distrib_mul_action S W] [smul_comm_class R S W]
variables [has_continuous_const_smul S W]

instance : has_smul S (P →A[R] W) :=
{ smul := λ t f, { cont := f.continuous.const_smul t, .. (t • (f : P →ᵃ[R] W)) } }

@[norm_cast, simp] lemma coe_smul (t : S) (f : P →A[R] W) : ⇑(t • f) = t • f := rfl

lemma smul_apply (t : S) (f : P →A[R] W) (x : P) : (t • f) x = t • (f x) := rfl

instance [distrib_mul_action Sᵐᵒᵖ W] [is_central_scalar S W] : is_central_scalar S (P →A[R] W) :=
{ op_smul_eq_smul := λ t f, ext $ λ _, op_smul_eq_smul _ _ }

instance : mul_action S (P →A[R] W) :=
function.injective.mul_action _ coe_injective coe_smul

end mul_action

variables [topological_add_group W]

instance : has_add (P →A[R] W) :=
{ add := λ f g, { cont := f.continuous.add g.continuous, .. ((f : P →ᵃ[R] W) + (g : P →ᵃ[R] W)) }, }

@[norm_cast, simp] lemma coe_add (f g : P →A[R] W) : ⇑(f + g) = f + g := rfl

lemma add_apply (f g : P →A[R] W) (x : P) : (f + g) x = f x + g x := rfl

instance : has_sub (P →A[R] W) :=
{ sub := λ f g, { cont := f.continuous.sub g.continuous, .. ((f : P →ᵃ[R] W) - (g : P →ᵃ[R] W)) }, }

@[norm_cast, simp] lemma coe_sub (f g : P →A[R] W) : ⇑(f - g) = f - g := rfl

lemma sub_apply (f g : P →A[R] W) (x : P) : (f - g) x = f x - g x := rfl

instance : has_neg (P →A[R] W) :=
{ neg := λ f, { cont := f.continuous.neg, .. (-(f : P →ᵃ[R] W)) }, }

@[norm_cast, simp] lemma coe_neg (f : P →A[R] W) : ⇑(-f) = -f := rfl

lemma neg_apply (f : P →A[R] W) (x : P) : (-f) x = -(f x) := rfl

instance : add_comm_group (P →A[R] W) :=
coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub
  (λ _ _, coe_smul _ _) (λ _ _, coe_smul _ _)

instance [monoid S] [distrib_mul_action S W] [smul_comm_class R S W]
  [has_continuous_const_smul S W] :
  distrib_mul_action S (P →A[R] W) :=
function.injective.distrib_mul_action ⟨λ f, f.to_affine_map.to_fun, rfl, coe_add⟩
  coe_injective coe_smul

instance [semiring S] [module S W] [smul_comm_class R S W] [has_continuous_const_smul S W] :
  module S (P →A[R] W) :=
function.injective.module S ⟨λ f, f.to_affine_map.to_fun, rfl, coe_add⟩ coe_injective coe_smul

end module_valued_maps

end continuous_affine_map

namespace continuous_linear_map

variables {R V W : Type*} [ring R]
variables [add_comm_group V] [module R V] [topological_space V]
variables [add_comm_group W] [module R W] [topological_space W]

/-- A continuous linear map can be regarded as a continuous affine map. -/
def to_continuous_affine_map (f : V →L[R] W) : V →A[R] W :=
{ to_fun    := f,
  linear    := f,
  map_vadd' := by simp,
  cont      := f.cont, }

@[simp] lemma coe_to_continuous_affine_map (f : V →L[R] W) :
  ⇑f.to_continuous_affine_map = f :=
rfl

@[simp] lemma to_continuous_affine_map_map_zero (f : V →L[R] W) :
  f.to_continuous_affine_map 0 = 0 :=
by simp

end continuous_linear_map
