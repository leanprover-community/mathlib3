/-
Copyright (c) 2022 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import analysis.inner_product_space.adjoint

/-!

# Proper cones

We define a proper cone as a nonempty, closed, convex cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once have the definitions of conic programs and
linear programs, the results from this file can be used to prove duality theorems.

## TODO

The next steps are:
- Prove the cone version of Farkas' lemma (2.3.4 in the reference).
- Define the positive cone as a proper cone.
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open continuous_linear_map filter

namespace convex_cone

variables {E : Type*} [add_comm_monoid E] [has_smul ℝ E] [topological_space E]
  [has_continuous_const_smul ℝ E] [has_continuous_add E]

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : convex_cone ℝ E) : convex_cone ℝ E :=
{ carrier := closure ↑K,
  smul_mem' :=
    λ c hc _ h₁, map_mem_closure (continuous_id'.const_smul c) h₁ (λ _ h₂, K.smul_mem hc h₂),
  add_mem' := λ _ h₁ _ h₂, map_mem_closure₂ continuous_add h₁ h₂ K.add_mem }

@[simp, norm_cast] lemma coe_closure (K : convex_cone ℝ E) : (K.closure : set E) = closure K := rfl

@[simp] protected lemma mem_closure {K : convex_cone ℝ E} {a : E} :
  a ∈ K.closure ↔ a ∈ closure (K : set E) := iff.rfl

lemma closure_eq_iff_is_closed {K : convex_cone ℝ E} : K.closure = K ↔ is_closed (K : set E) :=
⟨ (λ h, by rw [← closure_eq_iff_is_closed, ← coe_closure, h]),
  (λ h, set_like.coe_injective $ closure_eq_iff_is_closed.2 h) ⟩

end convex_cone

section definitions

/-- A proper cone is a convex cone `K` that is nonempty and closed. Proper cones have the nice
property that the dual of the dual of a proper cone is itself. This makes them useful for defining
cone programs and proving duality theorems. -/
structure proper_cone (E : Type*) [normed_add_comm_group E] [inner_product_space ℝ E]
  extends convex_cone ℝ E :=
(nonempty'  : (carrier : set E).nonempty)
(is_closed' : is_closed (carrier : set E))

end definitions

namespace proper_cone

section inner_product_space

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]
variables {F : Type*} [normed_add_comm_group F] [inner_product_space ℝ F]

instance : has_coe (proper_cone E) (convex_cone ℝ E) := ⟨λ K, K.1⟩

@[simp] lemma to_convex_cone_eq_coe (K : proper_cone E) : K.to_convex_cone = K := rfl

noncomputable instance : has_zero (proper_cone E) :=
⟨ { to_convex_cone := (0 : convex_cone ℝ E),
    nonempty' := ⟨0, rfl⟩,
    is_closed' := is_closed_singleton } ⟩

noncomputable instance : inhabited (proper_cone E) := ⟨0⟩

lemma ext' : function.injective (coe : proper_cone E → convex_cone ℝ E) :=
λ S T h, by cases S; cases T; congr'

instance : set_like (proper_cone E) E :=
{ coe := λ K, K.carrier,
  coe_injective' := λ _ _ h, proper_cone.ext' (set_like.coe_injective h) }

@[ext] lemma ext {S T : proper_cone E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

@[simp] lemma mem_coe {x : E} {K : proper_cone E} : x ∈ (K : convex_cone ℝ E) ↔ x ∈ K := iff.rfl

protected lemma nonempty (K : proper_cone E) : (K : set E).nonempty := K.nonempty'

protected lemma is_closed (K : proper_cone E) : is_closed (K : set E) := K.is_closed'

protected lemma pointed (K : proper_cone E) : (K : convex_cone ℝ E).pointed :=
(K : convex_cone ℝ E).pointed_of_nonempty_of_is_closed K.nonempty K.is_closed

-- TODO: Replace map with a bundled version: proper_cone E →L[ℝ] proper_cone F
/-- The closure of image of a proper cone under a continuous `ℝ`-linear map is a proper cone. We
use continuous maps here so that the adjoint of f is also a map between proper cones. -/
noncomputable def map (f : E →L[ℝ] F) (K : proper_cone E) : proper_cone F :=
{ to_convex_cone := convex_cone.closure (convex_cone.map (f : E →ₗ[ℝ] F) ↑K),
  nonempty' := ⟨ 0, subset_closure $ set_like.mem_coe.2 $ convex_cone.mem_map.2
    ⟨0, K.pointed, map_zero _⟩ ⟩,
  is_closed' := is_closed_closure }

@[simp, norm_cast] lemma coe_map (f : E →L[ℝ] F) (K : proper_cone E) :
  ↑(K.map f) = (convex_cone.map (f : E →ₗ[ℝ] F) ↑K).closure := rfl

@[simp] lemma mem_map {f : E →L[ℝ] F} {K : proper_cone E} {y : F} :
  y ∈ K.map f ↔ y ∈ (convex_cone.map (f : E →ₗ[ℝ] F) ↑K).closure := iff.rfl

@[simp] lemma map_id (K : proper_cone E) : K.map (continuous_linear_map.id ℝ E) = K :=
proper_cone.ext' $ by simpa using convex_cone.closure_eq_iff_is_closed.2 K.is_closed

/-- The inner dual cone of a proper cone is a proper cone. -/
def dual (K : proper_cone E): (proper_cone E) :=
{ to_convex_cone := (K : set E).inner_dual_cone,
  nonempty' := ⟨0, pointed_inner_dual_cone _⟩,
  is_closed' := is_closed_inner_dual_cone _ }

@[simp, norm_cast]
lemma coe_dual (K : proper_cone E) : ↑(dual K) = (K : set E).inner_dual_cone := rfl

@[simp] lemma mem_dual {K : proper_cone E} {y : E} :
  y ∈ dual K ↔ ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ :=
by {rw [← mem_coe, coe_dual, mem_inner_dual_cone _ _], refl}

-- TODO: add comap, adjoint

end inner_product_space

section complete_space

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] [complete_space E]

/-- The dual of the dual of a proper cone is itself. -/
theorem dual_dual (K : proper_cone E) : K.dual.dual = K := proper_cone.ext' $
  (K : convex_cone ℝ E).inner_dual_cone_of_inner_dual_cone_eq_self K.nonempty K.is_closed

end complete_space

end proper_cone
