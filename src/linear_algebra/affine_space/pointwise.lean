/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import linear_algebra.affine_space.affine_subspace


/-! # Pointwise instances on `affine_subspace`s

This file provides the additive action `affine_subspace.pointwise_add_action` in the
`pointwise` locale.

-/

open_locale affine pointwise

open set

namespace affine_subspace

variables {k : Type*} [ring k]
variables {V P V₁ P₁ V₂ P₂ : Type*}

variables [add_comm_group V] [module k V] [affine_space V P]
variables [add_comm_group V₁] [module k V₁] [add_torsor V₁ P₁]
variables [add_comm_group V₂] [module k V₂] [add_torsor V₂ P₂]

include V

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_add_action : add_action V (affine_subspace k P) :=
{ vadd := λ x S, S.map (affine_equiv.const_vadd k P x),
  zero_vadd := λ p,
    (congr_arg (λ f, p.map f) $ affine_map.ext $ by exact zero_vadd _).trans (p.map_id),
  add_vadd := λ x y p,
    (congr_arg (λ f, p.map f) $ affine_map.ext $ by exact add_vadd _ _).trans (p.map_map _ _).symm }

localized "attribute [instance] affine_subspace.pointwise_add_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_vadd (v : V) (s : affine_subspace k P) :
  ((v +ᵥ s : affine_subspace k P) : set P) = v +ᵥ s := rfl

lemma vadd_mem_pointwise_vadd_iff {v : V} {s : affine_subspace k P} {p : P} :
  v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
vadd_mem_vadd_set_iff

lemma pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : affine_subspace k P) = ⊥ :=
by { ext, simp, }

lemma pointwise_vadd_direction (v : V) (s : affine_subspace k P) :
  (v +ᵥ s).direction = s.direction :=
begin
  unfold has_vadd.vadd,
  rw map_direction,
  exact submodule.map_id _,
end

lemma pointwise_vadd_span (v : V) (s : set P) :
  v +ᵥ affine_span k s = affine_span k (v +ᵥ s) :=
map_span _ s

omit V
include V₁ V₂

lemma map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : affine_subspace k P₁) :
  (v +ᵥ s).map f = f.linear v +ᵥ s.map f :=
begin
  unfold has_vadd.vadd,
  rw [map_map, map_map],
  congr' 1,
  ext,
  exact f.map_vadd _ _,
end

end affine_subspace
