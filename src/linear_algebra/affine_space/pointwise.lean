/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import linear_algebra.affine_space.affine_subspace


/-! # Pointwise instances on `affine_subspace`s

This file provides:

* `affine_subspace.has_vadd`

and the actions

* `affine_subspace.add_action`

-/


noncomputable theory
open_locale big_operators classical affine pointwise

open set


namespace affine_subspace
variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

instance : has_vadd V (affine_subspace k P) :=
{ vadd := λ x S, S.map (affine_equiv.const_vadd k P x) }

instance : add_action V (affine_subspace k P) :=
{ vadd := (+ᵥ),
  zero_vadd := λ p, by { unfold has_vadd.vadd, simp, },
  add_vadd := λ x y p,
  begin
    unfold has_vadd.vadd,
    ext z,
    simp only [affine_equiv.const_vadd_add, coe_map, affine_equiv.coe_coe,
      affine_equiv.trans_apply, affine_equiv.const_vadd_apply, mem_image, mem_coe,
      image_vadd, set.mem_vadd_set],
    refine ⟨λ h, _, λ h, _⟩,
    { rcases h with ⟨a, ha, rfl⟩,
      refine ⟨y +ᵥ a, ⟨a, ha, rfl⟩, rfl⟩, },
    rcases h with ⟨a, ha, rfl⟩,
    refine ⟨-y +ᵥ a, _, _⟩,
    { rcases ha with ⟨b, hb, rfl⟩,
      rwa [vadd_vadd, add_left_neg, zero_vadd], },
    rw [vadd_vadd, vadd_vadd, add_neg_cancel_right],
  end }

@[simp] lemma coe_const_vadd (v : V) (s : affine_subspace k P) :
  ((v +ᵥ s : affine_subspace k P) : set P) = v +ᵥ s := rfl

lemma mem_const_vadd_iff (v : V) {s : affine_subspace k P} {p : P} :
  v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
vadd_mem_vadd_set_iff

lemma const_vadd_empty {v : V} :
  v +ᵥ (⊥ : affine_subspace k P)  = ⊥ :=
by { ext, simp, }

lemma mem_const_vadd_direction (v x : V) {s : affine_subspace k P} :
  x ∈ s.direction → x ∈ (v +ᵥ s).direction :=
begin
  by_cases hem : set.nonempty (s : set P),
  { rw mem_direction_iff_eq_vsub,
    rintro ⟨p, hp, q, hq, rfl⟩,
    rw ← vadd_vsub_vadd_cancel_left v _ _,
    rw ← mem_const_vadd_iff v at hp,
    rw ← mem_const_vadd_iff v at hq,
    exact vsub_mem_direction hp hq,
    exact hem, },
  rw [not_nonempty_iff_eq_empty, coe_eq_bot_iff] at hem,
  rw [hem, const_vadd_empty],
  exact id,
end

lemma const_vadd_direction (v : V) {s : affine_subspace k P} :
  (v +ᵥ s).direction = s.direction :=
begin
  ext, refine ⟨λ h, _, λ h, mem_const_vadd_direction v x h⟩,
  have hx := mem_const_vadd_direction (-v) x h,
  rwa neg_vadd_vadd at hx,
end

variables {V₁ P₁ V₂ P₂ V₃ P₃ : Type*}
variables [add_comm_group V₁] [module k V₁] [add_torsor V₁ P₁]
variables [add_comm_group V₂] [module k V₂] [add_torsor V₂ P₂]
variables [add_comm_group V₃] [module k V₃] [add_torsor V₃ P₃]
include V₁ V₂
omit V
lemma map_const_vadd {f : P₁ →ᵃ[k] P₂} (v : V₁) (s : affine_subspace k P₁) :
  (v +ᵥ s).map f = f.linear v +ᵥ s.map f :=
begin
  ext,
  simp only [coe_map, coe_const_vadd, mem_image],
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨_, ⟨y, hy, rfl⟩, rfl⟩,
    rw [affine_map.map_vadd, vadd_mem_vadd_set_iff],
    exact mem_image_of_mem _ hy, },
  rcases h with ⟨_, ⟨y, hy, rfl⟩, rfl⟩,
  use v +ᵥ y,
  rw vadd_mem_vadd_set_iff,
  refine ⟨hy, _⟩,
  rw affine_map.map_vadd,
end

end affine_subspace
