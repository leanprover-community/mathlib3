/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.convex.between
import analysis.convex.normed
import analysis.normed.group.add_torsor

/-!
# Sides of affine subspaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines notions of two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `s.w_same_side x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.s_same_side x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.w_opp_side x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.s_opp_side x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/

variables {R V V' P P' : Type*}

open affine_equiv affine_map

namespace affine_subspace

section strict_ordered_comm_ring

variables [strict_ordered_comm_ring R] [add_comm_group V] [module R V] [add_torsor V P]
variables [add_comm_group V'] [module R V'] [add_torsor V' P']

include V

/-- The points `x` and `y` are weakly on the same side of `s`. -/
def w_same_side (s : affine_subspace R P) (x y : P) : Prop :=
∃ p₁ p₂ ∈ s, same_ray R (x -ᵥ p₁) (y -ᵥ p₂)

/-- The points `x` and `y` are strictly on the same side of `s`. -/
def s_same_side (s : affine_subspace R P) (x y : P) : Prop :=
s.w_same_side x y ∧ x ∉ s ∧ y ∉ s

/-- The points `x` and `y` are weakly on opposite sides of `s`. -/
def w_opp_side (s : affine_subspace R P) (x y : P) : Prop :=
∃ p₁ p₂ ∈ s, same_ray R (x -ᵥ p₁) (p₂ -ᵥ y)

/-- The points `x` and `y` are strictly on opposite sides of `s`. -/
def s_opp_side (s : affine_subspace R P) (x y : P) : Prop :=
s.w_opp_side x y ∧ x ∉ s ∧ y ∉ s

include V'

lemma w_same_side.map {s : affine_subspace R P} {x y : P} (h : s.w_same_side x y)
  (f : P →ᵃ[R] P') : (s.map f).w_same_side (f x) (f y) :=
begin
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩,
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩,
  simp_rw [←linear_map_vsub],
  exact h.map f.linear
end

lemma _root_.function.injective.w_same_side_map_iff {s : affine_subspace R P} {x y : P}
  {f : P →ᵃ[R] P'} (hf : function.injective f) :
  (s.map f).w_same_side (f x) (f y) ↔ s.w_same_side x y :=
begin
  refine ⟨λ h, _, λ h, h.map _⟩,
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩,
  rw mem_map at hfp₁ hfp₂,
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩,
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩,
  refine ⟨p₁, hp₁, p₂, hp₂, _⟩,
  simp_rw [←linear_map_vsub, (f.linear_injective_iff.2 hf).same_ray_map_iff] at h,
  exact h
end

lemma _root_.function.injective.s_same_side_map_iff {s : affine_subspace R P} {x y : P}
  {f : P →ᵃ[R] P'} (hf : function.injective f) :
  (s.map f).s_same_side (f x) (f y) ↔ s.s_same_side x y :=
by simp_rw [s_same_side, hf.w_same_side_map_iff, mem_map_iff_mem_of_injective hf]

@[simp] lemma _root_.affine_equiv.w_same_side_map_iff {s : affine_subspace R P} {x y : P}
  (f : P ≃ᵃ[R] P') : (s.map ↑f).w_same_side (f x) (f y) ↔ s.w_same_side x y :=
(show function.injective f.to_affine_map, from f.injective).w_same_side_map_iff

@[simp] lemma _root_.affine_equiv.s_same_side_map_iff {s : affine_subspace R P} {x y : P}
  (f : P ≃ᵃ[R] P') : (s.map ↑f).s_same_side (f x) (f y) ↔ s.s_same_side x y :=
(show function.injective f.to_affine_map, from f.injective).s_same_side_map_iff

lemma w_opp_side.map {s : affine_subspace R P} {x y : P} (h : s.w_opp_side x y)
  (f : P →ᵃ[R] P') : (s.map f).w_opp_side (f x) (f y) :=
begin
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩,
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩,
  simp_rw [←linear_map_vsub],
  exact h.map f.linear
end

lemma _root_.function.injective.w_opp_side_map_iff {s : affine_subspace R P} {x y : P}
  {f : P →ᵃ[R] P'} (hf : function.injective f) :
  (s.map f).w_opp_side (f x) (f y) ↔ s.w_opp_side x y :=
begin
  refine ⟨λ h, _, λ h, h.map _⟩,
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩,
  rw mem_map at hfp₁ hfp₂,
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩,
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩,
  refine ⟨p₁, hp₁, p₂, hp₂, _⟩,
  simp_rw [←linear_map_vsub, (f.linear_injective_iff.2 hf).same_ray_map_iff] at h,
  exact h
end

lemma _root_.function.injective.s_opp_side_map_iff {s : affine_subspace R P} {x y : P}
  {f : P →ᵃ[R] P'} (hf : function.injective f) :
  (s.map f).s_opp_side (f x) (f y) ↔ s.s_opp_side x y :=
by simp_rw [s_opp_side, hf.w_opp_side_map_iff, mem_map_iff_mem_of_injective hf]

@[simp] lemma _root_.affine_equiv.w_opp_side_map_iff {s : affine_subspace R P} {x y : P}
  (f : P ≃ᵃ[R] P') : (s.map ↑f).w_opp_side (f x) (f y) ↔ s.w_opp_side x y :=
(show function.injective f.to_affine_map, from f.injective).w_opp_side_map_iff

@[simp] lemma _root_.affine_equiv.s_opp_side_map_iff {s : affine_subspace R P} {x y : P}
  (f : P ≃ᵃ[R] P') : (s.map ↑f).s_opp_side (f x) (f y) ↔ s.s_opp_side x y :=
(show function.injective f.to_affine_map, from f.injective).s_opp_side_map_iff

omit V'

lemma w_same_side.nonempty {s : affine_subspace R P} {x y : P} (h : s.w_same_side x y) :
  (s : set P).nonempty :=
⟨h.some, h.some_spec.some⟩

lemma s_same_side.nonempty {s : affine_subspace R P} {x y : P} (h : s.s_same_side x y) :
  (s : set P).nonempty :=
⟨h.1.some, h.1.some_spec.some⟩

lemma w_opp_side.nonempty {s : affine_subspace R P} {x y : P} (h : s.w_opp_side x y) :
  (s : set P).nonempty :=
⟨h.some, h.some_spec.some⟩

lemma s_opp_side.nonempty {s : affine_subspace R P} {x y : P} (h : s.s_opp_side x y) :
  (s : set P).nonempty :=
⟨h.1.some, h.1.some_spec.some⟩

lemma s_same_side.w_same_side {s : affine_subspace R P} {x y : P} (h : s.s_same_side x y) :
  s.w_same_side x y :=
h.1

lemma s_same_side.left_not_mem {s : affine_subspace R P} {x y : P} (h : s.s_same_side x y) :
  x ∉ s :=
h.2.1

lemma s_same_side.right_not_mem {s : affine_subspace R P} {x y : P} (h : s.s_same_side x y) :
  y ∉ s :=
h.2.2

lemma s_opp_side.w_opp_side {s : affine_subspace R P} {x y : P} (h : s.s_opp_side x y) :
  s.w_opp_side x y :=
h.1

lemma s_opp_side.left_not_mem {s : affine_subspace R P} {x y : P} (h : s.s_opp_side x y) :
  x ∉ s :=
h.2.1

lemma s_opp_side.right_not_mem {s : affine_subspace R P} {x y : P} (h : s.s_opp_side x y) :
  y ∉ s :=
h.2.2

lemma w_same_side_comm {s : affine_subspace R P} {x y : P} :
  s.w_same_side x y ↔ s.w_same_side y x :=
⟨λ ⟨p₁, hp₁, p₂, hp₂, h⟩, ⟨p₂, hp₂, p₁, hp₁, h.symm⟩,
 λ ⟨p₁, hp₁, p₂, hp₂, h⟩, ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩

alias w_same_side_comm ↔ w_same_side.symm _

lemma s_same_side_comm {s : affine_subspace R P} {x y : P} :
  s.s_same_side x y ↔ s.s_same_side y x :=
by rw [s_same_side, s_same_side, w_same_side_comm, and_comm (x ∉ s)]

alias s_same_side_comm ↔ s_same_side.symm _

lemma w_opp_side_comm {s : affine_subspace R P} {x y : P} :
  s.w_opp_side x y ↔ s.w_opp_side y x :=
begin
  split,
  { rintro ⟨p₁, hp₁, p₂, hp₂, h⟩,
    refine ⟨p₂, hp₂, p₁, hp₁, _⟩,
    rwa [same_ray_comm, ←same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] },
  { rintro ⟨p₁, hp₁, p₂, hp₂, h⟩,
    refine ⟨p₂, hp₂, p₁, hp₁, _⟩,
    rwa [same_ray_comm, ←same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] }
end

alias w_opp_side_comm ↔ w_opp_side.symm _

lemma s_opp_side_comm {s : affine_subspace R P} {x y : P} :
  s.s_opp_side x y ↔ s.s_opp_side y x :=
by rw [s_opp_side, s_opp_side, w_opp_side_comm, and_comm (x ∉ s)]

alias s_opp_side_comm ↔ s_opp_side.symm _

lemma not_w_same_side_bot (x y : P) : ¬ (⊥ : affine_subspace R P).w_same_side x y :=
by simp [w_same_side, not_mem_bot]

lemma not_s_same_side_bot (x y : P) : ¬ (⊥ : affine_subspace R P).s_same_side x y :=
λ h, not_w_same_side_bot x y h.w_same_side

lemma not_w_opp_side_bot (x y : P) : ¬ (⊥ : affine_subspace R P).w_opp_side x y :=
by simp [w_opp_side, not_mem_bot]

lemma not_s_opp_side_bot (x y : P) : ¬ (⊥ : affine_subspace R P).s_opp_side x y :=
λ h, not_w_opp_side_bot x y h.w_opp_side

@[simp] lemma w_same_side_self_iff {s : affine_subspace R P} {x : P} :
  s.w_same_side x x ↔ (s : set P).nonempty :=
⟨λ h, h.nonempty, λ ⟨p, hp⟩, ⟨p, hp, p, hp, same_ray.rfl⟩⟩

lemma s_same_side_self_iff {s : affine_subspace R P} {x : P} :
  s.s_same_side x x ↔ (s : set P).nonempty ∧ x ∉ s :=
⟨λ ⟨h, hx, _⟩, ⟨w_same_side_self_iff.1 h, hx⟩, λ ⟨h, hx⟩, ⟨w_same_side_self_iff.2 h, hx, hx⟩⟩

lemma w_same_side_of_left_mem {s : affine_subspace R P} {x : P} (y : P) (hx : x ∈ s) :
  s.w_same_side x y :=
begin
  refine ⟨x, hx, x, hx, _⟩,
  simp
end

lemma w_same_side_of_right_mem {s : affine_subspace R P} (x : P) {y : P} (hy : y ∈ s) :
  s.w_same_side x y :=
(w_same_side_of_left_mem x hy).symm

lemma w_opp_side_of_left_mem {s : affine_subspace R P} {x : P} (y : P) (hx : x ∈ s) :
  s.w_opp_side x y :=
begin
  refine ⟨x, hx, x, hx, _⟩,
  simp
end

lemma w_opp_side_of_right_mem {s : affine_subspace R P} (x : P) {y : P} (hy : y ∈ s) :
  s.w_opp_side x y :=
(w_opp_side_of_left_mem x hy).symm

lemma w_same_side_vadd_left_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.w_same_side (v +ᵥ x) y ↔ s.w_same_side x y :=
begin
  split,
  { rintro ⟨p₁, hp₁, p₂, hp₂, h⟩,
    refine ⟨-v +ᵥ p₁,
            affine_subspace.vadd_mem_of_mem_direction (submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩,
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ←vadd_vsub_assoc] },
  { rintro ⟨p₁, hp₁, p₂, hp₂, h⟩,
    refine ⟨v +ᵥ p₁,
            affine_subspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩,
    rwa vadd_vsub_vadd_cancel_left }
end

lemma w_same_side_vadd_right_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.w_same_side x (v +ᵥ y) ↔ s.w_same_side x y :=
by rw [w_same_side_comm, w_same_side_vadd_left_iff hv, w_same_side_comm]

lemma s_same_side_vadd_left_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.s_same_side (v +ᵥ x) y ↔ s.s_same_side x y :=
by rw [s_same_side, s_same_side, w_same_side_vadd_left_iff hv,
       vadd_mem_iff_mem_of_mem_direction hv]

lemma s_same_side_vadd_right_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.s_same_side x (v +ᵥ y) ↔ s.s_same_side x y :=
by rw [s_same_side_comm, s_same_side_vadd_left_iff hv, s_same_side_comm]

lemma w_opp_side_vadd_left_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.w_opp_side (v +ᵥ x) y ↔ s.w_opp_side x y :=
begin
  split,
  { rintro ⟨p₁, hp₁, p₂, hp₂, h⟩,
    refine ⟨-v +ᵥ p₁,
            affine_subspace.vadd_mem_of_mem_direction (submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩,
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ←vadd_vsub_assoc] },
  { rintro ⟨p₁, hp₁, p₂, hp₂, h⟩,
    refine ⟨v +ᵥ p₁,
            affine_subspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩,
    rwa vadd_vsub_vadd_cancel_left }
end

lemma w_opp_side_vadd_right_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.w_opp_side x (v +ᵥ y) ↔ s.w_opp_side x y :=
by rw [w_opp_side_comm, w_opp_side_vadd_left_iff hv, w_opp_side_comm]

lemma s_opp_side_vadd_left_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.s_opp_side (v +ᵥ x) y ↔ s.s_opp_side x y :=
by rw [s_opp_side, s_opp_side, w_opp_side_vadd_left_iff hv,
       vadd_mem_iff_mem_of_mem_direction hv]

lemma s_opp_side_vadd_right_iff {s : affine_subspace R P} {x y : P} {v : V}
  (hv : v ∈ s.direction) : s.s_opp_side x (v +ᵥ y) ↔ s.s_opp_side x y :=
by rw [s_opp_side_comm, s_opp_side_vadd_left_iff hv, s_opp_side_comm]

lemma w_same_side_smul_vsub_vadd_left {s : affine_subspace R P} {p₁ p₂ : P} (x : P)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.w_same_side (t • (x -ᵥ p₁) +ᵥ p₂) x :=
begin
  refine ⟨p₂, hp₂, p₁, hp₁, _⟩,
  rw vadd_vsub,
  exact same_ray_nonneg_smul_left _ ht
end

lemma w_same_side_smul_vsub_vadd_right {s : affine_subspace R P} {p₁ p₂ : P} (x : P)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.w_same_side x (t • (x -ᵥ p₁) +ᵥ p₂) :=
(w_same_side_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

lemma w_same_side_line_map_left {s : affine_subspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
  (ht : 0 ≤ t) : s.w_same_side (line_map x y t) y :=
w_same_side_smul_vsub_vadd_left y h h ht

lemma w_same_side_line_map_right {s : affine_subspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
  (ht : 0 ≤ t) : s.w_same_side y (line_map x y t) :=
(w_same_side_line_map_left y h ht).symm

lemma w_opp_side_smul_vsub_vadd_left {s : affine_subspace R P} {p₁ p₂ : P} (x : P)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.w_opp_side (t • (x -ᵥ p₁) +ᵥ p₂) x :=
begin
  refine ⟨p₂, hp₂, p₁, hp₁, _⟩,
  rw [vadd_vsub, ←neg_neg t, neg_smul, ←smul_neg, neg_vsub_eq_vsub_rev],
  exact same_ray_nonneg_smul_left _ (neg_nonneg.2 ht)
end

lemma w_opp_side_smul_vsub_vadd_right {s : affine_subspace R P} {p₁ p₂ : P} (x : P)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.w_opp_side x (t • (x -ᵥ p₁) +ᵥ p₂) :=
(w_opp_side_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

lemma w_opp_side_line_map_left {s : affine_subspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
  (ht : t ≤ 0) : s.w_opp_side (line_map x y t) y :=
w_opp_side_smul_vsub_vadd_left y h h ht

lemma w_opp_side_line_map_right {s : affine_subspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
  (ht : t ≤ 0) : s.w_opp_side y (line_map x y t) :=
(w_opp_side_line_map_left y h ht).symm

lemma _root_.wbtw.w_same_side₂₃ {s : affine_subspace R P} {x y z : P} (h : wbtw R x y z)
  (hx : x ∈ s) : s.w_same_side y z :=
begin
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩,
  exact w_same_side_line_map_left z hx ht0
end

lemma _root_.wbtw.w_same_side₃₂ {s : affine_subspace R P} {x y z : P} (h : wbtw R x y z)
  (hx : x ∈ s) : s.w_same_side z y :=
(h.w_same_side₂₃ hx).symm

lemma _root_.wbtw.w_same_side₁₂ {s : affine_subspace R P} {x y z : P} (h : wbtw R x y z)
  (hz : z ∈ s) : s.w_same_side x y :=
h.symm.w_same_side₃₂ hz

lemma _root_.wbtw.w_same_side₂₁ {s : affine_subspace R P} {x y z : P} (h : wbtw R x y z)
  (hz : z ∈ s) : s.w_same_side y x :=
h.symm.w_same_side₂₃ hz

lemma _root_.wbtw.w_opp_side₁₃ {s : affine_subspace R P} {x y z : P} (h : wbtw R x y z)
  (hy : y ∈ s) : s.w_opp_side x z :=
begin
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩,
  refine ⟨_, hy, _, hy, _⟩,
  rcases ht1.lt_or_eq with ht1' | rfl, swap, { simp },
  rcases ht0.lt_or_eq with ht0' | rfl, swap, { simp },
  refine or.inr (or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', _⟩),
  simp_rw [line_map_apply, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ←neg_vsub_eq_vsub_rev z x,
           vsub_self, zero_sub, ←neg_one_smul R (z -ᵥ x), ←add_smul, smul_neg, ←neg_smul,
           smul_smul],
  ring_nf
end

lemma _root_.wbtw.w_opp_side₃₁ {s : affine_subspace R P} {x y z : P} (h : wbtw R x y z)
  (hy : y ∈ s) : s.w_opp_side z x :=
h.symm.w_opp_side₁₃ hy

end strict_ordered_comm_ring

section linear_ordered_field

variables [linear_ordered_field R] [add_comm_group V] [module R V] [add_torsor V P]
variables [add_comm_group V'] [module R V'] [add_torsor V' P']

include V

variables {R}

@[simp] lemma w_opp_side_self_iff {s : affine_subspace R P} {x : P} : s.w_opp_side x x ↔ x ∈ s :=
begin
  split,
  { rintro ⟨p₁, hp₁, p₂, hp₂, h⟩,
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add,
    rw [add_comm, vsub_add_vsub_cancel, ←eq_vadd_iff_vsub_eq] at h₁,
    rw h₁,
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁ },
  { exact λ h, ⟨x, h, x, h, same_ray.rfl⟩ }
end

lemma not_s_opp_side_self (s : affine_subspace R P) (x : P) : ¬s.s_opp_side x x :=
by simp [s_opp_side]

lemma w_same_side_iff_exists_left {s : affine_subspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
  s.w_same_side x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, same_ray R (x -ᵥ p₁) (y -ᵥ p₂) :=
begin
  split,
  { rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩,
    { rw vsub_eq_zero_iff_eq at h0,
      rw h0,
      exact or.inl hp₁' },
    { refine or.inr ⟨p₂', hp₂', _⟩,
      rw h0,
      exact same_ray.zero_right _ },
    { refine or.inr ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
                     or.inr (or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩,
      rw [vsub_vadd_eq_vsub_sub, smul_sub, ←hr, smul_smul, mul_div_cancel' _ hr₂.ne.symm,
          ←smul_sub, vsub_sub_vsub_cancel_right] } },
  { rintro (h' | h'),
    { exact w_same_side_of_left_mem y h' },
    { exact ⟨p₁, h, h'⟩ } }
end

lemma w_same_side_iff_exists_right {s : affine_subspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
  s.w_same_side x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, same_ray R (x -ᵥ p₁) (y -ᵥ p₂) :=
begin
  rw [w_same_side_comm, w_same_side_iff_exists_left h],
  simp_rw same_ray_comm
end

lemma s_same_side_iff_exists_left {s : affine_subspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
  s.s_same_side x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, same_ray R (x -ᵥ p₁) (y -ᵥ p₂) :=
begin
  rw [s_same_side, and_comm, w_same_side_iff_exists_left h, and_assoc, and.congr_right_iff],
  intro hx,
  rw or_iff_right hx
end

lemma s_same_side_iff_exists_right {s : affine_subspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
  s.s_same_side x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, same_ray R (x -ᵥ p₁) (y -ᵥ p₂) :=
begin
  rw [s_same_side_comm, s_same_side_iff_exists_left h, ←and_assoc, and_comm (y ∉ s), and_assoc],
  simp_rw same_ray_comm
end

lemma w_opp_side_iff_exists_left {s : affine_subspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
  s.w_opp_side x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, same_ray R (x -ᵥ p₁) (p₂ -ᵥ y) :=
begin
  split,
  { rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩,
    { rw vsub_eq_zero_iff_eq at h0,
      rw h0,
      exact or.inl hp₁' },
    { refine or.inr ⟨p₂', hp₂', _⟩,
      rw h0,
      exact same_ray.zero_right _ },
    { refine or.inr ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
                     or.inr (or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩,
      rw [vadd_vsub_assoc, smul_add, ←hr, smul_smul, neg_div, mul_neg,
          mul_div_cancel' _ hr₂.ne.symm, neg_smul, neg_add_eq_sub, ←smul_sub,
          vsub_sub_vsub_cancel_right] } },
  { rintro (h' | h'),
    { exact w_opp_side_of_left_mem y h' },
    { exact ⟨p₁, h, h'⟩ } }
end

lemma w_opp_side_iff_exists_right {s : affine_subspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
  s.w_opp_side x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, same_ray R (x -ᵥ p₁) (p₂ -ᵥ y) :=
begin
  rw [w_opp_side_comm, w_opp_side_iff_exists_left h],
  split,
  { rintro (hy | ⟨p, hp, hr⟩), { exact or.inl hy },
    refine or.inr ⟨p, hp, _⟩,
    rwa [same_ray_comm, ←same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] },
  { rintro (hy | ⟨p, hp, hr⟩), { exact or.inl hy },
    refine or.inr ⟨p, hp, _⟩,
    rwa [same_ray_comm, ←same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] }
end

lemma s_opp_side_iff_exists_left {s : affine_subspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
  s.s_opp_side x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, same_ray R (x -ᵥ p₁) (p₂ -ᵥ y) :=
begin
  rw [s_opp_side, and_comm, w_opp_side_iff_exists_left h, and_assoc, and.congr_right_iff],
  intro hx,
  rw or_iff_right hx
end

lemma s_opp_side_iff_exists_right {s : affine_subspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
  s.s_opp_side x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, same_ray R (x -ᵥ p₁) (p₂ -ᵥ y) :=
begin
  rw [s_opp_side, and_comm, w_opp_side_iff_exists_right h, and_assoc, and.congr_right_iff,
      and.congr_right_iff],
  rintro hx hy,
  rw or_iff_right hy
end

lemma w_same_side.trans {s : affine_subspace R P} {x y z : P} (hxy : s.w_same_side x y)
  (hyz : s.w_same_side y z) (hy : y ∉ s) : s.w_same_side x z :=
begin
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩,
  rw [w_same_side_iff_exists_left hp₂, or_iff_right hy] at hyz,
  rcases hyz with ⟨p₃, hp₃, hyz⟩,
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩,
  refine λ h, false.elim _,
  rw vsub_eq_zero_iff_eq at h,
  exact hy (h.symm ▸ hp₂)
end

lemma w_same_side.trans_s_same_side {s : affine_subspace R P} {x y z : P}
  (hxy : s.w_same_side x y) (hyz : s.s_same_side y z) : s.w_same_side x z :=
hxy.trans hyz.1 hyz.2.1

lemma w_same_side.trans_w_opp_side {s : affine_subspace R P} {x y z : P} (hxy : s.w_same_side x y)
  (hyz : s.w_opp_side y z) (hy : y ∉ s) : s.w_opp_side x z :=
begin
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩,
  rw [w_opp_side_iff_exists_left hp₂, or_iff_right hy] at hyz,
  rcases hyz with ⟨p₃, hp₃, hyz⟩,
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩,
  refine λ h, false.elim _,
  rw vsub_eq_zero_iff_eq at h,
  exact hy (h.symm ▸ hp₂)
end

lemma w_same_side.trans_s_opp_side {s : affine_subspace R P} {x y z : P} (hxy : s.w_same_side x y)
  (hyz : s.s_opp_side y z) : s.w_opp_side x z :=
hxy.trans_w_opp_side hyz.1 hyz.2.1

lemma s_same_side.trans_w_same_side {s : affine_subspace R P} {x y z : P}
  (hxy : s.s_same_side x y) (hyz : s.w_same_side y z) : s.w_same_side x z :=
(hyz.symm.trans_s_same_side hxy.symm).symm

lemma s_same_side.trans {s : affine_subspace R P} {x y z : P} (hxy : s.s_same_side x y)
  (hyz : s.s_same_side y z) : s.s_same_side x z :=
⟨hxy.w_same_side.trans_s_same_side hyz, hxy.2.1, hyz.2.2⟩

lemma s_same_side.trans_w_opp_side {s : affine_subspace R P} {x y z : P} (hxy : s.s_same_side x y)
  (hyz : s.w_opp_side y z) : s.w_opp_side x z :=
hxy.w_same_side.trans_w_opp_side hyz hxy.2.2

lemma s_same_side.trans_s_opp_side {s : affine_subspace R P} {x y z : P} (hxy : s.s_same_side x y)
  (hyz : s.s_opp_side y z) : s.s_opp_side x z :=
⟨hxy.trans_w_opp_side hyz.1, hxy.2.1, hyz.2.2⟩

lemma w_opp_side.trans_w_same_side {s : affine_subspace R P} {x y z : P} (hxy : s.w_opp_side x y)
  (hyz : s.w_same_side y z) (hy : y ∉ s) : s.w_opp_side x z :=
(hyz.symm.trans_w_opp_side hxy.symm hy).symm

lemma w_opp_side.trans_s_same_side {s : affine_subspace R P} {x y z : P} (hxy : s.w_opp_side x y)
  (hyz : s.s_same_side y z) : s.w_opp_side x z :=
hxy.trans_w_same_side hyz.1 hyz.2.1

lemma w_opp_side.trans {s : affine_subspace R P} {x y z : P} (hxy : s.w_opp_side x y)
  (hyz : s.w_opp_side y z) (hy : y ∉ s) : s.w_same_side x z :=
begin
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩,
  rw [w_opp_side_iff_exists_left hp₂, or_iff_right hy] at hyz,
  rcases hyz with ⟨p₃, hp₃, hyz⟩,
  rw [←same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hyz,
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩,
  refine λ h, false.elim _,
  rw vsub_eq_zero_iff_eq at h,
  exact hy (h ▸ hp₂)
end

lemma w_opp_side.trans_s_opp_side {s : affine_subspace R P} {x y z : P} (hxy : s.w_opp_side x y)
  (hyz : s.s_opp_side y z) : s.w_same_side x z :=
hxy.trans hyz.1 hyz.2.1

lemma s_opp_side.trans_w_same_side {s : affine_subspace R P} {x y z : P} (hxy : s.s_opp_side x y)
  (hyz : s.w_same_side y z) : s.w_opp_side x z :=
(hyz.symm.trans_s_opp_side hxy.symm).symm

lemma s_opp_side.trans_s_same_side {s : affine_subspace R P} {x y z : P} (hxy : s.s_opp_side x y)
  (hyz : s.s_same_side y z) : s.s_opp_side x z :=
(hyz.symm.trans_s_opp_side hxy.symm).symm

lemma s_opp_side.trans_w_opp_side {s : affine_subspace R P} {x y z : P} (hxy : s.s_opp_side x y)
  (hyz : s.w_opp_side y z) : s.w_same_side x z :=
(hyz.symm.trans_s_opp_side hxy.symm).symm

lemma s_opp_side.trans {s : affine_subspace R P} {x y z : P} (hxy : s.s_opp_side x y)
  (hyz : s.s_opp_side y z) : s.s_same_side x z :=
⟨hxy.trans_w_opp_side hyz.1, hxy.2.1, hyz.2.2⟩

lemma w_same_side_and_w_opp_side_iff {s : affine_subspace R P} {x y : P} :
  (s.w_same_side x y ∧ s.w_opp_side x y) ↔ (x ∈ s ∨ y ∈ s) :=
begin
  split,
  { rintro ⟨hs, ho⟩,
    rw w_opp_side_comm at ho,
    by_contra h,
    rw not_or_distrib at h,
    exact h.1 (w_opp_side_self_iff.1 (hs.trans_w_opp_side ho h.2)) },
  { rintro (h | h),
    { exact ⟨w_same_side_of_left_mem y h, w_opp_side_of_left_mem y h⟩ },
    { exact ⟨w_same_side_of_right_mem x h, w_opp_side_of_right_mem x h⟩ } }
end

lemma w_same_side.not_s_opp_side {s : affine_subspace R P} {x y : P} (h : s.w_same_side x y) :
  ¬s.s_opp_side x y :=
begin
  intro ho,
  have hxy := w_same_side_and_w_opp_side_iff.1 ⟨h, ho.1⟩,
  rcases hxy with hx | hy,
  { exact ho.2.1 hx },
  { exact ho.2.2 hy }
end

lemma s_same_side.not_w_opp_side {s : affine_subspace R P} {x y : P} (h : s.s_same_side x y) :
  ¬s.w_opp_side x y :=
begin
  intro ho,
  have hxy := w_same_side_and_w_opp_side_iff.1 ⟨h.1, ho⟩,
  rcases hxy with hx | hy,
  { exact h.2.1 hx },
  { exact h.2.2 hy }
end

lemma s_same_side.not_s_opp_side {s : affine_subspace R P} {x y : P} (h : s.s_same_side x y) :
  ¬s.s_opp_side x y :=
λ ho, h.not_w_opp_side ho.1

lemma w_opp_side.not_s_same_side {s : affine_subspace R P} {x y : P} (h : s.w_opp_side x y) :
  ¬s.s_same_side x y :=
λ hs, hs.not_w_opp_side h

lemma s_opp_side.not_w_same_side {s : affine_subspace R P} {x y : P} (h : s.s_opp_side x y) :
  ¬s.w_same_side x y :=
λ hs, hs.not_s_opp_side h

lemma s_opp_side.not_s_same_side {s : affine_subspace R P} {x y : P} (h : s.s_opp_side x y) :
  ¬s.s_same_side x y :=
λ hs, h.not_w_same_side hs.1

lemma w_opp_side_iff_exists_wbtw {s : affine_subspace R P} {x y : P} :
  s.w_opp_side x y ↔ ∃ p ∈ s, wbtw R x p y :=
begin
  refine ⟨λ h, _, λ ⟨p, hp, h⟩, h.w_opp_side₁₃ hp⟩,
  rcases h with ⟨p₁, hp₁, p₂, hp₂, (h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩)⟩,
  { rw vsub_eq_zero_iff_eq at h,
    rw h,
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩ },
  { rw vsub_eq_zero_iff_eq at h,
    rw ←h,
    exact ⟨p₂, hp₂, wbtw_self_right _ _ _⟩ },
  { refine ⟨line_map x y (r₂ / (r₁ + r₂)), _, _⟩,
    { rw [line_map_apply, ←vsub_vadd x p₁, ←vsub_vadd y p₂, vsub_vadd_eq_vsub_sub,
          vadd_vsub_assoc, ←vadd_assoc, vadd_eq_add],
      convert s.smul_vsub_vadd_mem (r₂ / (r₁ + r₂)) hp₂ hp₁ hp₁,
      rw [add_comm (y -ᵥ p₂), smul_sub, smul_add, add_sub_assoc, add_assoc, add_right_eq_self,
          div_eq_inv_mul, ←neg_vsub_eq_vsub_rev, smul_neg, ←smul_smul, ←h, smul_smul,
          ←neg_smul, ←sub_smul, ←div_eq_inv_mul, ←div_eq_inv_mul, ←neg_div, ←sub_div,
          sub_eq_add_neg, ←neg_add, neg_div, div_self (left.add_pos hr₁ hr₂).ne.symm,
          neg_one_smul, neg_add_self] },
    { exact set.mem_image_of_mem _ ⟨div_nonneg hr₂.le (left.add_pos hr₁ hr₂).le,
                                    div_le_one_of_le (le_add_of_nonneg_left hr₁.le)
                                                     (left.add_pos hr₁ hr₂).le⟩ } }
end

lemma s_opp_side.exists_sbtw {s : affine_subspace R P} {x y : P} (h : s.s_opp_side x y) :
  ∃ p ∈ s, sbtw R x p y :=
begin
  obtain ⟨p, hp, hw⟩ := w_opp_side_iff_exists_wbtw.1 h.w_opp_side,
  refine ⟨p, hp, hw, _, _⟩,
  { rintro rfl,
    exact h.2.1 hp },
  { rintro rfl,
    exact h.2.2 hp },
end

lemma _root_.sbtw.s_opp_side_of_not_mem_of_mem {s : affine_subspace R P} {x y z : P}
  (h : sbtw R x y z) (hx : x ∉ s) (hy : y ∈ s) : s.s_opp_side x z :=
begin
  refine ⟨h.wbtw.w_opp_side₁₃ hy, hx, λ hz, hx _⟩,
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩,
  rw line_map_apply at hy,
  have ht : t ≠ 1, { rintro rfl, simpa [line_map_apply] using hyz },
  have hy' := vsub_mem_direction hy hz,
  rw [vadd_vsub_assoc, ←neg_vsub_eq_vsub_rev z, ←neg_one_smul R (z -ᵥ x), ←add_smul,
      ←sub_eq_add_neg, s.direction.smul_mem_iff (sub_ne_zero_of_ne ht)] at hy',
  rwa vadd_mem_iff_mem_of_mem_direction (submodule.smul_mem _ _ hy') at hy
end

lemma s_same_side_smul_vsub_vadd_left {s : affine_subspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.s_same_side (t • (x -ᵥ p₁) +ᵥ p₂) x :=
begin
  refine ⟨w_same_side_smul_vsub_vadd_left x hp₁ hp₂ ht.le, λ h, hx _, hx⟩,
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
       vsub_right_mem_direction_iff_mem hp₁] at h
end

lemma s_same_side_smul_vsub_vadd_right {s : affine_subspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.s_same_side x (t • (x -ᵥ p₁) +ᵥ p₂) :=
(s_same_side_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

lemma s_same_side_line_map_left {s : affine_subspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s)
  {t : R} (ht : 0 < t) : s.s_same_side (line_map x y t) y :=
s_same_side_smul_vsub_vadd_left hy hx hx ht

lemma s_same_side_line_map_right {s : affine_subspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s)
  {t : R} (ht : 0 < t) : s.s_same_side y (line_map x y t) :=
(s_same_side_line_map_left hx hy ht).symm

lemma s_opp_side_smul_vsub_vadd_left {s : affine_subspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.s_opp_side (t • (x -ᵥ p₁) +ᵥ p₂) x :=
begin
  refine ⟨w_opp_side_smul_vsub_vadd_left x hp₁ hp₂ ht.le, λ h, hx _, hx⟩,
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
       vsub_right_mem_direction_iff_mem hp₁] at h
end

lemma s_opp_side_smul_vsub_vadd_right {s : affine_subspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.s_opp_side x (t • (x -ᵥ p₁) +ᵥ p₂) :=
(s_opp_side_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

lemma s_opp_side_line_map_left {s : affine_subspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s)
  {t : R} (ht : t < 0) : s.s_opp_side (line_map x y t) y :=
s_opp_side_smul_vsub_vadd_left hy hx hx ht

lemma s_opp_side_line_map_right {s : affine_subspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s)
  {t : R} (ht : t < 0) : s.s_opp_side y (line_map x y t) :=
(s_opp_side_line_map_left hx hy ht).symm

lemma set_of_w_same_side_eq_image2 {s : affine_subspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
  {y | s.w_same_side x y} = set.image2 (λ (t : R) q, t • (x -ᵥ p) +ᵥ q) (set.Ici 0) s :=
begin
  ext y,
  simp_rw [set.mem_set_of, set.mem_image2, set.mem_Ici, mem_coe],
  split,
  { rw [w_same_side_iff_exists_left hp, or_iff_right hx],
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩,
    { rw vsub_eq_zero_iff_eq at h,
      exact false.elim (hx (h.symm ▸ hp)) },
    { rw vsub_eq_zero_iff_eq at h,
      refine ⟨0, p₂, le_refl _, hp₂, _⟩,
      simp [h] },
    { refine ⟨r₁ / r₂, p₂, (div_pos hr₁ hr₂).le, hp₂, _⟩,
      rw [div_eq_inv_mul, ←smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
          vsub_vadd] } },
  { rintro ⟨t, p', ht, hp', rfl⟩,
    exact w_same_side_smul_vsub_vadd_right x hp hp' ht }
end

lemma set_of_s_same_side_eq_image2 {s : affine_subspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
  {y | s.s_same_side x y} = set.image2 (λ (t : R) q, t • (x -ᵥ p) +ᵥ q) (set.Ioi 0) s :=
begin
  ext y,
  simp_rw [set.mem_set_of, set.mem_image2, set.mem_Ioi, mem_coe],
  split,
  { rw s_same_side_iff_exists_left hp,
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩,
    { rw vsub_eq_zero_iff_eq at h,
      exact false.elim (hx (h.symm ▸ hp)) },
    { rw vsub_eq_zero_iff_eq at h,
      exact false.elim (hy (h.symm ▸ hp₂)) },
    { refine ⟨r₁ / r₂, p₂, div_pos hr₁ hr₂, hp₂, _⟩,
      rw [div_eq_inv_mul, ←smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
          vsub_vadd] } },
  { rintro ⟨t, p', ht, hp', rfl⟩,
    exact s_same_side_smul_vsub_vadd_right hx hp hp' ht }
end

lemma set_of_w_opp_side_eq_image2 {s : affine_subspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
  {y | s.w_opp_side x y} = set.image2 (λ (t : R) q, t • (x -ᵥ p) +ᵥ q) (set.Iic 0) s :=
begin
  ext y,
  simp_rw [set.mem_set_of, set.mem_image2, set.mem_Iic, mem_coe],
  split,
  { rw [w_opp_side_iff_exists_left hp, or_iff_right hx],
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩,
    { rw vsub_eq_zero_iff_eq at h,
      exact false.elim (hx (h.symm ▸ hp)) },
    { rw vsub_eq_zero_iff_eq at h,
      refine ⟨0, p₂, le_refl _, hp₂, _⟩,
      simp [h] },
    { refine ⟨-r₁ / r₂, p₂, (div_neg_of_neg_of_pos (left.neg_neg_iff.2 hr₁) hr₂).le, hp₂, _⟩,
      rw [div_eq_inv_mul, ←smul_smul, neg_smul, h, smul_neg, smul_smul,
          inv_mul_cancel hr₂.ne.symm, one_smul, neg_vsub_eq_vsub_rev, vsub_vadd] } },
  { rintro ⟨t, p', ht, hp', rfl⟩,
    exact w_opp_side_smul_vsub_vadd_right x hp hp' ht }
end

lemma set_of_s_opp_side_eq_image2 {s : affine_subspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
  {y | s.s_opp_side x y} = set.image2 (λ (t : R) q, t • (x -ᵥ p) +ᵥ q) (set.Iio 0) s :=
begin
  ext y,
  simp_rw [set.mem_set_of, set.mem_image2, set.mem_Iio, mem_coe],
  split,
  { rw s_opp_side_iff_exists_left hp,
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩,
    { rw vsub_eq_zero_iff_eq at h,
      exact false.elim (hx (h.symm ▸ hp)) },
    { rw vsub_eq_zero_iff_eq at h,
      exact false.elim (hy (h ▸ hp₂)) },
    { refine ⟨-r₁ / r₂, p₂, div_neg_of_neg_of_pos (left.neg_neg_iff.2 hr₁) hr₂, hp₂, _⟩,
      rw [div_eq_inv_mul, ←smul_smul, neg_smul, h, smul_neg, smul_smul,
          inv_mul_cancel hr₂.ne.symm, one_smul, neg_vsub_eq_vsub_rev, vsub_vadd] } },
  { rintro ⟨t, p', ht, hp', rfl⟩,
    exact s_opp_side_smul_vsub_vadd_right hx hp hp' ht }
end

lemma w_opp_side_point_reflection {s : affine_subspace R P} {x : P} (y : P) (hx : x ∈ s) :
  s.w_opp_side y (point_reflection R x y) :=
(wbtw_point_reflection R _ _).w_opp_side₁₃ hx

lemma s_opp_side_point_reflection {s : affine_subspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) :
  s.s_opp_side y (point_reflection R x y) :=
begin
  refine (sbtw_point_reflection_of_ne R (λ h, hy _)).s_opp_side_of_not_mem_of_mem hy hx,
  rwa ←h
end

end linear_ordered_field

section normed

variables [seminormed_add_comm_group V] [normed_space ℝ V] [pseudo_metric_space P]
variables [normed_add_torsor V P]

include V

lemma is_connected_set_of_w_same_side {s : affine_subspace ℝ P} (x : P)
  (h : (s : set P).nonempty) : is_connected {y | s.w_same_side x y} :=
begin
  obtain ⟨p, hp⟩ := h,
  haveI : nonempty s := ⟨⟨p, hp⟩⟩,
  by_cases hx : x ∈ s,
  { convert is_connected_univ,
    { simp [w_same_side_of_left_mem, hx] },
    { exact add_torsor.connected_space V P } },
  { rw [set_of_w_same_side_eq_image2 hx hp, ←set.image_prod],
    refine (is_connected_Ici.prod (is_connected_iff_connected_space.2 _)).image _
           ((continuous_fst.smul continuous_const).vadd continuous_snd).continuous_on,
    convert add_torsor.connected_space s.direction s }
end

lemma is_preconnected_set_of_w_same_side (s : affine_subspace ℝ P) (x : P) :
  is_preconnected {y | s.w_same_side x y} :=
begin
  rcases set.eq_empty_or_nonempty (s : set P) with h | h,
  { convert is_preconnected_empty,
    rw coe_eq_bot_iff at h,
    simp only [h, not_w_same_side_bot],
    refl },
  { exact (is_connected_set_of_w_same_side x h).is_preconnected }
end

lemma is_connected_set_of_s_same_side {s : affine_subspace ℝ P} {x : P} (hx : x ∉ s)
  (h : (s : set P).nonempty) : is_connected {y | s.s_same_side x y} :=
begin
  obtain ⟨p, hp⟩ := h,
  haveI : nonempty s := ⟨⟨p, hp⟩⟩,
  rw [set_of_s_same_side_eq_image2 hx hp, ←set.image_prod],
  refine (is_connected_Ioi.prod (is_connected_iff_connected_space.2 _)).image _
         ((continuous_fst.smul continuous_const).vadd continuous_snd).continuous_on,
  convert add_torsor.connected_space s.direction s
end

lemma is_preconnected_set_of_s_same_side (s : affine_subspace ℝ P) (x : P) :
  is_preconnected {y | s.s_same_side x y} :=
begin
  rcases set.eq_empty_or_nonempty (s : set P) with h | h,
  { convert is_preconnected_empty,
    rw coe_eq_bot_iff at h,
    simp only [h, not_s_same_side_bot],
    refl },
  { by_cases hx : x ∈ s,
    { convert is_preconnected_empty,
      simp only [hx, s_same_side, not_true, false_and, and_false],
      refl },
    { exact (is_connected_set_of_s_same_side hx h).is_preconnected } }
end

lemma is_connected_set_of_w_opp_side {s : affine_subspace ℝ P} (x : P)
  (h : (s : set P).nonempty) : is_connected {y | s.w_opp_side x y} :=
begin
  obtain ⟨p, hp⟩ := h,
  haveI : nonempty s := ⟨⟨p, hp⟩⟩,
  by_cases hx : x ∈ s,
  { convert is_connected_univ,
    { simp [w_opp_side_of_left_mem, hx] },
    { exact add_torsor.connected_space V P } },
  { rw [set_of_w_opp_side_eq_image2 hx hp, ←set.image_prod],
    refine (is_connected_Iic.prod (is_connected_iff_connected_space.2 _)).image _
           ((continuous_fst.smul continuous_const).vadd continuous_snd).continuous_on,
    convert add_torsor.connected_space s.direction s }
end

lemma is_preconnected_set_of_w_opp_side (s : affine_subspace ℝ P) (x : P) :
  is_preconnected {y | s.w_opp_side x y} :=
begin
  rcases set.eq_empty_or_nonempty (s : set P) with h | h,
  { convert is_preconnected_empty,
    rw coe_eq_bot_iff at h,
    simp only [h, not_w_opp_side_bot],
    refl },
  { exact (is_connected_set_of_w_opp_side x h).is_preconnected }
end

lemma is_connected_set_of_s_opp_side {s : affine_subspace ℝ P} {x : P} (hx : x ∉ s)
  (h : (s : set P).nonempty) : is_connected {y | s.s_opp_side x y} :=
begin
  obtain ⟨p, hp⟩ := h,
  haveI : nonempty s := ⟨⟨p, hp⟩⟩,
  rw [set_of_s_opp_side_eq_image2 hx hp, ←set.image_prod],
  refine (is_connected_Iio.prod (is_connected_iff_connected_space.2 _)).image _
         ((continuous_fst.smul continuous_const).vadd continuous_snd).continuous_on,
  convert add_torsor.connected_space s.direction s
end

lemma is_preconnected_set_of_s_opp_side (s : affine_subspace ℝ P) (x : P) :
  is_preconnected {y | s.s_opp_side x y} :=
begin
  rcases set.eq_empty_or_nonempty (s : set P) with h | h,
  { convert is_preconnected_empty,
    rw coe_eq_bot_iff at h,
    simp only [h, not_s_opp_side_bot],
    refl },
  { by_cases hx : x ∈ s,
    { convert is_preconnected_empty,
      simp only [hx, s_opp_side, not_true, false_and, and_false],
      refl },
    { exact (is_connected_set_of_s_opp_side hx h).is_preconnected } }
end

end normed

end affine_subspace
