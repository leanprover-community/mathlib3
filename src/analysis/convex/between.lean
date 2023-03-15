/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import data.set.intervals.group
import analysis.convex.segment
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.midpoint_zero
import tactic.field_simp

/-!
# Betweenness in affine spaces

This file defines notions of a point in an affine space being between two given points.

## Main definitions

* `affine_segment R x y`: The segment of points weakly between `x` and `y`.
* `wbtw R x y z`: The point `y` is weakly between `x` and `z`.
* `sbtw R x y z`: The point `y` is strictly between `x` and `z`.

-/

variables (R : Type*) {V V' P P' : Type*}

open affine_equiv affine_map

open_locale big_operators

section ordered_ring

variables [ordered_ring R] [add_comm_group V] [module R V] [add_torsor V P]
variables [add_comm_group V'] [module R V'] [add_torsor V' P']

include V

/-- The segment of points weakly between `x` and `y`. When convexity is refactored to support
abstract affine combination spaces, this will no longer need to be a separate definition from
`segment`. However, lemmas involving `+ᵥ` or `-ᵥ` will still be relevant after such a
refactoring, as distinct from versions involving `+` or `-` in a module. -/
def affine_segment (x y : P) := line_map x y '' (set.Icc (0 : R) 1)

lemma affine_segment_eq_segment (x y : V) : affine_segment R x y = segment R x y :=
by rw [segment_eq_image_line_map, affine_segment]

lemma affine_segment_comm (x y : P) : affine_segment R x y = affine_segment R y x :=
begin
  refine set.ext (λ z, _),
  split;
    { rintro ⟨t, ht, hxy⟩,
      refine ⟨1 - t, _, _⟩,
      { rwa [set.sub_mem_Icc_iff_right, sub_self, sub_zero] },
      { rwa [line_map_apply_one_sub] } },
end

lemma left_mem_affine_segment (x y : P) : x ∈ affine_segment R x y :=
⟨0, set.left_mem_Icc.2 zero_le_one, line_map_apply_zero _ _⟩

lemma right_mem_affine_segment (x y : P) : y ∈ affine_segment R x y :=
⟨1, set.right_mem_Icc.2 zero_le_one, line_map_apply_one _ _⟩

include V'

variables {R}

@[simp] lemma affine_segment_image (f : P →ᵃ[R] P') (x y : P) :
  f '' affine_segment R x y = affine_segment R (f x) (f y) :=
begin
  rw [affine_segment, affine_segment, set.image_image, ←comp_line_map],
  refl
end

omit V'

variables (R)

@[simp] lemma affine_segment_const_vadd_image (x y : P) (v : V) :
  ((+ᵥ) v) '' affine_segment R x y = affine_segment R (v +ᵥ x) (v +ᵥ y) :=
affine_segment_image (affine_equiv.const_vadd R P v : P →ᵃ[R] P) x y

@[simp] lemma affine_segment_vadd_const_image (x y : V) (p : P) :
  (+ᵥ p) '' affine_segment R x y = affine_segment R (x +ᵥ p) (y +ᵥ p) :=
affine_segment_image (affine_equiv.vadd_const R p : V →ᵃ[R] P) x y

@[simp] lemma affine_segment_const_vsub_image (x y p : P) :
  ((-ᵥ) p) '' affine_segment R x y = affine_segment R (p -ᵥ x) (p -ᵥ y) :=
affine_segment_image (affine_equiv.const_vsub R p : P →ᵃ[R] V) x y

@[simp] lemma affine_segment_vsub_const_image (x y p : P) :
  (-ᵥ p) '' affine_segment R x y = affine_segment R (x -ᵥ p) (y -ᵥ p) :=
affine_segment_image ((affine_equiv.vadd_const R p).symm : P →ᵃ[R] V) x y

variables {R}

@[simp] lemma mem_const_vadd_affine_segment {x y z : P} (v : V) :
  v +ᵥ z ∈ affine_segment R (v +ᵥ x) (v +ᵥ y) ↔ z ∈ affine_segment R x y :=
by rw [←affine_segment_const_vadd_image, (add_action.injective v).mem_set_image]

@[simp] lemma mem_vadd_const_affine_segment {x y z : V} (p : P) :
  z +ᵥ p ∈ affine_segment R (x +ᵥ p) (y +ᵥ p) ↔ z ∈ affine_segment R x y :=
by rw [←affine_segment_vadd_const_image, (vadd_right_injective p).mem_set_image]
variables {R}

@[simp] lemma mem_const_vsub_affine_segment {x y z : P} (p : P) :
  p -ᵥ z ∈ affine_segment R (p -ᵥ x) (p -ᵥ y) ↔ z ∈ affine_segment R x y :=
by rw [←affine_segment_const_vsub_image, (vsub_right_injective p).mem_set_image]

@[simp] lemma mem_vsub_const_affine_segment {x y z : P} (p : P) :
  z -ᵥ p ∈ affine_segment R (x -ᵥ p) (y -ᵥ p) ↔ z ∈ affine_segment R x y :=
by rw [←affine_segment_vsub_const_image, (vsub_left_injective p).mem_set_image]

variables (R)

/-- The point `y` is weakly between `x` and `z`. -/
def wbtw (x y z : P) : Prop := y ∈ affine_segment R x z

/-- The point `y` is strictly between `x` and `z`. -/
def sbtw (x y z : P) : Prop := wbtw R x y z ∧ y ≠ x ∧ y ≠ z

variables {R}

include V'

lemma wbtw.map {x y z : P} (h : wbtw R x y z) (f : P →ᵃ[R] P') : wbtw R (f x) (f y) (f z) :=
begin
  rw [wbtw, ←affine_segment_image],
  exact set.mem_image_of_mem _ h
end

lemma function.injective.wbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} (hf : function.injective f) :
  wbtw R (f x) (f y) (f z) ↔ wbtw R x y z :=
begin
  refine ⟨λ h, _, λ h, h.map _⟩,
  rwa [wbtw, ←affine_segment_image, hf.mem_set_image] at h
end

lemma function.injective.sbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} (hf : function.injective f) :
  sbtw R (f x) (f y) (f z) ↔ sbtw R x y z :=
by simp_rw [sbtw, hf.wbtw_map_iff, hf.ne_iff]

@[simp] lemma affine_equiv.wbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') :
  wbtw R (f x) (f y) (f z) ↔ wbtw R x y z :=
begin
  refine function.injective.wbtw_map_iff (_ : function.injective f.to_affine_map),
  exact f.injective
end

@[simp] lemma affine_equiv.sbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') :
  sbtw R (f x) (f y) (f z) ↔ sbtw R x y z :=
begin
  refine function.injective.sbtw_map_iff (_ : function.injective f.to_affine_map),
  exact f.injective
end

omit V'

@[simp] lemma wbtw_const_vadd_iff {x y z : P} (v : V) :
  wbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ wbtw R x y z :=
mem_const_vadd_affine_segment _

@[simp] lemma wbtw_vadd_const_iff {x y z : V} (p : P) :
  wbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ wbtw R x y z :=
mem_vadd_const_affine_segment _

@[simp] lemma wbtw_const_vsub_iff {x y z : P} (p : P) :
  wbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ wbtw R x y z :=
mem_const_vsub_affine_segment _

@[simp] lemma wbtw_vsub_const_iff {x y z : P} (p : P) :
  wbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ wbtw R x y z :=
mem_vsub_const_affine_segment _

@[simp] lemma sbtw_const_vadd_iff {x y z : P} (v : V) :
  sbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ sbtw R x y z :=
by simp_rw [sbtw, wbtw_const_vadd_iff, (add_action.injective v).ne_iff]

@[simp] lemma sbtw_vadd_const_iff {x y z : V} (p : P) :
  sbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ sbtw R x y z :=
by simp_rw [sbtw, wbtw_vadd_const_iff, (vadd_right_injective p).ne_iff]

@[simp] lemma sbtw_const_vsub_iff {x y z : P} (p : P) :
  sbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ sbtw R x y z :=
by simp_rw [sbtw, wbtw_const_vsub_iff, (vsub_right_injective p).ne_iff]

@[simp] lemma sbtw_vsub_const_iff {x y z : P} (p : P) :
  sbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ sbtw R x y z :=
by simp_rw [sbtw, wbtw_vsub_const_iff, (vsub_left_injective p).ne_iff]

lemma sbtw.wbtw {x y z : P} (h : sbtw R x y z) : wbtw R x y z :=
h.1

lemma sbtw.ne_left {x y z : P} (h : sbtw R x y z) : y ≠ x :=
h.2.1

lemma sbtw.left_ne {x y z : P} (h : sbtw R x y z) : x ≠ y :=
h.2.1.symm

lemma sbtw.ne_right {x y z : P} (h : sbtw R x y z) : y ≠ z :=
h.2.2

lemma sbtw.right_ne {x y z : P} (h : sbtw R x y z) : z ≠ y :=
h.2.2.symm

lemma sbtw.mem_image_Ioo {x y z : P} (h : sbtw R x y z) :
  y ∈ line_map x z '' (set.Ioo (0 : R) 1) :=
begin
  rcases h with ⟨⟨t, ht, rfl⟩, hyx, hyz⟩,
  rcases set.eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl|rfl|ho,
  { exfalso, simpa using hyx },
  { exfalso, simpa using hyz },
  { exact ⟨t, ho, rfl⟩ }
end

lemma wbtw.mem_affine_span {x y z : P} (h : wbtw R x y z) : y ∈ line[R, x, z] :=
begin
  rcases h with ⟨r, ⟨-, rfl⟩⟩,
  exact line_map_mem_affine_span_pair _ _ _
end

lemma wbtw_comm {x y z : P} : wbtw R x y z ↔ wbtw R z y x :=
by rw [wbtw, wbtw, affine_segment_comm]

alias wbtw_comm ↔ wbtw.symm _

lemma sbtw_comm {x y z : P} : sbtw R x y z ↔ sbtw R z y x :=
by rw [sbtw, sbtw, wbtw_comm, ←and_assoc, ←and_assoc, and.right_comm]

alias sbtw_comm ↔ sbtw.symm _

variables (R)

@[simp] lemma wbtw_self_left (x y : P) : wbtw R x x y :=
left_mem_affine_segment _ _ _

@[simp] lemma wbtw_self_right (x y : P) : wbtw R x y y :=
right_mem_affine_segment _ _ _

@[simp] lemma wbtw_self_iff {x y : P} : wbtw R x y x ↔ y = x :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { simpa [wbtw, affine_segment] using h },
  { rw h,
    exact wbtw_self_left R x x }
end

@[simp] lemma not_sbtw_self_left (x y : P) : ¬ sbtw R x x y :=
λ h, h.ne_left rfl

@[simp] lemma not_sbtw_self_right (x y : P) : ¬ sbtw R x y y :=
λ h, h.ne_right rfl

variables {R}

lemma wbtw.left_ne_right_of_ne_left {x y z : P} (h : wbtw R x y z) (hne : y ≠ x) : x ≠ z :=
begin
  rintro rfl,
  rw wbtw_self_iff at h,
  exact hne h
end

lemma wbtw.left_ne_right_of_ne_right {x y z : P} (h : wbtw R x y z) (hne : y ≠ z) : x ≠ z :=
begin
  rintro rfl,
  rw wbtw_self_iff at h,
  exact hne h
end

lemma sbtw.left_ne_right {x y z : P} (h : sbtw R x y z) : x ≠ z :=
h.wbtw.left_ne_right_of_ne_left h.2.1

lemma sbtw_iff_mem_image_Ioo_and_ne [no_zero_smul_divisors R V] {x y z : P} :
  sbtw R x y z ↔ y ∈ line_map x z '' (set.Ioo (0 : R) 1) ∧ x ≠ z :=
begin
  refine ⟨λ h, ⟨h.mem_image_Ioo, h.left_ne_right⟩, λ h, _⟩,
  rcases h with ⟨⟨t, ht, rfl⟩, hxz⟩,
  refine ⟨⟨t, set.mem_Icc_of_Ioo ht, rfl⟩, _⟩,
  rw [line_map_apply, ←@vsub_ne_zero V, ←@vsub_ne_zero V _ _ _ _ z, vadd_vsub_assoc,
      vadd_vsub_assoc, ←neg_vsub_eq_vsub_rev z x, ←@neg_one_smul R, ←add_smul,
      ←sub_eq_add_neg],
  simp [smul_ne_zero, hxz.symm, sub_eq_zero, ht.1.ne.symm, ht.2.ne]
end

variables (R)

@[simp] lemma not_sbtw_self (x y : P) : ¬ sbtw R x y x :=
λ h, h.left_ne_right rfl

lemma wbtw_swap_left_iff [no_zero_smul_divisors R V] {x y : P} (z : P) :
  (wbtw R x y z ∧ wbtw R y x z) ↔ x = y :=
begin
  split,
  { rintro ⟨hxyz, hyxz⟩,
    rcases hxyz with ⟨ty, hty, rfl⟩,
    rcases hyxz with ⟨tx, htx, hx⟩,
    simp_rw [line_map_apply, ←add_vadd] at hx,
    rw [←@vsub_eq_zero_iff_eq V, vadd_vsub, vsub_vadd_eq_vsub_sub, smul_sub, smul_smul,
        ←sub_smul, ←add_smul, smul_eq_zero] at hx,
    rcases hx with h|h,
    { nth_rewrite 0 ←mul_one tx at h,
      rw [←mul_sub, add_eq_zero_iff_neg_eq] at h,
      have h' : ty = 0,
      { refine le_antisymm _ hty.1,
        rw [←h, left.neg_nonpos_iff],
        exact mul_nonneg htx.1 (sub_nonneg.2 hty.2) },
      simp [h'] },
    { rw vsub_eq_zero_iff_eq at h,
      simp [h] } },
  { rintro rfl,
    exact ⟨wbtw_self_left _ _ _, wbtw_self_left _ _ _⟩ }
end

lemma wbtw_swap_right_iff [no_zero_smul_divisors R V] (x : P) {y z : P} :
  (wbtw R x y z ∧ wbtw R x z y) ↔ y = z :=
begin
  nth_rewrite 0 wbtw_comm,
  nth_rewrite 1 wbtw_comm,
  rw eq_comm,
  exact wbtw_swap_left_iff R x
end

lemma wbtw_rotate_iff [no_zero_smul_divisors R V] (x : P) {y z : P} :
  (wbtw R x y z ∧ wbtw R z x y) ↔ x = y :=
by rw [wbtw_comm, wbtw_swap_right_iff, eq_comm]

variables {R}

lemma wbtw.swap_left_iff [no_zero_smul_divisors R V] {x y z : P} (h : wbtw R x y z) :
  wbtw R y x z ↔ x = y :=
by rw [←wbtw_swap_left_iff R z, and_iff_right h]

lemma wbtw.swap_right_iff [no_zero_smul_divisors R V] {x y z : P} (h : wbtw R x y z) :
  wbtw R x z y ↔ y = z :=
by rw [←wbtw_swap_right_iff R x, and_iff_right h]

lemma wbtw.rotate_iff [no_zero_smul_divisors R V] {x y z : P} (h : wbtw R x y z) :
  wbtw R z x y ↔ x = y :=
by rw [←wbtw_rotate_iff R x, and_iff_right h]

lemma sbtw.not_swap_left [no_zero_smul_divisors R V] {x y z : P} (h : sbtw R x y z) :
  ¬ wbtw R y x z :=
λ hs, h.left_ne (h.wbtw.swap_left_iff.1 hs)

lemma sbtw.not_swap_right [no_zero_smul_divisors R V] {x y z : P} (h : sbtw R x y z) :
  ¬ wbtw R x z y :=
λ hs, h.ne_right (h.wbtw.swap_right_iff.1 hs)

lemma sbtw.not_rotate [no_zero_smul_divisors R V] {x y z : P} (h : sbtw R x y z) :
  ¬ wbtw R z x y :=
λ hs, h.left_ne (h.wbtw.rotate_iff.1 hs)

@[simp] lemma wbtw_line_map_iff [no_zero_smul_divisors R V] {x y : P} {r : R} :
  wbtw R x (line_map x y r) y ↔ x = y ∨ r ∈ set.Icc (0 : R) 1 :=
begin
  by_cases hxy : x = y, { simp [hxy] },
  rw [or_iff_right hxy, wbtw, affine_segment, (line_map_injective R hxy).mem_set_image]
end

@[simp] lemma sbtw_line_map_iff [no_zero_smul_divisors R V] {x y : P} {r : R} :
  sbtw R x (line_map x y r) y ↔ x ≠ y ∧ r ∈ set.Ioo (0 : R) 1 :=
begin
  rw [sbtw_iff_mem_image_Ioo_and_ne, and_comm, and_congr_right],
  intro hxy,
  rw (line_map_injective R hxy).mem_set_image
end

omit V

@[simp] lemma wbtw_mul_sub_add_iff [no_zero_divisors R] {x y r : R} :
  wbtw R x (r * (y - x) + x) y ↔ x = y ∨ r ∈ set.Icc (0 : R) 1 :=
wbtw_line_map_iff

@[simp] lemma sbtw_mul_sub_add_iff [no_zero_divisors R] {x y r : R} :
  sbtw R x (r * (y - x) + x) y ↔ x ≠ y ∧ r ∈ set.Ioo (0 : R) 1 :=
sbtw_line_map_iff

@[simp] lemma wbtw_zero_one_iff {x : R} : wbtw R 0 x 1 ↔ x ∈ set.Icc (0 : R) 1 :=
begin
  simp_rw [wbtw, affine_segment, set.mem_image, line_map_apply_ring],
  simp
end

@[simp] lemma wbtw_one_zero_iff {x : R} : wbtw R 1 x 0 ↔ x ∈ set.Icc (0 : R) 1 :=
by rw [wbtw_comm, wbtw_zero_one_iff]

@[simp] lemma sbtw_zero_one_iff {x : R} : sbtw R 0 x 1 ↔ x ∈ set.Ioo (0 : R) 1 :=
begin
  rw [sbtw, wbtw_zero_one_iff, set.mem_Icc, set.mem_Ioo],
  exact ⟨λ h, ⟨h.1.1.lt_of_ne (ne.symm h.2.1), h.1.2.lt_of_ne h.2.2⟩,
         λ h, ⟨⟨h.1.le, h.2.le⟩, h.1.ne', h.2.ne⟩⟩
end

@[simp] lemma sbtw_one_zero_iff {x : R} : sbtw R 1 x 0 ↔ x ∈ set.Ioo (0 : R) 1 :=
by rw [sbtw_comm, sbtw_zero_one_iff]

include V

lemma wbtw.trans_left {w x y z : P} (h₁ : wbtw R w y z) (h₂ : wbtw R w x y) : wbtw R w x z :=
begin
  rcases h₁ with ⟨t₁, ht₁, rfl⟩,
  rcases h₂ with ⟨t₂, ht₂, rfl⟩,
  refine ⟨t₂ * t₁, ⟨mul_nonneg ht₂.1 ht₁.1, mul_le_one ht₂.2 ht₁.1 ht₁.2⟩, _⟩,
  simp [line_map_apply, smul_smul]
end

lemma wbtw.trans_right {w x y z : P} (h₁ : wbtw R w x z) (h₂ : wbtw R x y z) : wbtw R w y z :=
begin
  rw wbtw_comm at *,
  exact h₁.trans_left h₂
end

lemma wbtw.trans_sbtw_left [no_zero_smul_divisors R V] {w x y z : P} (h₁ : wbtw R w y z)
  (h₂ : sbtw R w x y) : sbtw R w x z :=
begin
  refine ⟨h₁.trans_left h₂.wbtw, h₂.ne_left, _⟩,
  rintro rfl,
  exact h₂.right_ne ((wbtw_swap_right_iff R w).1 ⟨h₁, h₂.wbtw⟩)
end

lemma wbtw.trans_sbtw_right [no_zero_smul_divisors R V] {w x y z : P} (h₁ : wbtw R w x z)
  (h₂ : sbtw R x y z) : sbtw R w y z :=
begin
  rw wbtw_comm at *,
  rw sbtw_comm at *,
  exact h₁.trans_sbtw_left h₂
end

lemma sbtw.trans_left [no_zero_smul_divisors R V] {w x y z : P} (h₁ : sbtw R w y z)
  (h₂ : sbtw R w x y) : sbtw R w x z :=
h₁.wbtw.trans_sbtw_left h₂

lemma sbtw.trans_right [no_zero_smul_divisors R V] {w x y z : P} (h₁ : sbtw R w x z)
  (h₂ : sbtw R x y z) : sbtw R w y z :=
h₁.wbtw.trans_sbtw_right h₂

lemma wbtw.trans_left_ne [no_zero_smul_divisors R V] {w x y z : P} (h₁ : wbtw R w y z)
  (h₂ : wbtw R w x y) (h : y ≠ z) : x ≠ z :=
begin
  rintro rfl,
  exact h (h₁.swap_right_iff.1 h₂)
end

lemma wbtw.trans_right_ne [no_zero_smul_divisors R V] {w x y z : P} (h₁ : wbtw R w x z)
  (h₂ : wbtw R x y z) (h : w ≠ x) : w ≠ y :=
begin
  rintro rfl,
  exact h (h₁.swap_left_iff.1 h₂)
end

lemma sbtw.trans_wbtw_left_ne [no_zero_smul_divisors R V] {w x y z : P} (h₁ : sbtw R w y z)
  (h₂ : wbtw R w x y) : x ≠ z :=
h₁.wbtw.trans_left_ne h₂ h₁.ne_right

lemma sbtw.trans_wbtw_right_ne [no_zero_smul_divisors R V] {w x y z : P} (h₁ : sbtw R w x z)
  (h₂ : wbtw R x y z) : w ≠ y :=
h₁.wbtw.trans_right_ne h₂ h₁.left_ne

/- Calls to `affine_combination` are slow to elaborate (generally, not just for this lemma), and
without the use of `@finset.affine_combination R V _ _ _ _ _ _` for at least three of the six
calls in this lemma statement, elaboration of the statement times out (even if the proof is
replaced by `sorry`). -/
lemma sbtw.affine_combination_of_mem_affine_span_pair [no_zero_divisors R]
  [no_zero_smul_divisors R V] {ι : Type*} {p : ι → P} (ha : affine_independent R p)
  {w w₁ w₂ : ι → R} {s : finset ι} (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1)
  (hw₂ : ∑ i in s, w₂ i = 1)
  (h : s.affine_combination p w ∈
    line[R, s.affine_combination p w₁, s.affine_combination p w₂]) {i : ι} (his : i ∈ s)
  (hs : sbtw R (w₁ i) (w i) (w₂ i)) :
  sbtw R (@finset.affine_combination R V _ _ _ _ _ _ s p w₁)
    (@finset.affine_combination R V _ _ _ _ _ _ s p w)
    (@finset.affine_combination R V _ _ _ _ _ _ s p w₂) :=
begin
  rw affine_combination_mem_affine_span_pair ha hw hw₁ hw₂ at h,
  rcases h with ⟨r, hr⟩,
  dsimp only at hr,
  rw [hr i his, sbtw_mul_sub_add_iff] at hs,
  change ∀ i ∈ s, w i = ((r • (w₂ - w₁) + w₁) i) at hr,
  rw s.affine_combination_congr hr (λ _ _, rfl),
  dsimp only,
  rw [←s.weighted_vsub_vadd_affine_combination, s.weighted_vsub_const_smul,
      ←s.affine_combination_vsub, ←line_map_apply, sbtw_line_map_iff, and_iff_left hs.2,
      ←@vsub_ne_zero V, s.affine_combination_vsub],
  intro hz,
  have hw₁w₂ : ∑ i in s, (w₁ - w₂) i = 0,
  { simp_rw [pi.sub_apply, finset.sum_sub_distrib, hw₁, hw₂, sub_self] },
  refine hs.1 _,
  have ha' := ha s (w₁ - w₂) hw₁w₂ hz i his,
  rwa [pi.sub_apply, sub_eq_zero] at ha'
end

end ordered_ring

section strict_ordered_comm_ring
variables [strict_ordered_comm_ring R] [add_comm_group V] [module R V] [add_torsor V P]

include V

variables {R}

lemma wbtw.same_ray_vsub {x y z : P} (h : wbtw R x y z) : same_ray R (y -ᵥ x) (z -ᵥ y) :=
begin
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩,
  simp_rw line_map_apply,
  rcases ht0.lt_or_eq with ht0' | rfl, swap, { simp },
  rcases ht1.lt_or_eq with ht1' | rfl, swap, { simp },
  refine or.inr (or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', _⟩),
  simp [vsub_vadd_eq_vsub_sub, smul_sub, smul_smul, ←sub_smul],
  ring_nf
end

lemma wbtw.same_ray_vsub_left {x y z : P} (h : wbtw R x y z) : same_ray R (y -ᵥ x) (z -ᵥ x) :=
begin
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩,
  simpa [line_map_apply] using same_ray_nonneg_smul_left (z -ᵥ x) ht0
end

lemma wbtw.same_ray_vsub_right {x y z : P} (h : wbtw R x y z) : same_ray R (z -ᵥ x) (z -ᵥ y) :=
begin
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩,
  simpa [line_map_apply, vsub_vadd_eq_vsub_sub, sub_smul] using
    same_ray_nonneg_smul_right (z -ᵥ x) (sub_nonneg.2 ht1)
end

end strict_ordered_comm_ring

section linear_ordered_ring

variables [linear_ordered_ring R] [add_comm_group V] [module R V] [add_torsor V P]

include V

variables {R}

/-- Suppose lines from two vertices of a triangle to interior points of the opposite side meet at
`p`. Then `p` lies in the interior of the first (and by symmetry the other) segment from a
vertex to the point on the opposite side. -/
lemma sbtw_of_sbtw_of_sbtw_of_mem_affine_span_pair [no_zero_smul_divisors R V]
  {t : affine.triangle R P} {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂) {p₁ p₂ p : P}
  (h₁ : sbtw R (t.points i₂) p₁ (t.points i₃)) (h₂ : sbtw R (t.points i₁) p₂ (t.points i₃))
  (h₁' : p ∈ line[R, t.points i₁, p₁]) (h₂' : p ∈ line[R, t.points i₂, p₂]) :
  sbtw R (t.points i₁) p p₁ :=
begin
  -- Should not be needed; see comments on local instances in `data.sign`.
  letI : decidable_rel ((<) : R → R → Prop) := linear_ordered_ring.decidable_lt,
  have h₁₃ : i₁ ≠ i₃, { rintro rfl, simpa using h₂ },
  have h₂₃ : i₂ ≠ i₃, { rintro rfl, simpa using h₁ },
  have h3 : ∀ i : fin 3, i = i₁ ∨ i = i₂ ∨ i = i₃, { clear h₁ h₂ h₁' h₂', dec_trivial! },
  have hu : (finset.univ : finset (fin 3)) = {i₁, i₂, i₃}, { clear h₁ h₂ h₁' h₂', dec_trivial! },
  have hp : p ∈ affine_span R (set.range t.points),
  { have hle : line[R, t.points i₁, p₁] ≤ affine_span R (set.range t.points),
    { refine affine_span_pair_le_of_mem_of_mem (mem_affine_span _ (set.mem_range_self _)) _,
      have hle : line[R, t.points i₂, t.points i₃] ≤ affine_span R (set.range t.points),
      { refine affine_span_mono _ _, simp [set.insert_subset] },
      rw affine_subspace.le_def' at hle,
      exact hle _ h₁.wbtw.mem_affine_span },
    rw affine_subspace.le_def' at hle,
    exact hle _ h₁' },
  have h₁i := h₁.mem_image_Ioo,
  have h₂i := h₂.mem_image_Ioo,
  rw set.mem_image at h₁i h₂i,
  rcases h₁i with ⟨r₁, ⟨hr₁0, hr₁1⟩, rfl⟩,
  rcases h₂i with ⟨r₂, ⟨hr₂0, hr₂1⟩, rfl⟩,
  rcases eq_affine_combination_of_mem_affine_span_of_fintype hp with ⟨w, hw, rfl⟩,
  have h₁s := sign_eq_of_affine_combination_mem_affine_span_single_line_map t.independent hw
    (finset.mem_univ _) (finset.mem_univ _) (finset.mem_univ _) h₁₂ h₁₃ h₂₃ hr₁0 hr₁1 h₁',
  have h₂s := sign_eq_of_affine_combination_mem_affine_span_single_line_map t.independent hw
    (finset.mem_univ _) (finset.mem_univ _) (finset.mem_univ _) h₁₂.symm h₂₃ h₁₃ hr₂0 hr₂1 h₂',
  dsimp only at h₁s h₂s,
  rw [←finset.univ.affine_combination_affine_combination_single_weights R t.points
        (finset.mem_univ i₁),
      ←finset.univ.affine_combination_affine_combination_line_map_weights t.points
        (finset.mem_univ _) (finset.mem_univ _)] at ⊢ h₁',
  refine sbtw.affine_combination_of_mem_affine_span_pair t.independent hw
    (finset.univ.sum_affine_combination_single_weights R (finset.mem_univ _))
    (finset.univ.sum_affine_combination_line_map_weights (finset.mem_univ _) (finset.mem_univ _) _)
    h₁' (finset.mem_univ i₁) _,
  rw [finset.affine_combination_single_weights_apply_self,
      finset.affine_combination_line_map_weights_apply_of_ne h₁₂ h₁₃, sbtw_one_zero_iff],
  have hs : ∀ i : fin 3, sign (w i) = sign (w i₃),
  { intro i,
    rcases h3 i with rfl | rfl | rfl,
    { exact h₂s },
    { exact h₁s },
    { refl } },
  have hss : sign (∑ i, w i) = 1, { simp [hw] },
  have hs' := sign_sum (finset.univ_nonempty) (sign (w i₃)) (λ i _, hs i),
  rw hs' at hss,
  simp_rw [hss, sign_eq_one_iff] at hs,
  refine ⟨hs i₁, _⟩,
  rw hu at hw,
  rw [finset.sum_insert, finset.sum_insert, finset.sum_singleton] at hw,
  { by_contra hle,
    rw not_lt at hle,
    exact (hle.trans_lt (lt_add_of_pos_right _ (left.add_pos (hs i₂) (hs i₃)))).ne' hw },
  { simp [h₂₃] },
  { simp [h₁₂, h₁₃] }
end

end linear_ordered_ring

section linear_ordered_field

variables [linear_ordered_field R] [add_comm_group V] [module R V] [add_torsor V P]

include V

variables {R}

lemma wbtw_iff_left_eq_or_right_mem_image_Ici {x y z : P} :
  wbtw R x y z ↔ x = y ∨ z ∈ line_map x y '' (set.Ici (1 : R)) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩,
    rcases hr0.lt_or_eq with hr0' | rfl,
    { rw set.mem_image,
      refine or.inr ⟨r⁻¹, one_le_inv hr0' hr1, _⟩,
      simp only [line_map_apply, smul_smul, vadd_vsub],
      rw [inv_mul_cancel hr0'.ne', one_smul, vsub_vadd] },
    { simp } },
  { rcases h with rfl | ⟨r, ⟨hr, rfl⟩⟩,
    { exact wbtw_self_left _ _ _ },
    { rw set.mem_Ici at hr,
      refine ⟨r⁻¹, ⟨inv_nonneg.2 (zero_le_one.trans hr), inv_le_one hr⟩, _⟩,
      simp only [line_map_apply, smul_smul, vadd_vsub],
      rw [inv_mul_cancel (one_pos.trans_le hr).ne', one_smul, vsub_vadd] } }
end

lemma wbtw.right_mem_image_Ici_of_left_ne {x y z : P} (h : wbtw R x y z) (hne : x ≠ y) :
  z ∈ line_map x y '' (set.Ici (1 : R)) :=
(wbtw_iff_left_eq_or_right_mem_image_Ici.1 h).resolve_left hne

lemma wbtw.right_mem_affine_span_of_left_ne {x y z : P} (h : wbtw R x y z) (hne : x ≠ y) :
  z ∈ line[R, x, y] :=
begin
  rcases h.right_mem_image_Ici_of_left_ne hne with ⟨r, ⟨-, rfl⟩⟩,
  exact line_map_mem_affine_span_pair _ _ _
end

lemma sbtw_iff_left_ne_and_right_mem_image_IoI {x y z : P} :
  sbtw R x y z ↔ x ≠ y ∧ z ∈ line_map x y '' (set.Ioi (1 : R)) :=
begin
  refine ⟨λ h, ⟨h.left_ne, _⟩, λ h, _⟩,
  { obtain ⟨r, ⟨hr, rfl⟩⟩ := h.wbtw.right_mem_image_Ici_of_left_ne h.left_ne,
    rw [set.mem_Ici] at hr,
    rcases hr.lt_or_eq with hrlt | rfl,
    { exact set.mem_image_of_mem _ hrlt },
    { exfalso, simpa using h } },
  { rcases h with ⟨hne, r, hr, rfl⟩,
    rw set.mem_Ioi at hr,
    refine ⟨wbtw_iff_left_eq_or_right_mem_image_Ici.2 (or.inr (set.mem_image_of_mem _
      (set.mem_of_mem_of_subset hr set.Ioi_subset_Ici_self))), hne.symm, _⟩,
    rw [line_map_apply, ←@vsub_ne_zero V, vsub_vadd_eq_vsub_sub],
    nth_rewrite 0 ←one_smul R (y -ᵥ x),
    rw [←sub_smul, smul_ne_zero_iff, vsub_ne_zero, sub_ne_zero],
    exact ⟨hr.ne, hne.symm⟩ }
end

lemma sbtw.right_mem_image_Ioi {x y z : P} (h : sbtw R x y z) :
  z ∈ line_map x y '' (set.Ioi (1 : R)) :=
(sbtw_iff_left_ne_and_right_mem_image_IoI.1 h).2

lemma sbtw.right_mem_affine_span {x y z : P} (h : sbtw R x y z) : z ∈ line[R, x, y] :=
h.wbtw.right_mem_affine_span_of_left_ne h.left_ne

lemma wbtw_iff_right_eq_or_left_mem_image_Ici {x y z : P} :
  wbtw R x y z ↔ z = y ∨ x ∈ line_map z y '' (set.Ici (1 : R)) :=
by rw [wbtw_comm, wbtw_iff_left_eq_or_right_mem_image_Ici]

lemma wbtw.left_mem_image_Ici_of_right_ne {x y z : P} (h : wbtw R x y z) (hne : z ≠ y) :
  x ∈ line_map z y '' (set.Ici (1 : R)) :=
h.symm.right_mem_image_Ici_of_left_ne hne

lemma wbtw.left_mem_affine_span_of_right_ne {x y z : P} (h : wbtw R x y z) (hne : z ≠ y) :
  x ∈ line[R, z, y] :=
h.symm.right_mem_affine_span_of_left_ne hne

lemma sbtw_iff_right_ne_and_left_mem_image_IoI {x y z : P} :
  sbtw R x y z ↔ z ≠ y ∧ x ∈ line_map z y '' (set.Ioi (1 : R)) :=
by rw [sbtw_comm, sbtw_iff_left_ne_and_right_mem_image_IoI]

lemma sbtw.left_mem_image_Ioi {x y z : P} (h : sbtw R x y z) :
  x ∈ line_map z y '' (set.Ioi (1 : R)) :=
h.symm.right_mem_image_Ioi

lemma sbtw.left_mem_affine_span {x y z : P} (h : sbtw R x y z) : x ∈ line[R, z, y] :=
h.symm.right_mem_affine_span

lemma wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁)
  (hr₂ : r₁ ≤ r₂) : wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) :=
begin
  refine ⟨r₁ / r₂, ⟨div_nonneg hr₁ (hr₁.trans hr₂), div_le_one_of_le hr₂ (hr₁.trans hr₂)⟩, _⟩,
  by_cases h : r₁ = 0, { simp [h] },
  simp [line_map_apply, smul_smul, ((hr₁.lt_of_ne' h).trans_le hr₂).ne.symm]
end

lemma wbtw_or_wbtw_smul_vadd_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
  wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) :=
begin
  rcases le_total r₁ r₂ with h|h,
  { exact or.inl (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₁ h) },
  { exact or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₂ h) }
end

lemma wbtw_smul_vadd_smul_vadd_of_nonpos_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0)
  (hr₂ : r₂ ≤ r₁) : wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) :=
begin
  convert wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x (-v) (left.nonneg_neg_iff.2 hr₁)
                                                     (neg_le_neg_iff.2 hr₂) using 1;
    rw neg_smul_neg
end

lemma wbtw_or_wbtw_smul_vadd_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0) (hr₂ : r₂ ≤ 0) :
  wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) :=
begin
  rcases le_total r₁ r₂ with h|h,
  { exact or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₂ h) },
  { exact or.inl (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₁ h) }
end

lemma wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0)
  (hr₂ : 0 ≤ r₂) : wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) :=
begin
  convert wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (r₁ • v +ᵥ x) v (left.nonneg_neg_iff.2 hr₁)
    (neg_le_sub_iff_le_add.2 ((le_add_iff_nonneg_left r₁).2 hr₂)) using 1;
    simp [sub_smul, ←add_vadd]
end

lemma wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁)
  (hr₂ : r₂ ≤ 0) : wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) :=
begin
  rw wbtw_comm,
  exact wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg x v hr₂ hr₁
end

lemma wbtw.trans_left_right {w x y z : P} (h₁ : wbtw R w y z) (h₂ : wbtw R w x y) : wbtw R x y z :=
begin
  rcases h₁ with ⟨t₁, ht₁, rfl⟩,
  rcases h₂ with ⟨t₂, ht₂, rfl⟩,
  refine ⟨(t₁ - t₂ * t₁) / (1 - t₂ * t₁),
          ⟨div_nonneg (sub_nonneg.2 (mul_le_of_le_one_left ht₁.1 ht₂.2))
                      (sub_nonneg.2 (mul_le_one ht₂.2 ht₁.1 ht₁.2)),
           div_le_one_of_le (sub_le_sub_right ht₁.2 _)
                            (sub_nonneg.2 (mul_le_one ht₂.2 ht₁.1 ht₁.2))⟩, _⟩,
  simp only [line_map_apply, smul_smul, ←add_vadd, vsub_vadd_eq_vsub_sub, smul_sub, ←sub_smul,
             ←add_smul, vadd_vsub, vadd_right_cancel_iff, div_mul_eq_mul_div, div_sub_div_same],
  nth_rewrite 0 [←mul_one (t₁ - t₂ * t₁)],
  rw [←mul_sub, mul_div_assoc],
  by_cases h : 1 - t₂ * t₁ = 0,
  { rw [sub_eq_zero, eq_comm] at h,
    rw h,
    suffices : t₁ = 1, by simp [this],
    exact eq_of_le_of_not_lt ht₁.2
      (λ ht₁lt, (mul_lt_one_of_nonneg_of_lt_one_right ht₂.2 ht₁.1 ht₁lt).ne h) },
  { rw div_self h,
    ring_nf }
end

lemma wbtw.trans_right_left {w x y z : P} (h₁ : wbtw R w x z) (h₂ : wbtw R x y z) : wbtw R w x y :=
begin
  rw wbtw_comm at *,
  exact h₁.trans_left_right h₂
end

lemma sbtw.trans_left_right {w x y z : P} (h₁ : sbtw R w y z) (h₂ : sbtw R w x y) : sbtw R x y z :=
⟨h₁.wbtw.trans_left_right h₂.wbtw, h₂.right_ne, h₁.ne_right⟩

lemma sbtw.trans_right_left {w x y z : P} (h₁ : sbtw R w x z) (h₂ : sbtw R x y z) : sbtw R w x y :=
⟨h₁.wbtw.trans_right_left h₂.wbtw, h₁.ne_left, h₂.left_ne⟩

lemma wbtw.collinear {x y z : P} (h : wbtw R x y z) : collinear R ({x, y, z} : set P) :=
begin
  rw collinear_iff_exists_forall_eq_smul_vadd,
  refine ⟨x, z -ᵥ x, _⟩,
  intros p hp,
  simp_rw [set.mem_insert_iff, set.mem_singleton_iff] at hp,
  rcases hp with rfl|rfl|rfl,
  { refine ⟨0, _⟩, simp },
  { rcases h with ⟨t, -, rfl⟩,
    exact ⟨t, rfl⟩ },
  { refine ⟨1, _⟩, simp }
end

lemma collinear.wbtw_or_wbtw_or_wbtw {x y z : P} (h : collinear R ({x, y, z} : set P)) :
  wbtw R x y z ∨ wbtw R y z x ∨ wbtw R z x y :=
begin
  rw collinear_iff_of_mem (set.mem_insert _ _) at h,
  rcases h with ⟨v, h⟩,
  simp_rw [set.mem_insert_iff, set.mem_singleton_iff] at h,
  have hy := h y (or.inr (or.inl rfl)),
  have hz := h z (or.inr (or.inr rfl)),
  rcases hy with ⟨ty, rfl⟩,
  rcases hz with ⟨tz, rfl⟩,
  rcases lt_trichotomy ty 0 with hy0|rfl|hy0,
  { rcases lt_trichotomy tz 0 with hz0|rfl|hz0,
    { nth_rewrite 1 wbtw_comm,
      rw ←or_assoc,
      exact or.inl (wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hy0.le hz0.le) },
    { simp },
    { exact or.inr (or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos _ _ hz0.le hy0.le)) } },
  { simp },
  { rcases lt_trichotomy tz 0 with hz0|rfl|hz0,
    { refine or.inr (or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg _ _ hz0.le hy0.le)) },
    { simp },
    { nth_rewrite 1 wbtw_comm,
      rw ←or_assoc,
      exact or.inl (wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hy0.le hz0.le) } }
end

lemma wbtw_iff_same_ray_vsub {x y z : P} : wbtw R x y z ↔ same_ray R (y -ᵥ x) (z -ᵥ y) :=
begin
  refine ⟨wbtw.same_ray_vsub, λ h, _⟩,
  rcases h with h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩,
  { rw vsub_eq_zero_iff_eq at h, simp [h] },
  { rw vsub_eq_zero_iff_eq at h, simp [h] },
  { refine ⟨r₂ / (r₁ + r₂),
            ⟨div_nonneg hr₂.le (add_nonneg hr₁.le hr₂.le),
             div_le_one_of_le (le_add_of_nonneg_left hr₁.le) (add_nonneg hr₁.le hr₂.le)⟩, _⟩,
    have h' : z = r₂⁻¹ • r₁ • (y -ᵥ x) +ᵥ y, { simp [h, hr₂.ne'] },
    rw eq_comm,
    simp only [line_map_apply, h', vadd_vsub_assoc, smul_smul, ←add_smul, eq_vadd_iff_vsub_eq,
               smul_add],
    convert (one_smul _ _).symm,
    field_simp [(add_pos hr₁ hr₂).ne', hr₂.ne'],
    ring }
end

variables (R)

lemma wbtw_point_reflection (x y : P) : wbtw R y x (point_reflection R x y) :=
begin
  refine ⟨2⁻¹, ⟨by norm_num, by norm_num⟩, _⟩,
  rw [line_map_apply, point_reflection_apply, vadd_vsub_assoc, ←two_smul R (x -ᵥ y)],
  simp
end

lemma sbtw_point_reflection_of_ne {x y : P} (h : x ≠ y) : sbtw R y x (point_reflection R x y) :=
begin
  refine ⟨wbtw_point_reflection _ _ _, h, _⟩,
  nth_rewrite 0 [←point_reflection_self R x],
  exact (point_reflection_involutive R x).injective.ne h
end

lemma wbtw_midpoint (x y : P) : wbtw R x (midpoint R x y) y :=
by { convert wbtw_point_reflection R (midpoint R x y) x, simp }

lemma sbtw_midpoint_of_ne {x y : P} (h : x ≠ y) : sbtw R x (midpoint R x y) y :=
begin
  have h : midpoint R x y ≠ x, { simp [h] },
  convert sbtw_point_reflection_of_ne R h,
  simp
end

end linear_ordered_field
