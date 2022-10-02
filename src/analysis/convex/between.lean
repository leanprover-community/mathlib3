/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.convex.segment
import linear_algebra.affine_space.finite_dimensional

/-!
# Betweenness in affine spaces

This file defines notions of a point in an affine space being between two given points, and of
two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `affine_segment R x y`: The segment of points weakly between `x` and `y`.
* `wbtw R x y z`: The point `y` is weakly between `x` and `z`.
* `sbtw R x y z`: The point `y` is strictly between `x` and `z`.
* `s.w_same_side x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.s_same_side x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.w_opp_side x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.s_opp_side x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/

variables (R : Type*) {V V' P P' : Type*}

open affine_map

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

lemma sbtw.left_ne_right {x y z : P} (h : sbtw R x y z) : x ≠ z :=
begin
  rintro rfl,
  rw [sbtw, wbtw_self_iff] at h,
  exact h.2.1 h.1
end

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

end ordered_ring

section linear_ordered_field

variables [linear_ordered_field R] [add_comm_group V] [module R V] [add_torsor V P]

include V

variables {R}

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
  rw collinear_iff_of_mem R (set.mem_insert _ _) at h,
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

end linear_ordered_field

namespace affine_subspace

section ordered_comm_ring

variables [ordered_comm_ring R] [add_comm_group V] [module R V] [add_torsor V P]
variables [add_comm_group V'] [module R V'] [add_torsor V' P']

include V

variables {R}

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
  simp_rw [←linear_map_vsub, (f.injective_iff_linear_injective.2 hf).same_ray_map_iff] at h,
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
  simp_rw [←linear_map_vsub, (f.injective_iff_linear_injective.2 hf).same_ray_map_iff] at h,
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

end ordered_comm_ring

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

end linear_ordered_field

end affine_subspace
