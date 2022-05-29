/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import algebra.order.invertible
import algebra.order.module
import linear_algebra.affine_space.midpoint
import linear_algebra.affine_space.affine_subspace
import linear_algebra.ray

/-!
# Convex sets and functions in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `open_segment 𝕜 x y`: Open segment joining `x` and `y`.
* `convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.
* `std_simplex 𝕜 ι`: The standard simplex in `ι → 𝕜` (currently requires `fintype ι`). It is the
  intersection of the positive quadrant with the hyperplane `s.sum = 1`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex.

## Notations

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in locale `convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `open_segment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopen_segment`/`convex.Ico`/`convex.Ioc`?
-/

variables {𝕜 E F β : Type*}

open linear_map set
open_locale big_operators classical pointwise

/-! ### Segment -/

section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_monoid E]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E]

/-- Segments in a vector space. -/
def segment (x y : E) : set E :=
{z : E | ∃ (a b : 𝕜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), a • x + b • y = z}

/-- Open segment in a vector space. Note that `open_segment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def open_segment (x y : E) : set E :=
{z : E | ∃ (a b : 𝕜) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1), a • x + b • y = z}

localized "notation `[` x ` -[` 𝕜 `] ` y `]` := segment 𝕜 x y" in convex

lemma segment_eq_image₂ (x y : E) :
  [x -[𝕜] y] = (λ p : 𝕜 × 𝕜, p.1 • x + p.2 • y) '' {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} :=
by simp only [segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

lemma open_segment_eq_image₂ (x y : E) :
  open_segment 𝕜 x y =
    (λ p : 𝕜 × 𝕜, p.1 • x + p.2 • y) '' {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1} :=
by simp only [open_segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

lemma segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x] :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma open_segment_symm (x y : E) :
  open_segment 𝕜 x y = open_segment 𝕜 y x :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma open_segment_subset_segment (x y : E) :
  open_segment 𝕜 x y ⊆ [x -[𝕜] y] :=
λ z ⟨a, b, ha, hb, hab, hz⟩, ⟨a, b, ha.le, hb.le, hab, hz⟩

lemma segment_subset_iff {x y : E} {s : set E} :
  [x -[𝕜] y] ⊆ s ↔ ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s :=
⟨λ H a b ha hb hab, H ⟨a, b, ha, hb, hab, rfl⟩,
  λ H z ⟨a, b, ha, hb, hab, hz⟩, hz ▸ H a b ha hb hab⟩

lemma open_segment_subset_iff {x y : E} {s : set E} :
  open_segment 𝕜 x y ⊆ s ↔ ∀ a b : 𝕜, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
⟨λ H a b ha hb hab, H ⟨a, b, ha, hb, hab, rfl⟩,
  λ H z ⟨a, b, ha, hb, hab, hz⟩, hz ▸ H a b ha hb hab⟩

end has_scalar

open_locale convex

section mul_action_with_zero
variables (𝕜) [mul_action_with_zero 𝕜 E]

lemma left_mem_segment (x y : E) : x ∈ [x -[𝕜] y] :=
⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

lemma right_mem_segment (x y : E) : y ∈ [x -[𝕜] y] :=
segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

end mul_action_with_zero

section module
variables (𝕜) [module 𝕜 E] {x y z : E} {s : set E}

@[simp] lemma segment_same (x : E) : [x -[𝕜] x] = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
  λ h, mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩

lemma insert_endpoints_open_segment (x y : E) :
  insert x (insert y (open_segment 𝕜 x y)) = [x -[𝕜] y] :=
begin
  simp only [subset_antisymm_iff, insert_subset, left_mem_segment, right_mem_segment,
    open_segment_subset_segment, true_and],
  rintro z ⟨a, b, ha, hb, hab, rfl⟩,
  refine hb.eq_or_gt.imp _ (λ hb', ha.eq_or_gt.imp _ _),
  { rintro rfl,
    rw add_zero at hab,
    rw [hab, one_smul, zero_smul, add_zero] },
  { rintro rfl,
    rw zero_add at hab,
    rw [hab, one_smul, zero_smul, zero_add] },
  { exact λ ha', ⟨a, b, ha', hb', hab, rfl⟩ }
end

variables {𝕜}

lemma mem_open_segment_of_ne_left_right (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ [x -[𝕜] y]) :
  z ∈ open_segment 𝕜 x y :=
begin
  rw [← insert_endpoints_open_segment] at hz,
  exact ((hz.resolve_left hx.symm).resolve_left hy.symm)
end

lemma open_segment_subset_iff_segment_subset (hx : x ∈ s) (hy : y ∈ s) :
  open_segment 𝕜 x y ⊆ s ↔ [x -[𝕜] y] ⊆ s :=
by simp only [← insert_endpoints_open_segment, insert_subset, *, true_and]

end module
end ordered_semiring

open_locale convex

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_group
variables (𝕜) [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F]

section densely_ordered
variables [nontrivial 𝕜] [densely_ordered 𝕜]

@[simp] lemma open_segment_same (x : E) :
  open_segment 𝕜 x x = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
  λ (h : z = x), begin
    obtain ⟨a, ha₀, ha₁⟩ := densely_ordered.dense (0 : 𝕜) 1 zero_lt_one,
    refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel'_right _ _, _⟩,
    rw [←add_smul, add_sub_cancel'_right, one_smul, h],
  end⟩

end densely_ordered

lemma segment_eq_image (x y : E) : [x -[𝕜] y] = (λ θ : 𝕜, (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1 :=
set.ext $ λ z,
  ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
    ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel]⟩,
    λ ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩, ⟨1-θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

lemma open_segment_eq_image (x y : E) :
  open_segment 𝕜 x y = (λ (θ : 𝕜), (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1 :=
set.ext $ λ z,
  ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
    ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel]⟩,
    λ ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩, ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

lemma segment_eq_image' (x y : E) :
  [x -[𝕜] y] = (λ (θ : 𝕜), x + θ • (y - x)) '' Icc (0 : 𝕜) 1 :=
by { convert segment_eq_image 𝕜 x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma open_segment_eq_image' (x y : E) :
  open_segment 𝕜 x y = (λ (θ : 𝕜), x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 :=
by { convert open_segment_eq_image 𝕜 x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma segment_eq_image_line_map (x y : E) :
  [x -[𝕜] y] = affine_map.line_map x y '' Icc (0 : 𝕜) 1 :=
by { convert segment_eq_image 𝕜 x y, ext, exact affine_map.line_map_apply_module _ _ _ }

lemma open_segment_eq_image_line_map (x y : E) :
  open_segment 𝕜 x y = affine_map.line_map x y '' Ioo (0 : 𝕜) 1 :=
by { convert open_segment_eq_image 𝕜 x y, ext, exact affine_map.line_map_apply_module _ _ _ }

lemma segment_image (f : E →ₗ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
set.ext (λ x, by simp_rw [segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul])

@[simp] lemma open_segment_image (f : E →ₗ[𝕜] F) (a b : E) :
  f '' open_segment 𝕜 a b = open_segment 𝕜 (f a) (f b) :=
set.ext (λ x, by simp_rw [open_segment_eq_image, mem_image, exists_exists_and_eq_and, map_add,
  map_smul])

lemma mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b -[𝕜] a + c] ↔ x ∈ [b -[𝕜] c] :=
begin
  rw [segment_eq_image', segment_eq_image'],
  refine exists_congr (λ θ, and_congr iff.rfl _),
  simp only [add_sub_add_left_eq_sub, add_assoc, add_right_inj],
end

@[simp] lemma mem_open_segment_translate (a : E) {x b c : E} :
  a + x ∈ open_segment 𝕜 (a + b) (a + c) ↔ x ∈ open_segment 𝕜 b c :=
begin
  rw [open_segment_eq_image', open_segment_eq_image'],
  refine exists_congr (λ θ, and_congr iff.rfl _),
  simp only [add_sub_add_left_eq_sub, add_assoc, add_right_inj],
end

lemma segment_translate_preimage (a b c : E) : (λ x, a + x) ⁻¹' [a + b -[𝕜] a + c] = [b -[𝕜] c] :=
set.ext $ λ x, mem_segment_translate 𝕜 a

lemma open_segment_translate_preimage (a b c : E) :
  (λ x, a + x) ⁻¹' open_segment 𝕜 (a + b) (a + c) = open_segment 𝕜 b c :=
set.ext $ λ x, mem_open_segment_translate 𝕜 a

lemma segment_translate_image (a b c : E) : (λ x, a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c] :=
segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ $ add_left_surjective a

lemma open_segment_translate_image (a b c : E) :
  (λ x, a + x) '' open_segment 𝕜 b c = open_segment 𝕜 (a + b) (a + c) :=
open_segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ $ add_left_surjective a

end add_comm_group
end ordered_ring

lemma same_ray_of_mem_segment [ordered_comm_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  {x y z : E} (h : x ∈ [y -[𝕜] z]) : same_ray 𝕜 (x - y) (z - x) :=
begin
  rw segment_eq_image' at h,
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩,
  simpa only [add_sub_cancel', ← sub_sub, sub_smul, one_smul]
    using (same_ray_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)
end

section linear_ordered_ring
variables [linear_ordered_ring 𝕜]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F]

lemma midpoint_mem_segment [invertible (2 : 𝕜)] (x y : E) :
  midpoint 𝕜 x y ∈ [x -[𝕜] y] :=
begin
  rw segment_eq_image_line_map,
  exact ⟨⅟2, ⟨inv_of_nonneg.mpr zero_le_two, inv_of_le_one one_le_two⟩, rfl⟩,
end

lemma mem_segment_sub_add [invertible (2 : 𝕜)] (x y : E) :
  x ∈ [x-y -[𝕜] x+y] :=
begin
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _,
  rw midpoint_sub_add
end

lemma mem_segment_add_sub [invertible (2 : 𝕜)] (x y : E) :
  x ∈ [x+y -[𝕜] x-y] :=
begin
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _,
  rw midpoint_add_sub
end

@[simp] lemma left_mem_open_segment_iff [densely_ordered 𝕜] [no_zero_smul_divisors 𝕜 E] {x y : E} :
  x ∈ open_segment 𝕜 x y ↔ x = y :=
begin
  split,
  { rintro ⟨a, b, ha, hb, hab, hx⟩,
    refine smul_right_injective _ hb.ne' ((add_right_inj (a • x)).1 _),
    rw [hx, ←add_smul, hab, one_smul] },
  { rintro rfl,
    rw open_segment_same,
    exact mem_singleton _ }
end

@[simp] lemma right_mem_open_segment_iff [densely_ordered 𝕜] [no_zero_smul_divisors 𝕜 E] {x y : E} :
  y ∈ open_segment 𝕜 x y ↔ x = y :=
by rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

end add_comm_group
end linear_ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {x y z : E}

lemma mem_segment_iff_same_ray : x ∈ [y -[𝕜] z] ↔ same_ray 𝕜 (x - y) (z - x) :=
begin
  refine ⟨same_ray_of_mem_segment, λ h, _⟩,
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩,
  rw [add_comm, sub_add_sub_cancel] at hxy hzx,
  rw [← mem_segment_translate _ (-x), neg_add_self],
  refine ⟨b, a, hb, ha, add_comm a b ▸ hab, _⟩,
  rw [← sub_eq_neg_add, ← neg_sub, hxy, ← sub_eq_neg_add, hzx, smul_neg, smul_comm, neg_add_self]
end

lemma mem_segment_iff_div : x ∈ [y -[𝕜] z] ↔
  ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x :=
begin
  split,
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    use [a, b, ha, hb],
    simp * },
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    refine ⟨a / (a + b), b / (a + b), div_nonneg ha hab.le, div_nonneg hb hab.le, _, rfl⟩,
    rw [← add_div, div_self hab.ne'] }
end

lemma mem_open_segment_iff_div : x ∈ open_segment 𝕜 y z ↔
  ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x :=
begin
  split,
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    use [a, b, ha, hb],
    rw [hab, div_one, div_one] },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    have hab : 0 < a + b, from add_pos ha hb,
    refine ⟨a / (a + b), b / (a + b), div_pos ha hab, div_pos hb hab, _, rfl⟩,
    rw [← add_div, div_self hab.ne'] }
end

end add_comm_group
end linear_ordered_field

/-!
#### Segments in an ordered space
Relates `segment`, `open_segment` and `set.Icc`, `set.Ico`, `set.Ioc`, `set.Ioo`
-/
section ordered_semiring
variables [ordered_semiring 𝕜]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E]

lemma segment_subset_Icc {x y : E} (h : x ≤ y) : [x -[𝕜] y] ⊆ Icc x y :=
begin
  rintro z ⟨a, b, ha, hb, hab, rfl⟩,
  split,
  calc
    x   = a • x + b • x :(convex.combo_self hab _).symm
    ... ≤ a • x + b • y : add_le_add_left (smul_le_smul_of_nonneg h hb) _,
  calc
    a • x + b • y
        ≤ a • y + b • y : add_le_add_right (smul_le_smul_of_nonneg h ha) _
    ... = y : convex.combo_self hab _,
end

end ordered_add_comm_monoid

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E]

lemma open_segment_subset_Ioo {x y : E} (h : x < y) : open_segment 𝕜 x y ⊆ Ioo x y :=
begin
  rintro z ⟨a, b, ha, hb, hab, rfl⟩,
  split,
  calc
    x   = a • x + b • x : (convex.combo_self hab _).symm
    ... < a • x + b • y : add_lt_add_left (smul_lt_smul_of_pos h hb) _,
  calc
    a • x + b • y
        < a • y + b • y : add_lt_add_right (smul_lt_smul_of_pos h ha) _
    ... = y : convex.combo_self hab _,
end

end ordered_cancel_add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E] {𝕜}

lemma segment_subset_interval (x y : E) : [x -[𝕜] y] ⊆ interval x y :=
begin
  cases le_total x y,
  { rw interval_of_le h,
    exact segment_subset_Icc h },
  { rw [interval_of_ge h, segment_symm],
    exact segment_subset_Icc h }
end

lemma convex.min_le_combo (x y : E) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min x y ≤ a • x + b • y :=
(segment_subset_interval x y ⟨_, _, ha, hb, hab, rfl⟩).1

lemma convex.combo_le_max (x y : E) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • x + b • y ≤ max x y :=
(segment_subset_interval x y ⟨_, _, ha, hb, hab, rfl⟩).2

end linear_ordered_add_comm_monoid
end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

lemma Icc_subset_segment {x y : 𝕜} : Icc x y ⊆ [x -[𝕜] y] :=
begin
  rintro z ⟨hxz, hyz⟩,
  obtain rfl | h := (hxz.trans hyz).eq_or_lt,
  { rw segment_same,
    exact hyz.antisymm hxz },
  rw ←sub_nonneg at hxz hyz,
  rw ←sub_pos at h,
  refine ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, _, _⟩,
  { rw [←add_div, sub_add_sub_cancel, div_self h.ne'] },
  { rw [smul_eq_mul, smul_eq_mul, ←mul_div_right_comm, ←mul_div_right_comm, ←add_div,
      div_eq_iff h.ne', add_comm, sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub] }
end

@[simp] lemma segment_eq_Icc {x y : 𝕜} (h : x ≤ y) : [x -[𝕜] y] = Icc x y :=
(segment_subset_Icc h).antisymm Icc_subset_segment

lemma Ioo_subset_open_segment {x y : 𝕜} : Ioo x y ⊆ open_segment 𝕜 x y :=
λ z hz, mem_open_segment_of_ne_left_right hz.1.ne hz.2.ne'
    (Icc_subset_segment $ Ioo_subset_Icc_self hz)

@[simp] lemma open_segment_eq_Ioo {x y : 𝕜} (h : x < y) : open_segment 𝕜 x y = Ioo x y :=
(open_segment_subset_Ioo h).antisymm Ioo_subset_open_segment

lemma segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) :=
begin
  cases le_total x y,
  { rw [segment_eq_Icc h, max_eq_right h, min_eq_left h] },
  { rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h] }
end

lemma open_segment_eq_Ioo' {x y : 𝕜} (hxy : x ≠ y) :
  open_segment 𝕜 x y = Ioo (min x y) (max x y) :=
begin
  cases hxy.lt_or_lt,
  { rw [open_segment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le] },
  { rw [open_segment_symm, open_segment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le] }
end

lemma segment_eq_interval (x y : 𝕜) : [x -[𝕜] y] = interval x y :=
segment_eq_Icc' _ _

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
lemma convex.mem_Icc {x y : 𝕜} (h : x ≤ y) {z : 𝕜} :
  z ∈ Icc x y ↔ ∃ (a b : 𝕜), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  rw ←segment_eq_Icc h,
  simp_rw [←exists_prop],
  refl,
end

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
lemma convex.mem_Ioo {x y : 𝕜} (h : x < y) {z : 𝕜} :
  z ∈ Ioo x y ↔ ∃ (a b : 𝕜), 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  rw ←open_segment_eq_Ioo h,
  simp_rw [←exists_prop],
  refl,
end

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
lemma convex.mem_Ioc {x y : 𝕜} (h : x < y) {z : 𝕜} :
  z ∈ Ioc x y ↔ ∃ (a b : 𝕜), 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  split,
  { rintro hz,
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := (convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz),
    obtain rfl | hb' := hb.eq_or_lt,
    { rw add_zero at hab,
      rw [hab, one_mul, zero_mul, add_zero] at hz,
      exact (hz.1.ne rfl).elim },
    { exact ⟨a, b, ha, hb', hab, rfl⟩ } },
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    obtain rfl | ha' := ha.eq_or_lt,
    { rw zero_add at hab,
      rwa [hab, one_mul, zero_mul, zero_add, right_mem_Ioc] },
    { exact Ioo_subset_Ioc_self ((convex.mem_Ioo h).2 ⟨a, b, ha', hb, hab, rfl⟩) } }
end

/-- A point is in an `Ico` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
lemma convex.mem_Ico {x y : 𝕜} (h : x < y) {z : 𝕜} :
  z ∈ Ico x y ↔ ∃ (a b : 𝕜), 0 < a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  split,
  { rintro hz,
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := (convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz),
    obtain rfl | ha' := ha.eq_or_lt,
    { rw zero_add at hab,
      rw [hab, one_mul, zero_mul, zero_add] at hz,
      exact (hz.2.ne rfl).elim },
    { exact ⟨a, b, ha', hb, hab, rfl⟩ } },
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    obtain rfl | hb' := hb.eq_or_lt,
    { rw add_zero at hab,
      rwa [hab, one_mul, zero_mul, add_zero, left_mem_Ico] },
    { exact Ioo_subset_Ico_self ((convex.mem_Ioo h).2 ⟨a, b, ha, hb', hab, rfl⟩) } }
end

end linear_ordered_field

/-! ### Convexity of sets -/

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E] [has_scalar 𝕜 F] (s : set E)

/-- Convexity of sets. -/
def convex : Prop :=
∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
  a • x + b • y ∈ s

variables {𝕜 s}

lemma convex_iff_segment_subset :
  convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → [x -[𝕜] y] ⊆ s :=
forall₄_congr $ λ x y hx hy, (segment_subset_iff _).symm

lemma convex.segment_subset (h : convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  [x -[𝕜] y] ⊆ s :=
convex_iff_segment_subset.1 h hx hy

lemma convex.open_segment_subset (h : convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  open_segment 𝕜 x y ⊆ s :=
(open_segment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
lemma convex_iff_pointwise_add_subset :
  convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
iff.intro
  begin
    rintro hA a b ha hb hab w ⟨au, bv, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩,
    exact hA hu hv ha hb hab
  end
  (λ h x y hx hy a b ha hb hab,
    (h ha hb hab) (set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩))

alias convex_iff_pointwise_add_subset ↔ convex.set_combo_subset _

lemma convex_empty : convex 𝕜 (∅ : set E) :=
λ x y, false.elim

lemma convex_univ : convex 𝕜 (set.univ : set E) := λ _ _ _ _ _ _ _ _ _, trivial

lemma convex.inter {t : set E} (hs : convex 𝕜 s) (ht : convex 𝕜 t) : convex 𝕜 (s ∩ t) :=
λ x y (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) a b (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb hab⟩

lemma convex_sInter {S : set (set E)} (h : ∀ s ∈ S, convex 𝕜 s) : convex 𝕜 (⋂₀ S) :=
assume x y hx hy a b ha hb hab s hs,
h s hs (hx s hs) (hy s hs) ha hb hab

lemma convex_Inter {ι : Sort*} {s : ι → set E} (h : ∀ i, convex 𝕜 (s i)) : convex 𝕜 (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

lemma convex_Inter₂ {ι : Sort*} {κ : ι → Sort*} {s : Π i, κ i → set E}
  (h : ∀ i j, convex 𝕜 (s i j)) :
  convex 𝕜 (⋂ i j, s i j) :=
convex_Inter $ λ i, convex_Inter $ h i

lemma convex.prod {s : set E} {t : set F} (hs : convex 𝕜 s) (ht : convex 𝕜 t) :
  convex 𝕜 (s ×ˢ t) :=
begin
  intros x y hx hy a b ha hb hab,
  apply mem_prod.2,
  exact ⟨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma convex_pi {ι : Type*} {E : ι → Type*} [Π i, add_comm_monoid (E i)]
  [Π i, has_scalar 𝕜 (E i)] {s : set ι} {t : Π i, set (E i)} (ht : ∀ i, convex 𝕜 (t i)) :
  convex 𝕜 (s.pi t) :=
λ x y hx hy a b ha hb hab i hi, ht i (hx i hi) (hy i hi) ha hb hab

lemma directed.convex_Union {ι : Sort*} {s : ι → set E} (hdir : directed (⊆) s)
  (hc : ∀ ⦃i : ι⦄, convex 𝕜 (s i)) :
  convex 𝕜 (⋃ i, s i) :=
begin
  rintro x y hx hy a b ha hb hab,
  rw mem_Union at ⊢ hx hy,
  obtain ⟨i, hx⟩ := hx,
  obtain ⟨j, hy⟩ := hy,
  obtain ⟨k, hik, hjk⟩ := hdir i j,
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩,
end

lemma directed_on.convex_sUnion {c : set (set E)} (hdir : directed_on (⊆) c)
  (hc : ∀ ⦃A : set E⦄, A ∈ c → convex 𝕜 A) :
  convex 𝕜 (⋃₀c) :=
begin
  rw sUnion_eq_Union,
  exact (directed_on_iff_directed.1 hdir).convex_Union (λ A, hc A.2),
end

end has_scalar

section module
variables [module 𝕜 E] [module 𝕜 F] {s : set E}

lemma convex_iff_open_segment_subset :
  convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → open_segment 𝕜 x y ⊆ s :=
convex_iff_segment_subset.trans $ forall₄_congr $ λ x y hx hy,
  (open_segment_subset_iff_segment_subset hx hy).symm

lemma convex_iff_forall_pos :
  convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
  → a • x + b • y ∈ s :=
convex_iff_open_segment_subset.trans $ forall₄_congr $ λ x y hx hy,
  open_segment_subset_iff 𝕜

lemma convex_iff_pairwise_pos :
  convex 𝕜 s ↔ s.pairwise (λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s) :=
begin
  refine convex_iff_forall_pos.trans ⟨λ h x hx y hy _, h hx hy, _⟩,
  intros h x y hx hy a b ha hb hab,
  obtain rfl | hxy := eq_or_ne x y,
  { rwa convex.combo_self hab },
  { exact h hx hy hxy ha hb hab },
end

protected lemma set.subsingleton.convex {s : set E} (h : s.subsingleton) : convex 𝕜 s :=
convex_iff_pairwise_pos.mpr (h.pairwise _)

lemma convex_singleton (c : E) : convex 𝕜 ({c} : set E) :=
subsingleton_singleton.convex

lemma convex.linear_image (hs : convex 𝕜 s) (f : E →ₗ[𝕜] F) : convex 𝕜 (f '' s) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx,
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy,
  exact ⟨a • x' + b • y', hs hx' hy' ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩,
end

lemma convex.is_linear_image (hs : convex 𝕜 s) {f : E → F} (hf : is_linear_map 𝕜 f) :
  convex 𝕜 (f '' s) :=
hs.linear_image $ hf.mk' f

lemma convex.linear_preimage {s : set F} (hs : convex 𝕜 s) (f : E →ₗ[𝕜] F) :
  convex 𝕜 (f ⁻¹' s) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul],
  exact hs hx hy ha hb hab,
end

lemma convex.is_linear_preimage {s : set F} (hs : convex 𝕜 s) {f : E → F} (hf : is_linear_map 𝕜 f) :
  convex 𝕜 (f ⁻¹' s) :=
hs.linear_preimage $ hf.mk' f

lemma convex.add {t : set E} (hs : convex 𝕜 s) (ht : convex 𝕜 t) : convex 𝕜 (s + t) :=
by { rw ← add_image_prod, exact (hs.prod ht).is_linear_image is_linear_map.is_linear_map_add }

lemma convex.vadd (hs : convex 𝕜 s) (z : E) : convex 𝕜 (z +ᵥ s) :=
by { simp_rw [←image_vadd, vadd_eq_add, ←singleton_add], exact (convex_singleton _).add hs }

lemma convex.translate (hs : convex 𝕜 s) (z : E) : convex 𝕜 ((λ x, z + x) '' s) := hs.vadd _

/-- The translation of a convex set is also convex. -/
lemma convex.translate_preimage_right (hs : convex 𝕜 s) (z : E) : convex 𝕜 ((λ x, z + x) ⁻¹' s) :=
begin
  intros x y hx hy a b ha hb hab,
  have h := hs hx hy ha hb hab,
  rwa [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul] at h,
end

/-- The translation of a convex set is also convex. -/
lemma convex.translate_preimage_left (hs : convex 𝕜 s) (z : E) : convex 𝕜 ((λ x, x + z) ⁻¹' s) :=
by simpa only [add_comm] using hs.translate_preimage_right z

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β] [module 𝕜 β] [ordered_smul 𝕜 β]

lemma convex_Iic (r : β) : convex 𝕜 (Iic r) :=
λ x y hx hy a b ha hb hab,
calc
  a • x + b • y
      ≤ a • r + b • r
      : add_le_add (smul_le_smul_of_nonneg hx ha) (smul_le_smul_of_nonneg hy hb)
  ... = r : convex.combo_self hab _

lemma convex_Ici (r : β) : convex 𝕜 (Ici r) := @convex_Iic 𝕜 βᵒᵈ _ _ _ _ r

lemma convex_Icc (r s : β) : convex 𝕜 (Icc r s) :=
Ici_inter_Iic.subst ((convex_Ici r).inter $ convex_Iic s)

lemma convex_halfspace_le {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  convex 𝕜 {w | f w ≤ r} :=
(convex_Iic r).is_linear_preimage h

lemma convex_halfspace_ge {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  convex 𝕜 {w | r ≤ f w} :=
(convex_Ici r).is_linear_preimage h

lemma convex_hyperplane {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  convex 𝕜 {w | f w = r} :=
begin
  simp_rw le_antisymm_iff,
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r),
end

end ordered_add_comm_monoid

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid β] [module 𝕜 β] [ordered_smul 𝕜 β]

lemma convex_Iio (r : β) : convex 𝕜 (Iio r) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw zero_add at hab,
    rwa [zero_smul, zero_add, hab, one_smul] },
  rw mem_Iio at hx hy,
  calc
    a • x + b • y
        < a • r + b • r
        : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx ha') (smul_le_smul_of_nonneg hy.le hb)
    ... = r : convex.combo_self hab _
end

lemma convex_Ioi (r : β) : convex 𝕜 (Ioi r) := @convex_Iio 𝕜 βᵒᵈ _ _ _ _ r

lemma convex_Ioo (r s : β) : convex 𝕜 (Ioo r s) :=
Ioi_inter_Iio.subst ((convex_Ioi r).inter $ convex_Iio s)

lemma convex_Ico (r s : β) : convex 𝕜 (Ico r s) :=
Ici_inter_Iio.subst ((convex_Ici r).inter $ convex_Iio s)

lemma convex_Ioc (r s : β) : convex 𝕜 (Ioc r s) :=
Ioi_inter_Iic.subst ((convex_Ioi r).inter $ convex_Iic s)

lemma convex_halfspace_lt {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  convex 𝕜 {w | f w < r} :=
(convex_Iio r).is_linear_preimage h

lemma convex_halfspace_gt {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  convex 𝕜 {w | r < f w} :=
(convex_Ioi r).is_linear_preimage h

end ordered_cancel_add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid β] [module 𝕜 β] [ordered_smul 𝕜 β]

lemma convex_interval (r s : β) : convex 𝕜 (interval r s) :=
convex_Icc _ _

end linear_ordered_add_comm_monoid
end module
end add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid E] [ordered_add_comm_monoid β] [module 𝕜 E]
  [ordered_smul 𝕜 E] {s : set E} {f : E → β}

lemma monotone_on.convex_le (hf : monotone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | f x ≤ r} :=
λ x y hx hy a b ha hb hab, ⟨hs hx.1 hy.1 ha hb hab,
  (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (convex.combo_le_max x y ha hb hab)).trans
    (max_rec' _ hx.2 hy.2)⟩

lemma monotone_on.convex_lt (hf : monotone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | f x < r} :=
λ x y hx hy a b ha hb hab, ⟨hs hx.1 hy.1 ha hb hab,
  (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (convex.combo_le_max x y ha hb hab)).trans_lt
    (max_rec' _ hx.2 hy.2)⟩

lemma monotone_on.convex_ge (hf : monotone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | r ≤ f x} :=
@monotone_on.convex_le 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r

lemma monotone_on.convex_gt (hf : monotone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | r < f x} :=
@monotone_on.convex_lt 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r

lemma antitone_on.convex_le (hf : antitone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | f x ≤ r} :=
@monotone_on.convex_ge 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

lemma antitone_on.convex_lt (hf : antitone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | f x < r} :=
@monotone_on.convex_gt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

lemma antitone_on.convex_ge (hf : antitone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | r ≤ f x} :=
@monotone_on.convex_le 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

lemma antitone_on.convex_gt (hf : antitone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | r < f x} :=
@monotone_on.convex_lt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

lemma monotone.convex_le (hf : monotone f) (r : β) :
  convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.monotone_on univ).convex_le convex_univ r)

lemma monotone.convex_lt (hf : monotone f) (r : β) :
  convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.monotone_on univ).convex_le convex_univ r)

lemma monotone.convex_ge (hf : monotone f ) (r : β) :
  convex 𝕜 {x | r ≤ f x} :=
set.sep_univ.subst ((hf.monotone_on univ).convex_ge convex_univ r)

lemma monotone.convex_gt (hf : monotone f) (r : β) :
  convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.monotone_on univ).convex_le convex_univ r)

lemma antitone.convex_le (hf : antitone f) (r : β) :
  convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.antitone_on univ).convex_le convex_univ r)

lemma antitone.convex_lt (hf : antitone f) (r : β) :
  convex 𝕜 {x | f x < r} :=
set.sep_univ.subst ((hf.antitone_on univ).convex_lt convex_univ r)

lemma antitone.convex_ge (hf : antitone f) (r : β) :
  convex 𝕜 {x | r ≤ f x} :=
set.sep_univ.subst ((hf.antitone_on univ).convex_ge convex_univ r)

lemma antitone.convex_gt (hf : antitone f) (r : β) :
  convex 𝕜 {x | r < f x} :=
set.sep_univ.subst ((hf.antitone_on univ).convex_gt convex_univ r)

end linear_ordered_add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] {s t : set E}

lemma convex.combo_eq_vadd {a b : 𝕜} {x y : E} (h : a + b = 1) :
  a • x + b • y = b • (y - x) + x :=
calc
  a • x + b • y = (b • y - b • x) + (a • x + b • x) : by abel
            ... = b • (y - x) + x                   : by rw [smul_sub, convex.combo_self h]

lemma convex_segment (x y : E) : convex 𝕜 [x -[𝕜] y] :=
begin
  rintro p q ⟨ap, bp, hap, hbp, habp, rfl⟩ ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab,
  refine ⟨a * ap + b * aq, a * bp + b * bq,
    add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
    add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), _, _⟩,
  { rw [add_add_add_comm, ←mul_add, ←mul_add, habp, habq, mul_one, mul_one, hab] },
  { simp_rw [add_smul, mul_smul, smul_add],
    exact add_add_add_comm _ _ _ _ }
end

lemma convex_open_segment (a b : E) : convex 𝕜 (open_segment 𝕜 a b) :=
begin
  rw convex_iff_open_segment_subset,
  rintro p q ⟨ap, bp, hap, hbp, habp, rfl⟩ ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩,
  refine ⟨a * ap + b * aq, a * bp + b * bq,
    add_pos (mul_pos ha hap) (mul_pos hb haq),
    add_pos (mul_pos ha hbp) (mul_pos hb hbq), _, _⟩,
  { rw [add_add_add_comm, ←mul_add, ←mul_add, habp, habq, mul_one, mul_one, hab] },
  { simp_rw [add_smul, mul_smul, smul_add],
    exact add_add_add_comm _ _ _ _ }
end

end add_comm_group
end ordered_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F] [module 𝕜 E] [module 𝕜 F] {s : set E}

lemma convex.smul (hs : convex 𝕜 s) (c : 𝕜) : convex 𝕜 (c • s) :=
hs.linear_image (linear_map.lsmul _ _ c)

lemma convex.smul_preimage (hs : convex 𝕜 s) (c : 𝕜) : convex 𝕜 ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma convex.affinity (hs : convex 𝕜 s) (z : E) (c : 𝕜) : convex 𝕜 ((λ x, z + c • x) '' s) :=
by simpa only [←image_smul, ←image_vadd, image_image] using (hs.smul c).vadd z

end add_comm_monoid
end ordered_comm_semiring

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {s t : set E}

lemma convex.add_smul_mem (hs : convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s)
  {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • y ∈ s :=
begin
  have h : x + t • y = (1 - t) • x + t • (x + y),
  { rw [smul_add, ←add_assoc, ←add_smul, sub_add_cancel, one_smul] },
  rw h,
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _),
end

lemma convex.smul_mem_of_zero_mem (hs : convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
  {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : t • x ∈ s :=
by simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

lemma convex.add_smul_sub_mem (h : convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • (y - x) ∈ s :=
begin
  apply h.segment_subset hx hy,
  rw segment_eq_image',
  exact mem_image_of_mem _ ht,
end

/-- Affine subspaces are convex. -/
lemma affine_subspace.convex (Q : affine_subspace 𝕜 E) : convex 𝕜 (Q : set E) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [eq_sub_of_add_eq hab, ← affine_map.line_map_apply_module],
  exact affine_map.line_map_mem b hx hy,
end

/--
Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
lemma convex.combo_affine_apply {a b : 𝕜} {x y : E} {f : E →ᵃ[𝕜] F} (h : a + b = 1) :
  f (a • x + b • y) = a • f x + b • f y :=
begin
  simp only [convex.combo_eq_vadd h, ← vsub_eq_sub],
  exact f.apply_line_map _ _ _,
end

/-- The preimage of a convex set under an affine map is convex. -/
lemma convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : set F} (hs : convex 𝕜 s) :
  convex 𝕜 (f ⁻¹' s) :=
begin
  intros x y xs ys a b ha hb hab,
  rw [mem_preimage, convex.combo_affine_apply hab],
  exact hs xs ys ha hb hab,
end

/-- The image of a convex set under an affine map is convex. -/
lemma convex.affine_image (f : E →ᵃ[𝕜] F) (hs : convex 𝕜 s) : convex 𝕜 (f '' s) :=
begin
  rintro x y ⟨x', ⟨hx', hx'f⟩⟩ ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab,
  refine ⟨a • x' + b • y', ⟨hs hx' hy' ha hb hab, _⟩⟩,
  rw [convex.combo_affine_apply hab, hx'f, hy'f]
end

lemma convex.neg (hs : convex 𝕜 s) : convex 𝕜 (-s) :=
hs.is_linear_preimage is_linear_map.is_linear_map_neg

lemma convex.sub (hs : convex 𝕜 s) (ht : convex 𝕜 t) : convex 𝕜 (s - t) :=
by { rw sub_eq_add_neg, exact hs.add ht.neg }

end add_comm_group
end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {s : set E}

/-- Alternative definition of set convexity, using division. -/
lemma convex_iff_div :
  convex 𝕜 s ↔ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄,
    0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
begin
  simp only [convex_iff_segment_subset, subset_def, mem_segment_iff_div],
  refine forall₄_congr (λ x y hx hy, ⟨λ H a b ha hb hab, H _ ⟨a, b, ha, hb, hab, rfl⟩, _⟩),
  rintro H _ ⟨a, b, ha, hb, hab, rfl⟩,
  exact H ha hb hab
end

lemma convex.mem_smul_of_zero_mem (h : convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s)
  (hx : x ∈ s) {t : 𝕜} (ht : 1 ≤ t) :
  x ∈ t • s :=
begin
  rw mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne',
  exact h.smul_mem_of_zero_mem zero_mem hx ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one ht⟩,
end

lemma convex.add_smul (h_conv : convex 𝕜 s) {p q : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) :
  (p + q) • s = p • s + q • s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp_rw [smul_set_empty, add_empty] },
  obtain rfl | hp' := hp.eq_or_lt,
  { rw [zero_add, zero_smul_set hs, zero_add] },
  obtain rfl | hq' := hq.eq_or_lt,
  { rw [add_zero, zero_smul_set hs, add_zero] },
  ext,
  split,
  { rintro ⟨v, hv, rfl⟩,
    exact ⟨p • v, q • v, smul_mem_smul_set hv, smul_mem_smul_set hv, (add_smul _ _ _).symm⟩ },
  { rintro ⟨v₁, v₂, ⟨v₁₁, h₁₂, rfl⟩, ⟨v₂₁, h₂₂, rfl⟩, rfl⟩,
    have hpq := add_pos hp' hq',
    exact mem_smul_set.2 ⟨_, h_conv h₁₂ h₂₂ (div_pos hp' hpq).le (div_pos hq' hpq).le
      (by rw [←div_self hpq.ne', add_div] : p / (p + q) + q / (p + q) = 1),
      by simp only [← mul_smul, smul_add, mul_div_cancel' _ hpq.ne']⟩ }
end

end add_comm_group
end linear_ordered_field

/-!
#### Convex sets in an ordered space
Relates `convex` and `ord_connected`.
-/

section

lemma set.ord_connected.convex_of_chain [ordered_semiring 𝕜] [ordered_add_comm_monoid E]
  [module 𝕜 E] [ordered_smul 𝕜 E] {s : set E} (hs : s.ord_connected) (h : is_chain (≤) s) :
  convex 𝕜 s :=
begin
  refine convex_iff_segment_subset.mpr (λ x y hx hy, _),
  obtain hxy | hyx := h.total hx hy,
  { exact (segment_subset_Icc hxy).trans (hs.out hx hy) },
  { rw segment_symm,
    exact (segment_subset_Icc hyx).trans (hs.out hy hx) }
end

lemma set.ord_connected.convex [ordered_semiring 𝕜] [linear_ordered_add_comm_monoid E] [module 𝕜 E]
  [ordered_smul 𝕜 E] {s : set E} (hs : s.ord_connected) :
  convex 𝕜 s :=
hs.convex_of_chain $ is_chain_of_trichotomous s

lemma convex_iff_ord_connected [linear_ordered_field 𝕜] {s : set 𝕜} :
  convex 𝕜 s ↔ s.ord_connected :=
begin
  simp_rw [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset],
  exact forall_congr (λ x, forall_swap)
end

alias convex_iff_ord_connected ↔ convex.ord_connected _

end

/-! #### Convexity of submodules/subspaces -/

section submodule
open submodule

lemma submodule.convex [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] (K : submodule 𝕜 E) :
  convex 𝕜 (↑K : set E) :=
by { repeat {intro}, refine add_mem (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma subspace.convex [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] (K : subspace 𝕜 E) :
  convex 𝕜 (↑K : set E) :=
K.convex

end submodule

/-! ### Simplex -/

section simplex

variables (𝕜) (ι : Type*) [ordered_semiring 𝕜] [fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of convex spaces. -/
def std_simplex : set (ι → 𝕜) :=
{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

lemma std_simplex_eq_inter :
  std_simplex 𝕜 ι = (⋂ x, {f | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} :=
by { ext f, simp only [std_simplex, set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] }

lemma convex_std_simplex : convex 𝕜 (std_simplex 𝕜 ι) :=
begin
  refine λ f g hf hg a b ha hb hab, ⟨λ x, _, _⟩,
  { apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1] },
  { erw [finset.sum_add_distrib, ← finset.smul_sum, ← finset.smul_sum, hf.2, hg.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    exact hab }
end

variable {ι}

lemma ite_eq_mem_std_simplex (i : ι) : (λ j, ite (i = j) (1:𝕜) 0) ∈ std_simplex 𝕜 ι :=
⟨λ j, by simp only; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)]⟩

end simplex
