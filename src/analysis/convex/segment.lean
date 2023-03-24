/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
import algebra.order.invertible
import algebra.order.smul
import linear_algebra.affine_space.midpoint
import linear_algebra.ray
import tactic.positivity

/-!
# Segments in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `open_segment 𝕜 x y`: Open segment joining `x` and `y`.

## Notations

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in locale `convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `open_segment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopen_segment`/`convex.Ico`/`convex.Ioc`?
-/

variables {𝕜 E F G ι : Type*} {π : ι → Type*}

open function set
open_locale pointwise

section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_monoid E]

section has_smul
variables (𝕜) [has_smul 𝕜 E] {s : set E} {x y : E}

/-- Segments in a vector space. -/
def segment (x y : E) : set E :=
{z : E | ∃ (a b : 𝕜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), a • x + b • y = z}

/-- Open segment in a vector space. Note that `open_segment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def open_segment (x y : E) : set E :=
{z : E | ∃ (a b : 𝕜) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1), a • x + b • y = z}

localized "notation (name := segment) `[` x ` -[` 𝕜 `] ` y `]` := segment 𝕜 x y" in convex

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

lemma open_segment_symm (x y : E) : open_segment 𝕜 x y = open_segment 𝕜 y x :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma open_segment_subset_segment (x y : E) : open_segment 𝕜 x y ⊆ [x -[𝕜] y] :=
λ z ⟨a, b, ha, hb, hab, hz⟩, ⟨a, b, ha.le, hb.le, hab, hz⟩

lemma segment_subset_iff :
  [x -[𝕜] y] ⊆ s ↔ ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s :=
⟨λ H a b ha hb hab, H ⟨a, b, ha, hb, hab, rfl⟩,
  λ H z ⟨a, b, ha, hb, hab, hz⟩, hz ▸ H a b ha hb hab⟩

lemma open_segment_subset_iff :
  open_segment 𝕜 x y ⊆ s ↔ ∀ a b : 𝕜, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
⟨λ H a b ha hb hab, H ⟨a, b, ha, hb, hab, rfl⟩,
  λ H z ⟨a, b, ha, hb, hab, hz⟩, hz ▸ H a b ha hb hab⟩

end has_smul

open_locale convex

section mul_action_with_zero
variables (𝕜) [mul_action_with_zero 𝕜 E]

lemma left_mem_segment (x y : E) : x ∈ [x -[𝕜] y] :=
⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

lemma right_mem_segment (x y : E) : y ∈ [x -[𝕜] y] := segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

end mul_action_with_zero

section module
variables (𝕜) [module 𝕜 E] {s : set E} {x y z : E}

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
  refine hb.eq_or_gt.imp _ (λ hb', ha.eq_or_gt.imp _ $ λ ha', _),
  { rintro rfl,
    rw [← add_zero a, hab, one_smul, zero_smul, add_zero] },
  { rintro rfl,
    rw [← zero_add b, hab, one_smul, zero_smul, zero_add] },
  { exact ⟨a, b, ha', hb', hab, rfl⟩ }
end

variables {𝕜}

lemma mem_open_segment_of_ne_left_right (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ [x -[𝕜] y]) :
  z ∈ open_segment 𝕜 x y :=
begin
  rw [←insert_endpoints_open_segment] at hz,
  exact ((hz.resolve_left hx.symm).resolve_left hy.symm)
end

lemma open_segment_subset_iff_segment_subset (hx : x ∈ s) (hy : y ∈ s) :
  open_segment 𝕜 x y ⊆ s ↔ [x -[𝕜] y] ⊆ s :=
by simp only [←insert_endpoints_open_segment, insert_subset, *, true_and]

end module
end ordered_semiring

open_locale convex

section ordered_ring
variables (𝕜) [ordered_ring 𝕜] [add_comm_group E] [add_comm_group F] [add_comm_group G] [module 𝕜 E]
  [module 𝕜 F]

section densely_ordered
variables [nontrivial 𝕜] [densely_ordered 𝕜]

@[simp] lemma open_segment_same (x : E) : open_segment 𝕜 x x = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [←add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
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

lemma segment_eq_image' (x y : E) : [x -[𝕜] y] = (λ (θ : 𝕜), x + θ • (y - x)) '' Icc (0 : 𝕜) 1 :=
by { convert segment_eq_image 𝕜 x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma open_segment_eq_image' (x y : E) :
  open_segment 𝕜 x y = (λ (θ : 𝕜), x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 :=
by { convert open_segment_eq_image 𝕜 x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma segment_eq_image_line_map (x y : E) : [x -[𝕜] y] = affine_map.line_map x y '' Icc (0 : 𝕜) 1 :=
by { convert segment_eq_image 𝕜 x y, ext, exact affine_map.line_map_apply_module _ _ _ }

lemma open_segment_eq_image_line_map (x y : E) :
  open_segment 𝕜 x y = affine_map.line_map x y '' Ioo (0 : 𝕜) 1 :=
by { convert open_segment_eq_image 𝕜 x y, ext, exact affine_map.line_map_apply_module _ _ _ }

@[simp] lemma image_segment (f : E →ᵃ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
set.ext $ λ x, by simp_rw [segment_eq_image_line_map, mem_image, exists_exists_and_eq_and,
  affine_map.apply_line_map]

@[simp] lemma image_open_segment (f : E →ᵃ[𝕜] F) (a b : E) :
  f '' open_segment 𝕜 a b = open_segment 𝕜 (f a) (f b) :=
set.ext $ λ x, by simp_rw [open_segment_eq_image_line_map, mem_image, exists_exists_and_eq_and,
  affine_map.apply_line_map]

@[simp] lemma vadd_segment [add_torsor G E] [vadd_comm_class G E E] (a : G) (b c : E) :
  a +ᵥ [b -[𝕜] c] = [a +ᵥ b -[𝕜] a +ᵥ c] :=
image_segment 𝕜 ⟨_, linear_map.id, λ _ _, vadd_comm _ _ _⟩ b c

@[simp] lemma vadd_open_segment [add_torsor G E] [vadd_comm_class G E E] (a : G) (b c : E) :
  a +ᵥ open_segment 𝕜 b c = open_segment 𝕜 (a +ᵥ b) (a +ᵥ c) :=
image_open_segment 𝕜 ⟨_, linear_map.id, λ _ _, vadd_comm _ _ _⟩ b c

@[simp] lemma mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b -[𝕜] a + c] ↔ x ∈ [b -[𝕜] c] :=
by simp_rw [←vadd_eq_add, ←vadd_segment, vadd_mem_vadd_set_iff]

@[simp] lemma mem_open_segment_translate (a : E) {x b c : E} :
  a + x ∈ open_segment 𝕜 (a + b) (a + c) ↔ x ∈ open_segment 𝕜 b c :=
by simp_rw [←vadd_eq_add, ←vadd_open_segment, vadd_mem_vadd_set_iff]

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

end ordered_ring

lemma same_ray_of_mem_segment [strict_ordered_comm_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  {x y z : E} (h : x ∈ [y -[𝕜] z]) : same_ray 𝕜 (x - y) (z - x) :=
begin
  rw segment_eq_image' at h,
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩,
  simpa only [add_sub_cancel', ←sub_sub, sub_smul, one_smul]
    using (same_ray_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)
end

section linear_ordered_ring
variables [linear_ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {x y : E}

lemma midpoint_mem_segment [invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y ∈ [x -[𝕜] y] :=
begin
  rw segment_eq_image_line_map,
  exact ⟨⅟2, ⟨inv_of_nonneg.mpr zero_le_two, inv_of_le_one one_le_two⟩, rfl⟩,
end

lemma mem_segment_sub_add [invertible (2 : 𝕜)] (x y : E) : x ∈ [x - y -[𝕜] x + y] :=
by { convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _, rw midpoint_sub_add }

lemma mem_segment_add_sub [invertible (2 : 𝕜)] (x y : E) : x ∈ [x + y -[𝕜] x - y] :=
by { convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _, rw midpoint_add_sub }

@[simp] lemma left_mem_open_segment_iff [densely_ordered 𝕜] [no_zero_smul_divisors 𝕜 E] :
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

@[simp] lemma right_mem_open_segment_iff [densely_ordered 𝕜] [no_zero_smul_divisors 𝕜 E] :
  y ∈ open_segment 𝕜 x y ↔ x = y :=
by rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

end linear_ordered_ring

section linear_ordered_semifield
variables [linear_ordered_semifield 𝕜] [add_comm_group E] [module 𝕜 E] {x y z : E}

lemma mem_segment_iff_div : x ∈ [y -[𝕜] z] ↔
  ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x :=
begin
  split,
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    use [a, b, ha, hb],
    simp * },
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    refine ⟨a / (a + b), b / (a + b), div_nonneg ha hab.le, div_nonneg hb hab.le, _, rfl⟩,
    rw [←add_div, div_self hab.ne'] }
end

lemma mem_open_segment_iff_div : x ∈ open_segment 𝕜 y z ↔
  ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x :=
begin
  split,
  { rintro ⟨a, b, ha, hb, hab, rfl⟩,
    use [a, b, ha, hb],
    rw [hab, div_one, div_one] },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    have hab : 0 < a + b := by positivity,
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, _, rfl⟩,
    rw [←add_div, div_self hab.ne'] }
end

end linear_ordered_semifield

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {x y z : E}

lemma mem_segment_iff_same_ray : x ∈ [y -[𝕜] z] ↔ same_ray 𝕜 (x - y) (z - x) :=
begin
  refine ⟨same_ray_of_mem_segment, λ h, _⟩,
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩,
  rw [add_comm, sub_add_sub_cancel] at hxy hzx,
  rw [←mem_segment_translate _ (-x), neg_add_self],
  refine ⟨b, a, hb, ha, add_comm a b ▸ hab, _⟩,
  rw [←sub_eq_neg_add, ←neg_sub, hxy, ←sub_eq_neg_add, hzx, smul_neg, smul_comm, neg_add_self]
end

open affine_map

/-- If `z = line_map x y c` is a point on the line passing through `x` and `y`, then the open
segment `open_segment 𝕜 x y` is included in the union of the open segments `open_segment 𝕜 x z`,
`open_segment 𝕜 z y`, and the point `z`. Informally, `(x, y) ⊆ {z} ∪ (x, z) ∪ (z, y)`. -/
lemma open_segment_subset_union (x y : E) {z : E} (hz : z ∈ range (line_map x y : 𝕜 → E)) :
  open_segment 𝕜 x y ⊆ insert z (open_segment 𝕜 x z ∪ open_segment 𝕜 z y) :=
begin
  rcases hz with ⟨c, rfl⟩,
  simp only [open_segment_eq_image_line_map, ← maps_to'],
  rintro a ⟨h₀, h₁⟩,
  rcases lt_trichotomy a c with hac|rfl|hca,
  { right, left,
    have hc : 0 < c, from h₀.trans hac,
    refine ⟨a / c, ⟨div_pos h₀ hc, (div_lt_one hc).2 hac⟩, _⟩,
    simp only [← homothety_eq_line_map, ← homothety_mul_apply, div_mul_cancel _ hc.ne'] },
  { left, refl },
  { right, right,
    have hc : 0 < 1 - c, from sub_pos.2 (hca.trans h₁),
    simp only [← line_map_apply_one_sub y],
    refine ⟨(a - c) / (1 - c), ⟨div_pos (sub_pos.2 hca) hc,
      (div_lt_one hc).2 $ sub_lt_sub_right h₁ _⟩, _⟩,
    simp only [← homothety_eq_line_map, ← homothety_mul_apply, sub_mul, one_mul,
      div_mul_cancel _ hc.ne', sub_sub_sub_cancel_right] }
end

end linear_ordered_field

/-!
#### Segments in an ordered space

Relates `segment`, `open_segment` and `set.Icc`, `set.Ico`, `set.Ioc`, `set.Ioo`
-/
section ordered_semiring
variables [ordered_semiring 𝕜]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E] {x y : E}

lemma segment_subset_Icc (h : x ≤ y) : [x -[𝕜] y] ⊆ Icc x y :=
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
variables [ordered_cancel_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E] {x y : E}

lemma open_segment_subset_Ioo (h : x < y) : open_segment 𝕜 x y ⊆ Ioo x y :=
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
variables [linear_ordered_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E] {𝕜} {a b : 𝕜}

lemma segment_subset_uIcc (x y : E) : [x -[𝕜] y] ⊆ uIcc x y :=
begin
  cases le_total x y,
  { rw uIcc_of_le h,
    exact segment_subset_Icc h },
  { rw [uIcc_of_ge h, segment_symm],
    exact segment_subset_Icc h }
end

lemma convex.min_le_combo (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min x y ≤ a • x + b • y :=
(segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).1

lemma convex.combo_le_max (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • x + b • y ≤ max x y :=
(segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).2

end linear_ordered_add_comm_monoid
end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field 𝕜] {x y z : 𝕜}

lemma Icc_subset_segment : Icc x y ⊆ [x -[𝕜] y] :=
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

@[simp] lemma segment_eq_Icc (h : x ≤ y) : [x -[𝕜] y] = Icc x y :=
(segment_subset_Icc h).antisymm Icc_subset_segment

lemma Ioo_subset_open_segment : Ioo x y ⊆ open_segment 𝕜 x y :=
λ z hz, mem_open_segment_of_ne_left_right hz.1.ne hz.2.ne' $ Icc_subset_segment $
  Ioo_subset_Icc_self hz

@[simp] lemma open_segment_eq_Ioo (h : x < y) : open_segment 𝕜 x y = Ioo x y :=
(open_segment_subset_Ioo h).antisymm Ioo_subset_open_segment

lemma segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) :=
begin
  cases le_total x y,
  { rw [segment_eq_Icc h, max_eq_right h, min_eq_left h] },
  { rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h] }
end

lemma open_segment_eq_Ioo' (hxy : x ≠ y) : open_segment 𝕜 x y = Ioo (min x y) (max x y) :=
begin
  cases hxy.lt_or_lt,
  { rw [open_segment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le] },
  { rw [open_segment_symm, open_segment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le] }
end

lemma segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y := segment_eq_Icc' _ _

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
lemma convex.mem_Icc (h : x ≤ y) :
  z ∈ Icc x y ↔ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z :=
by { rw ←segment_eq_Icc h, simp_rw [←exists_prop], refl }

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
lemma convex.mem_Ioo (h : x < y) :
  z ∈ Ioo x y ↔ ∃ a b, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z :=
by { rw ←open_segment_eq_Ioo h, simp_rw [←exists_prop], refl }

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
lemma convex.mem_Ioc (h : x < y) :
  z ∈ Ioc x y ↔ ∃ a b, 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  refine ⟨λ hz, _, _⟩,
  { obtain ⟨a, b, ha, hb, hab, rfl⟩ := (convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz),
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
lemma convex.mem_Ico (h : x < y) :
  z ∈ Ico x y ↔ ∃ a b, 0 < a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  refine ⟨λ hz, _, _⟩,
  { obtain ⟨a, b, ha, hb, hab, rfl⟩ := (convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz),
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

namespace prod
variables [ordered_semiring 𝕜] [add_comm_monoid E] [add_comm_monoid F] [module 𝕜 E] [module 𝕜 F]

lemma segment_subset (x y : E × F) : segment 𝕜 x y ⊆ segment 𝕜 x.1 y.1 ×ˢ segment 𝕜 x.2 y.2 :=
begin
  rintro z ⟨a, b, ha, hb, hab, hz⟩,
  exact ⟨⟨a, b, ha, hb, hab, congr_arg prod.fst hz⟩, a, b, ha, hb, hab, congr_arg prod.snd hz⟩,
end

lemma open_segment_subset (x y : E × F) :
  open_segment 𝕜 x y ⊆ open_segment 𝕜 x.1 y.1 ×ˢ open_segment 𝕜 x.2 y.2 :=
begin
  rintro z ⟨a, b, ha, hb, hab, hz⟩,
  exact ⟨⟨a, b, ha, hb, hab, congr_arg prod.fst hz⟩, a, b, ha, hb, hab, congr_arg prod.snd hz⟩,
end

lemma image_mk_segment_left (x₁ x₂ : E) (y : F) :
  (λ x, (x, y)) '' [x₁ -[𝕜] x₂] = [(x₁, y) -[𝕜] (x₂, y)] :=
begin
  ext ⟨x', y'⟩,
  simp_rw [set.mem_image, segment, set.mem_set_of, prod.smul_mk, prod.mk_add_mk,
    prod.mk.inj_iff, ←exists_and_distrib_right, @exists_comm E, exists_eq_left'],
  refine exists₅_congr (λ a b ha hb hab, _),
  rw convex.combo_self hab,
end

lemma image_mk_segment_right (x : E) (y₁ y₂ : F) :
  (λ y, (x, y)) '' [y₁ -[𝕜] y₂] = [(x, y₁) -[𝕜] (x, y₂)] :=
begin
  ext ⟨x', y'⟩,
  simp_rw [set.mem_image, segment, set.mem_set_of, prod.smul_mk, prod.mk_add_mk,
    prod.mk.inj_iff, ←exists_and_distrib_right, @exists_comm F, exists_eq_left'],
  refine exists₅_congr (λ a b ha hb hab, _),
  rw convex.combo_self hab,
end

lemma image_mk_open_segment_left (x₁ x₂ : E) (y : F) :
  (λ x, (x, y)) '' open_segment 𝕜 x₁ x₂ = open_segment 𝕜 (x₁, y) (x₂, y) :=
begin
  ext ⟨x', y'⟩,
  simp_rw [set.mem_image, open_segment, set.mem_set_of, prod.smul_mk, prod.mk_add_mk,
    prod.mk.inj_iff, ←exists_and_distrib_right, @exists_comm E, exists_eq_left'],
  refine exists₅_congr (λ a b ha hb hab, _),
  rw convex.combo_self hab,
end

@[simp] lemma image_mk_open_segment_right (x : E) (y₁ y₂ : F) :
  (λ y, (x, y)) '' open_segment 𝕜 y₁ y₂ = open_segment 𝕜 (x, y₁) (x, y₂) :=
begin
  ext ⟨x', y'⟩,
  simp_rw [set.mem_image, open_segment, set.mem_set_of, prod.smul_mk, prod.mk_add_mk,
    prod.mk.inj_iff, ←exists_and_distrib_right, @exists_comm F, exists_eq_left'],
  refine exists₅_congr (λ a b ha hb hab, _),
  rw convex.combo_self hab,
end

end prod

namespace pi
variables [ordered_semiring 𝕜] [Π i, add_comm_monoid (π i)] [Π i, module 𝕜 (π i)] {s : set ι}

lemma segment_subset (x y : Π i, π i) : segment 𝕜 x y ⊆ s.pi (λ i, segment 𝕜 (x i) (y i)) :=
by { rintro z ⟨a, b, ha, hb, hab, hz⟩ i -, exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩ }

lemma open_segment_subset (x y : Π i, π i) :
  open_segment 𝕜 x y ⊆ s.pi (λ i, open_segment 𝕜 (x i) (y i)) :=
by { rintro z ⟨a, b, ha, hb, hab, hz⟩ i -, exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩ }

variables [decidable_eq ι]

lemma image_update_segment (i : ι) (x₁ x₂ : π i) (y : Π i, π i) :
  update y i '' [x₁ -[𝕜] x₂] = [update y i x₁ -[𝕜] update y i x₂] :=
begin
  ext z,
  simp_rw [set.mem_image, segment, set.mem_set_of, ←update_smul, ←update_add, update_eq_iff,
    ←exists_and_distrib_right, @exists_comm (π i), exists_eq_left'],
  refine exists₅_congr (λ a b ha hb hab, _),
  rw convex.combo_self hab,
end

lemma image_update_open_segment (i : ι) (x₁ x₂ : π i) (y : Π i, π i) :
  update y i '' open_segment 𝕜 x₁ x₂ = open_segment 𝕜 (update y i x₁) (update y i x₂) :=
begin
  ext z,
  simp_rw [set.mem_image, open_segment, set.mem_set_of, ←update_smul, ←update_add, update_eq_iff,
    ←exists_and_distrib_right, @exists_comm (π i), exists_eq_left'],
  refine exists₅_congr (λ a b ha hb hab, _),
  rw convex.combo_self hab,
end

end pi
