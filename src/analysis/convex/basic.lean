/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import algebra.order.smul
import data.set.intervals.image_preimage
import linear_algebra.affine_space.affine_map
import order.closure

/-!
# Convex sets and functions in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `open_segment 𝕜 x y`: Open segment joining `x` and `y`.
* `convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.
* `convex_hull 𝕜 s`: The minimal convex set that includes `s`. In order theory speak, this is a
  closure operator.
* Standard simplex `std_simplex ι [fintype ι]` is the intersection of the positive quadrant with
  the hyperplane `s.sum = 1` in the space `ι → 𝕜`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex.

## Notations

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in locale `convex`

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull s` is automatically elaborated as
`⇑convex_hull s`.

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `open_segment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopen_segment`/`convex.Ico`/`convex.Ioc`?
-/

universes u u'
variables (𝕜 : Type*) {E F : Type*}

open linear_map set
open_locale big_operators classical pointwise

/-! ### Segment -/

/-- Segments in a vector space. -/
def segment [add_comm_monoid E] [ordered_semiring 𝕜] [has_scalar 𝕜 E] (x y : E) : set E :=
{z : E | ∃ (a b : 𝕜) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), a • x + b • y = z}

/-- Open segment in a vector space. Note that `open_segment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def open_segment [add_comm_monoid E] [ordered_semiring 𝕜] [has_scalar 𝕜 E] (x y : E) : set E :=
{z : E | ∃ (a b : 𝕜) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1), a • x + b • y = z}

localized "notation `[` x ` -[` 𝕜 `] ` y `]` := segment 𝕜 x y" in convex

section ordered_semiring
variables [add_comm_monoid E] [ordered_semiring 𝕜] [module 𝕜 E]

lemma segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x] :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma open_segment_symm (x y : E) :
  open_segment 𝕜 x y = open_segment 𝕜 y x :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma left_mem_segment (x y : E) : x ∈ [x -[𝕜] y] :=
⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

lemma right_mem_segment (x y : E) : y ∈ [x -[𝕜] y] :=
segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

lemma segment_same (x : E) : [x -[𝕜] x] = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
  λ h, mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩

lemma open_segment_subset_segment (x y : E) :
  open_segment 𝕜 x y ⊆ [x -[𝕜] y] :=
λ z ⟨a, b, ha, hb, hab, hz⟩, ⟨a, b, ha.le, hb.le, hab, hz⟩

lemma mem_open_segment_of_ne_left_right {x y z : E} (hx : x ≠ z) (hy : y ≠ z)
  (hz : z ∈ [x -[𝕜] y]) :
  z ∈ open_segment 𝕜 x y :=
begin
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hz,
    by_cases ha' : a = 0,
  { rw [ha', zero_add] at hab,
    rw [ha', hab, zero_smul, one_smul, zero_add] at hz,
    exact (hy hz).elim },
  by_cases hb' : b = 0,
  { rw [hb', add_zero] at hab,
    rw [hb', hab, zero_smul, one_smul, add_zero] at hz,
    exact (hx hz).elim },
  exact ⟨a, b, ha.lt_of_ne (ne.symm ha'), hb.lt_of_ne (ne.symm hb'), hab, hz⟩,
end

variables {𝕜}

lemma open_segment_subset_iff_segment_subset {x y : E} {s : set E} (hx : x ∈ s) (hy : y ∈ s) :
  open_segment 𝕜 x y ⊆ s ↔ [x -[𝕜] y] ⊆ s :=
begin
  refine ⟨λ h z hz, _, (open_segment_subset_segment 𝕜 x y).trans⟩,
  obtain rfl | hxz := eq_or_ne x z,
  { exact hx },
  obtain rfl | hyz := eq_or_ne y z,
  { exact hy },
  exact h (mem_open_segment_of_ne_left_right 𝕜 hxz hyz hz),
end

lemma convex.combo_self {x y : 𝕜} (h : x + y = 1) (a : E) : x • a + y • a = a :=
by rw [←add_smul, h, one_smul]

end ordered_semiring

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F]

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

lemma segment_eq_image₂ (x y : E) :
  [x -[𝕜] y] = (λ p : 𝕜 × 𝕜, p.1 • x + p.2 • y) '' {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} :=
by simp only [segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

lemma open_segment_eq_image (x y : E) :
  open_segment 𝕜 x y = (λ (θ : 𝕜), (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1 :=
set.ext $ λ z,
  ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
    ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel]⟩,
    λ ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩, ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

lemma open_segment_eq_image₂ (x y : E) :
  open_segment 𝕜 x y =
    (λ p : 𝕜 × 𝕜, p.1 • x + p.2 • y) '' {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1} :=
by simp only [open_segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

lemma segment_image (f : E →ₗ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
set.ext (λ x, by simp_rw [segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul])

@[simp] lemma open_segment_image (f : E →ₗ[𝕜] F) (a b : E) :
  f '' open_segment 𝕜 a b = open_segment 𝕜 (f a) (f b) :=
set.ext (λ x, by simp_rw [open_segment_eq_image, mem_image, exists_exists_and_eq_and, map_add,
  map_smul])

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module 𝕜 E]

lemma segment_eq_image' (x y : E) :
  [x -[𝕜] y] = (λ (θ : 𝕜), x + θ • (y - x)) '' Icc (0 : 𝕜) 1 :=
by { convert segment_eq_image 𝕜 x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma open_segment_eq_image' (x y : E) :
  open_segment 𝕜 x y = (λ (θ : 𝕜), x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 :=
by { convert open_segment_eq_image 𝕜 x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

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

section linear_ordered_field
variables [linear_ordered_field 𝕜]

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F] {𝕜}

@[simp] lemma left_mem_open_segment_iff [no_zero_smul_divisors 𝕜 E] {x y : E} :
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

@[simp] lemma right_mem_open_segment_iff {x y : E} :
  y ∈ open_segment 𝕜 x y ↔ x = y :=
by rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

end add_comm_group
end linear_ordered_field

/-!
#### Segments in an ordered space
Relates `segment`, `open_segment` and `set.Icc`, `set.Ico`, `set.Ioc`, `set.Ioo`
-/
section ordered_semiring
variables [ordered_semiring 𝕜]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E] {𝕜}

lemma segment_subset_Icc {x y : E} (h : x ≤ y) : [x -[𝕜] y] ⊆ Icc x y :=
begin
  rintro z ⟨a, b, ha, hb, hab, rfl⟩,
  split,
  calc
    x   = a • x + b • x : by rw [←add_smul, hab, one_smul]
    ... ≤ a • x + b • y : add_le_add_left (smul_le_smul_of_nonneg h hb) _,
  calc
    a • x + b • y
        ≤ a • y + b • y : add_le_add_right (smul_le_smul_of_nonneg h ha) _
    ... = y : by rw [←add_smul, hab, one_smul],
end

end ordered_add_comm_monoid

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid E] [module 𝕜 E] [ordered_smul 𝕜 E] {𝕜}

lemma open_segment_subset_Ioo {x y : E} (h : x < y) : open_segment 𝕜 x y ⊆ Ioo x y :=
begin
  rintro z ⟨a, b, ha, hb, hab, rfl⟩,
  split,
  calc
    x   = a • x + b • x : by rw [←add_smul, hab, one_smul]
    ... < a • x + b • y : add_lt_add_left (smul_lt_smul_of_pos h hb) _,
  calc
    a • x + b • y
        < a • y + b • y : add_lt_add_right (smul_lt_smul_of_pos h ha) _
    ... = y : by rw [←add_smul, hab, one_smul],
end

end ordered_cancel_add_comm_monoid
end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field 𝕜] {𝕜}

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
λ z hz, mem_open_segment_of_ne_left_right _ hz.1.ne hz.2.ne'
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
variables [add_comm_monoid E]

/-- Convexity of sets. -/
def convex [has_scalar 𝕜 E] (s : set E) :=
∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
  a • x + b • y ∈ s

variables {𝕜} [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F] {s : set E}

lemma convex_iff_forall_pos :
  convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
  → a • x + b • y ∈ s :=
begin
  refine ⟨λ h x y hx hy a b ha hb hab, h hx hy ha.le hb.le hab, _⟩,
  intros h x y hx hy a b ha hb hab,
  cases ha.eq_or_lt with ha ha,
  { subst a, rw [zero_add] at hab, simp [hab, hy] },
  cases hb.eq_or_lt with hb hb,
  { subst b, rw [add_zero] at hab, simp [hab, hx] },
  exact h hx hy ha hb hab
end

lemma convex_iff_segment_subset :
  convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → [x -[𝕜] y] ⊆ s :=
begin
  split,
  { rintro h x y hx hy z ⟨a, b, ha, hb, hab, rfl⟩,
    exact h hx hy ha hb hab },
  { rintro h x y hx hy a b ha hb hab,
    exact h hx hy ⟨a, b, ha, hb, hab, rfl⟩ }
end

lemma convex_iff_open_segment_subset :
  convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → open_segment 𝕜 x y ⊆ s :=
begin
  rw convex_iff_segment_subset,
  exact forall₂_congr (λ x y, forall₂_congr $ λ hx hy,
    (open_segment_subset_iff_segment_subset hx hy).symm),
end

lemma convex.segment_subset (h : convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  [x -[𝕜] y] ⊆ s :=
convex_iff_segment_subset.1 h hx hy

lemma convex.open_segment_subset (h : convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  open_segment 𝕜 x y ⊆ s :=
convex_iff_open_segment_subset.1 h hx hy

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

lemma convex_empty : convex 𝕜 (∅ : set E) := by finish

lemma convex_singleton (c : E) : convex 𝕜 ({c} : set E) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [set.eq_of_mem_singleton hx, set.eq_of_mem_singleton hy, ←add_smul, hab, one_smul],
  exact mem_singleton c
end

lemma convex_univ : convex 𝕜 (set.univ : set E) := λ _ _ _ _ _ _ _ _ _, trivial

lemma convex.inter {t : set E} (hs : convex 𝕜 s) (ht : convex 𝕜 t) : convex 𝕜 (s ∩ t) :=
λ x y (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) a b (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb hab⟩

lemma convex_sInter {S : set (set E)} (h : ∀ s ∈ S, convex 𝕜 s) : convex 𝕜 (⋂₀ S) :=
assume x y hx hy a b ha hb hab s hs,
h s hs (hx s hs) (hy s hs) ha hb hab

lemma convex_Inter {ι : Sort*} {s : ι → set E} (h : ∀ i : ι, convex 𝕜 (s i)) :
  convex 𝕜 (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

lemma convex.prod {s : set E} {t : set F} (hs : convex 𝕜 s) (ht : convex 𝕜 t) :
  convex 𝕜 (s.prod t) :=
begin
  intros x y hx hy a b ha hb hab,
  apply mem_prod.2,
  exact ⟨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma directed.convex_Union {ι : Sort*} {s : ι → set E} (hdir : directed has_subset.subset s)
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

lemma directed_on.convex_sUnion {c : set (set E)} (hdir : directed_on has_subset.subset c)
  (hc : ∀ ⦃A : set E⦄, A ∈ c → convex 𝕜 A) :
  convex 𝕜 (⋃₀c) :=
begin
  rw sUnion_eq_Union,
  exact (directed_on_iff_directed.1 hdir).convex_Union (λ A, hc A.2),
end

lemma convex.linear_image (hs : convex 𝕜 s) (f : E →ₗ[𝕜]  F) : convex 𝕜 (s.image f) :=
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
  convex 𝕜 (s.preimage f) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul],
  exact hs hx hy ha hb hab,
end

lemma convex.is_linear_preimage {s : set F} (hs : convex 𝕜 s) {f : E → F} (hf : is_linear_map 𝕜 f) :
  convex 𝕜 (preimage f s) :=
hs.linear_preimage $ hf.mk' f

lemma convex.add {t : set E}  (hs : convex 𝕜 s) (ht : convex 𝕜 t) : convex 𝕜 (s + t) :=
by { rw ← add_image_prod, exact (hs.prod ht).is_linear_image is_linear_map.is_linear_map_add }

lemma convex.translate (hs : convex 𝕜 s) (z : E) : convex 𝕜 ((λ x, z + x) '' s) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx,
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy,
  refine ⟨a • x' + b • y', hs hx' hy' ha hb hab, _⟩,
  rw [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul],
end

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

lemma convex_Iio (r : 𝕜) : convex 𝕜 (Iio r) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw zero_add at hab,
    rwa [zero_smul, zero_add, hab, one_smul] },
  rw [smul_eq_mul, smul_eq_mul],
  rw mem_Iio at hx hy,
  calc
    a * x + b * y
        < a * r + b * r : add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx ha')
          (mul_le_mul_of_nonneg_left hy.le hb)
  ... = r : by rw [←add_mul, hab, one_mul]
end

lemma convex_Ioi (r : 𝕜) : convex 𝕜 (Ioi r) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw zero_add at hab,
    rwa [zero_smul, zero_add, hab, one_smul] },
  rw [smul_eq_mul, smul_eq_mul],
  rw mem_Ioi at hx hy,
  calc
    r   = a * r + b * r : by rw [←add_mul, hab, one_mul]
    ... < a * x + b * y : add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx ha')
          (mul_le_mul_of_nonneg_left hy.le hb),
end

lemma convex_Iic (r : 𝕜) : convex 𝕜 (Iic r) :=
λ x y hx hy a b ha hb hab,
calc
  a * x + b * y
      ≤ a * r + b * r
      : add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  ... = r : by rw [←add_mul, hab, one_mul]

lemma convex_Ici (r : 𝕜) : convex 𝕜 (Ici r) :=
λ x y hx hy a b ha hb hab,
calc
  r   = a * r + b * r : by rw [←add_mul, hab, one_mul]
  ... ≤ a * x + b * y
      : add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma convex_Ioo (r s : 𝕜) : convex 𝕜 (Ioo r s) :=
Ioi_inter_Iio.subst ((convex_Ioi r).inter $ convex_Iio s)

lemma convex_Ico (r s : 𝕜) : convex 𝕜 (Ico r s) :=
Ici_inter_Iio.subst ((convex_Ici r).inter $ convex_Iio s)

lemma convex_Ioc (r s : 𝕜) : convex 𝕜 (Ioc r s) :=
Ioi_inter_Iic.subst ((convex_Ioi r).inter $ convex_Iic s)

lemma convex_Icc (r s : 𝕜) : convex 𝕜 (Icc r s) :=
Ici_inter_Iic.subst ((convex_Ici r).inter $ convex_Iic s)

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] {𝕜} {s t : set E}

lemma convex.combo_eq_vadd {a b : 𝕜} {x y : E} (h : a + b = 1) :
  a • x + b • y = b • (y - x) + x :=
calc
  a • x + b • y = (b • y - b • x) + (a • x + b • x) : by abel
            ... = b • (y - x) + x                   : by rw [smul_sub, ←add_smul, h, one_smul]

lemma convex.sub (hs : convex 𝕜 s) (ht : convex 𝕜 t) :
  convex 𝕜 ((λ x : E × E, x.1 - x.2) '' (s.prod t)) :=
(hs.prod ht).is_linear_image is_linear_map.is_linear_map_sub

lemma convex_segment (x y : E) : convex 𝕜 [x -[𝕜]  y] :=
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

lemma convex_halfspace_lt {f : E → 𝕜} (h : is_linear_map 𝕜 f) (r : 𝕜) :
  convex 𝕜 {w | f w < r} :=
(convex_Iio r).is_linear_preimage h

lemma convex_halfspace_le {f : E → 𝕜} (h : is_linear_map 𝕜 f) (r : 𝕜) :
  convex 𝕜 {w | f w ≤ r} :=
(convex_Iic r).is_linear_preimage h

lemma convex_halfspace_gt {f : E → 𝕜} (h : is_linear_map 𝕜 f) (r : 𝕜) :
  convex 𝕜 {w | r < f w} :=
(convex_Ioi r).is_linear_preimage h

lemma convex_halfspace_ge {f : E → 𝕜} (h : is_linear_map 𝕜 f) (r : 𝕜) :
  convex 𝕜 {w | r ≤ f w} :=
(convex_Ici r).is_linear_preimage h

lemma convex_hyperplane {f : E → 𝕜} (h : is_linear_map 𝕜 f) (r : 𝕜) :
  convex 𝕜 {w | f w = r} :=
begin
  simp_rw le_antisymm_iff,
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r),
end

end add_comm_group
end ordered_semiring

section linear_ordered_semiring
variables [linear_ordered_semiring 𝕜] {𝕜}

lemma convex_interval (r s : 𝕜) : convex 𝕜 (interval r s) :=
convex_Icc _ _

end linear_ordered_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F] {𝕜} {s : set E}

lemma convex.smul (hs : convex 𝕜 s) (c : 𝕜) : convex 𝕜 (c • s) :=
hs.linear_image (linear_map.lsmul _ _ c)

lemma convex.smul_preimage (hs : convex 𝕜 s) (c : 𝕜) : convex 𝕜 ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma convex.affinity (hs : convex 𝕜 s) (z : E) (c : 𝕜) : convex 𝕜 ((λ x, z + c • x) '' s) :=
begin
  have h := (hs.smul c).translate z,
  rwa [←image_smul, image_image] at h,
end

end add_comm_monoid
end ordered_comm_semiring

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F] {𝕜} {s : set E}

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

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F] {𝕜} {s : set E}

lemma convex.add_smul_sub_mem (h : convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • (y - x) ∈ s :=
begin
  apply h.segment_subset hx hy,
  rw segment_eq_image',
  exact mem_image_of_mem _ ht,
end

/--
Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
lemma convex.combo_affine_apply {a b : 𝕜} {x y : E} {f : E →ᵃ[𝕜]  F} (h : a + b = 1) :
  f (a • x + b • y) = a • f x + b • f y :=
begin
  simp only [convex.combo_eq_vadd h, ← vsub_eq_sub],
  exact f.apply_line_map _ _ _,
end

/-- The preimage of a convex set under an affine map is convex. -/
lemma convex.affine_preimage (f : E →ᵃ[𝕜]  F) {s : set F} (hs : convex 𝕜 s) :
  convex 𝕜 (f ⁻¹' s) :=
begin
  intros x y xs ys a b ha hb hab,
  rw [mem_preimage, convex.combo_affine_apply hab],
  exact hs xs ys ha hb hab,
end

/-- The image of a convex set under an affine map is convex. -/
lemma convex.affine_image (f : E →ᵃ[𝕜]  F) {s : set E} (hs : convex 𝕜 s) :
  convex 𝕜 (f '' s) :=
begin
  rintro x y ⟨x', ⟨hx', hx'f⟩⟩ ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab,
  refine ⟨a • x' + b • y', ⟨hs hx' hy' ha hb hab, _⟩⟩,
  rw [convex.combo_affine_apply hab, hx'f, hy'f]
end

lemma convex.neg (hs : convex 𝕜 s) : convex 𝕜 ((λ z, -z) '' s) :=
hs.is_linear_image is_linear_map.is_linear_map_neg

lemma convex.neg_preimage (hs : convex 𝕜 s) : convex 𝕜 ((λ z, -z) ⁻¹' s) :=
hs.is_linear_preimage is_linear_map.is_linear_map_neg

end add_comm_group

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F] {𝕜} {s : set E}

/-- Alternative definition of set convexity, using division. -/
lemma convex_iff_div :
  convex 𝕜 s ↔ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄,
    0 ≤ a → 0 ≤ b → 0 < a + b → (a/(a+b)) • x + (b/(a+b)) • y ∈ s :=
⟨λ h x y hx hy a b ha hb hab, begin
  apply h hx hy,
  { have ha', from mul_le_mul_of_nonneg_left ha (inv_pos.2 hab).le,
    rwa [mul_zero, ←div_eq_inv_mul] at ha' },
  { have hb', from mul_le_mul_of_nonneg_left hb (inv_pos.2 hab).le,
    rwa [mul_zero, ←div_eq_inv_mul] at hb' },
  { rw ←add_div,
    exact div_self hab.ne' }
end, λ h x y hx hy a b ha hb hab,
begin
  have h', from h hx hy ha hb,
  rw [hab, div_one, div_one] at h',
  exact h' zero_lt_one
end⟩

lemma convex.mem_smul_of_zero_mem (h : convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s)
  (hx : x ∈ s) {t : 𝕜} (ht : 1 ≤ t) :
  x ∈ t • s :=
begin
  rw mem_smul_set_iff_inv_smul_mem' (zero_lt_one.trans_le ht).ne',
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

end add_comm_monoid
end linear_ordered_field

/-!
#### Convex sets in an ordered space
Relates `convex` and `ord_connected`.
-/

section
variables {𝕜}

lemma set.ord_connected.convex_of_chain [ordered_add_comm_monoid E] [ordered_semiring 𝕜]
  [module 𝕜 E] [ordered_smul 𝕜 E] {s : set E} (hs : s.ord_connected) (h : zorn.chain (≤) s) :
  convex 𝕜 s :=
begin
  intros x y hx hy a b ha hb hab,
  obtain hxy | hyx := h.total_of_refl hx hy,
  { refine hs.out hx hy (mem_Icc.2 ⟨_, _⟩),
    calc
      x   = a • x + b • x : by rw [←add_smul, hab, one_smul]
      ... ≤ a • x + b • y : add_le_add_left (smul_le_smul_of_nonneg hxy hb) _,
    calc
      a • x + b • y
          ≤ a • y + b • y : add_le_add_right (smul_le_smul_of_nonneg hxy ha) _
      ... = y : by rw [←add_smul, hab, one_smul] },
  { refine hs.out hy hx (mem_Icc.2 ⟨_, _⟩),
    calc
      y   = a • y + b • y : by rw [←add_smul, hab, one_smul]
      ... ≤ a • x + b • y : add_le_add_right (smul_le_smul_of_nonneg hyx ha) _,
    calc
      a • x + b • y
          ≤ a • x + b • x : add_le_add_left (smul_le_smul_of_nonneg hyx hb) _
      ... = x : by rw [←add_smul, hab, one_smul] }
end

lemma set.ord_connected.convex [linear_ordered_add_comm_monoid E] [ordered_semiring 𝕜]
  [module 𝕜 E] [ordered_smul 𝕜 E] {s : set E} (hs : s.ord_connected) :
  convex 𝕜 s :=
hs.convex_of_chain (zorn.chain_of_trichotomous s)

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
variables {𝕜}
open submodule

lemma submodule.convex [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] (K : submodule 𝕜 E) :
  convex 𝕜 (↑K : set E) :=
by { repeat {intro}, refine add_mem _ (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma subspace.convex [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] (K : subspace 𝕜 E) :
  convex 𝕜 (↑K : set E) :=
K.convex

end submodule

/-! ### Convex hull -/

section convex_hull
section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convex_hull : closure_operator (set E) :=
closure_operator.mk₃
  (λ s, ⋂ (t : set E) (hst : s ⊆ t) (ht : convex 𝕜 t), t)
  (convex 𝕜)
  (λ s, set.subset_Inter (λ t, set.subset_Inter $ λ hst, set.subset_Inter $ λ ht, hst))
  (λ s, convex_Inter $ λ t, convex_Inter $ λ ht, convex_Inter id)
  (λ s t hst ht, set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $
  set.Inter_subset _ ht)

variables (s : set E)

lemma subset_convex_hull : s ⊆ convex_hull 𝕜 s :=
(convex_hull 𝕜).le_closure s

lemma convex_convex_hull : convex 𝕜 (convex_hull 𝕜 s) :=
closure_operator.closure_mem_mk₃ s

variables {s 𝕜} {t : set E}

lemma convex_hull_min (hst : s ⊆ t) (ht : convex 𝕜 t) : convex_hull 𝕜 s ⊆ t :=
closure_operator.closure_le_mk₃_iff (show s ≤ t, from hst) ht

lemma convex_hull_mono (hst : s ⊆ t) : convex_hull 𝕜 s ⊆ convex_hull 𝕜 t :=
(convex_hull 𝕜).monotone hst

lemma convex.convex_hull_eq {s : set E} (hs : convex 𝕜 s) : convex_hull 𝕜 s = s :=
closure_operator.mem_mk₃_closed hs

@[simp]
lemma convex_hull_empty :
  convex_hull 𝕜 (∅ : set E) = ∅ :=
convex_empty.convex_hull_eq

@[simp]
lemma convex_hull_empty_iff :
  convex_hull 𝕜 s = ∅ ↔ s = ∅ :=
begin
  split,
  { intro h,
    rw [←set.subset_empty_iff, ←h],
    exact subset_convex_hull 𝕜 _ },
  { rintro rfl,
    exact convex_hull_empty }
end

@[simp] lemma convex_hull_nonempty_iff :
  (convex_hull 𝕜 s).nonempty ↔ s.nonempty :=
begin
  rw [←ne_empty_iff_nonempty, ←ne_empty_iff_nonempty, ne.def, ne.def],
  exact not_congr convex_hull_empty_iff,
end

@[simp]
lemma convex_hull_singleton {x : E} : convex_hull 𝕜 ({x} : set E) = {x} :=
(convex_singleton x).convex_hull_eq

lemma convex.convex_remove_iff_not_mem_convex_hull_remove {s : set E} (hs : convex 𝕜 s) (x : E) :
  convex 𝕜 (s \ {x}) ↔ x ∉ convex_hull 𝕜 (s \ {x}) :=
begin
  split,
  { rintro hsx hx,
    rw hsx.convex_hull_eq at hx,
    exact hx.2 (mem_singleton _) },
  rintro hx,
  suffices h : s \ {x} = convex_hull 𝕜 (s \ {x}), { convert convex_convex_hull 𝕜 _ },
  exact subset.antisymm (subset_convex_hull 𝕜 _) (λ y hy, ⟨convex_hull_min (diff_subset _ _) hs hy,
    by { rintro (rfl : y = x), exact hx hy }⟩),
end

lemma is_linear_map.image_convex_hull {f : E → F} (hf : is_linear_map 𝕜 f) :
  f '' (convex_hull 𝕜 s) = convex_hull 𝕜 (f '' s) :=
begin
  apply set.subset.antisymm ,
  { rw set.image_subset_iff,
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull 𝕜 $ f '' s)
      ((convex_convex_hull 𝕜 (f '' s)).is_linear_preimage hf) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull 𝕜 s)
     ((convex_convex_hull 𝕜 s).is_linear_image hf) }
end

lemma linear_map.image_convex_hull (f : E →ₗ[𝕜] F) :
  f '' (convex_hull 𝕜 s) = convex_hull 𝕜 (f '' s) :=
f.is_linear.image_convex_hull

lemma is_linear_map.convex_hull_image {f : E → F} (hf : is_linear_map 𝕜 f) (s : set E) :
  convex_hull 𝕜 (f '' s) = f '' convex_hull 𝕜 s :=
set.subset.antisymm (convex_hull_min (image_subset _ (subset_convex_hull 𝕜 s)) $
  (convex_convex_hull 𝕜 s).is_linear_image hf)
  (image_subset_iff.2 $ convex_hull_min
    (image_subset_iff.1 $ subset_convex_hull 𝕜 _)
    ((convex_convex_hull 𝕜 _).is_linear_preimage hf))

lemma linear_map.convex_hull_image (f : E →ₗ[𝕜] F) (s : set E) :
  convex_hull 𝕜 (f '' s) = f '' convex_hull 𝕜 s :=
f.is_linear.convex_hull_image s

end add_comm_monoid
end ordered_semiring

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_monoid
variables {𝕜} [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F] {s : set E}

lemma affine_map.image_convex_hull (f : E →ᵃ[𝕜] F) :
  f '' (convex_hull 𝕜 s) = convex_hull 𝕜 (f '' s) :=
begin
  apply set.subset.antisymm,
  { rw set.image_subset_iff,
    refine convex_hull_min _ ((convex_convex_hull 𝕜 (⇑f '' s)).affine_preimage f),
    rw ← set.image_subset_iff,
    exact subset_convex_hull 𝕜 (f '' s) },
  { exact convex_hull_min (set.image_subset _ (subset_convex_hull 𝕜 s))
    ((convex_convex_hull 𝕜 s).affine_image f) }
end

end add_comm_monoid
end ordered_ring
end convex_hull

/-! ### Simplex -/

section simplex

variables (ι : Type*) [fintype ι]

/-- The standard simplex in the space of functions `ι → ℝ` is the set
of vectors with non-negative coordinates with total sum `1`. -/
def std_simplex (ι : Type*) [fintype ι] (R : Type*) [ordered_semiring R] :
  set (ι → R) :=
{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

variables (R : Type*) [ordered_semiring R] {f : ι → R}

lemma std_simplex_eq_inter :
  std_simplex ι R = (⋂ x, {f | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} :=
by { ext f, simp only [std_simplex, set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] }

lemma convex_std_simplex : convex R (std_simplex ι R) :=
begin
  refine λ f g hf hg a b ha hb hab, ⟨λ x, _, _⟩,
  { apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1] },
  { erw [finset.sum_add_distrib, ← finset.smul_sum, ← finset.smul_sum, hf.2, hg.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    exact hab }
end

variable {ι}

lemma ite_eq_mem_std_simplex (i : ι) : (λ j, ite (i = j) (1:R) 0) ∈ std_simplex ι R :=
⟨λ j, by simp only; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)]⟩

end simplex
