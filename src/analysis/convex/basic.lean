/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import data.complex.module
import data.set.intervals.image_preimage
import linear_algebra.affine_space.affine_map
import order.closure

/-!
# Convex sets and functions in vector spaces

In a vector space, we define the following objects and properties.

* `segment x y` is the closed segment joining `x` and `y`.
* `open_segment k x y` is the open segment joining `x` and `y`.
* A set `s` is `convex` if for any two points `x y ∈ s` it includes `segment x y`;
* A function `f : E → β` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
  points `x y ∈ s` the segment joining `(x, f x)` to `(y, f y)` is (non-strictly) above the graph
  of `f`; equivalently, `convex_on k f s` means that the epigraph
  `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is a convex set;
* Center mass of a finite set of points with prescribed weights.
* Convex hull of a set `s` is the minimal convex set that includes `s`.
* Standard simplex `std_simplex ι [fintype ι]` is the intersection of the positive quadrant with
  the hyperplane `s.sum = 1` in the space `ι → k`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex, and prove Jensen's inequality.

Note: To define convexity for functions `f : E → β`, we need `β` to be an ordered vector space,
defined using the instance `ordered_smul k β`.

## Notations

We use the following local notations:

* `I = Icc (0:k) 1`;
* `[x -[k] y] = segment x y`.

They are defined using `local notation`, so they are not available outside of this file.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull k s` is automatically elaborated as
`⇑convex_hull k s`.

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `open_segment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopen_segment`/`convex.Ico`/`convex.Ioc`?
-/

variables (k : Type*) {E F : Type*}

open linear_map set
open_locale big_operators classical pointwise

section sets

/-! ### Segment -/

section ordered_semiring
variables [add_comm_monoid E] [ordered_semiring k] [module k E]

/-- Segments in a vector space. -/
def segment (x y : E) : set E :=
{z : E | ∃ (a b : k) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), a • x + b • y = z}

/-- Open segment in a vector space. Note that `open_segment k x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def open_segment (x y : E) : set E :=
{z : E | ∃ (a b : k) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1), a • x + b • y = z}

notation `[`x `-[` k`]` y `]` := segment k x y

lemma segment_symm (x y : E) : [x -[k] y] = [y -[k] x] :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma open_segment_symm (x y : E) :
  open_segment k x y = open_segment k y x :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma left_mem_segment (x y : E) : x ∈ [x -[k] y] :=
⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

lemma right_mem_segment (x y : E) : y ∈ [x -[k] y] :=
segment_symm k y x ▸ left_mem_segment k y x

lemma segment_same (x : E) : [x -[k] x] = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
  λ h, mem_singleton_iff.1 h ▸ left_mem_segment k z z⟩

lemma open_segment_subset_segment (x y : E) :
  open_segment k x y ⊆ [x -[k] y] :=
λ z ⟨a, b, ha, hb, hab, hz⟩, ⟨a, b, ha.le, hb.le, hab, hz⟩

lemma mem_open_segment_of_ne_left_right {x y z : E} (hx : x ≠ z) (hy : y ≠ z)
  (hz : z ∈ [x -[k] y]) :
  z ∈ open_segment k x y :=
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

variables {k}

lemma open_segment_subset_iff_segment_subset {x y : E} {s : set E} (hx : x ∈ s) (hy : y ∈ s) :
  open_segment k x y ⊆ s ↔ [x -[k] y] ⊆ s :=
begin
  refine ⟨λ h z hz, _, (open_segment_subset_segment k x y).trans⟩,
  obtain rfl | hxz := eq_or_ne x z,
  { exact hx },
  obtain rfl | hyz := eq_or_ne y z,
  { exact hy },
  exact h (mem_open_segment_of_ne_left_right k hxz hyz hz),
end

lemma convex.combo_self {x y : k} (h : x + y = 1) (a : k) : x • a + y • a = a :=
by rw [←add_smul, h, one_smul]

end ordered_semiring

section ordered_ring
variables [ordered_ring k]

section add_comm_monoid
variables [add_comm_monoid E] [module k E] [add_comm_monoid F] [module k F]

section densely_ordered
variables [nontrivial k] [densely_ordered k]

@[simp] lemma open_segment_same (x : E) :
  open_segment k x x = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
  λ (h : z = x), begin
    obtain ⟨a, ha₀, ha₁⟩ := densely_ordered.dense (0 : k) 1 zero_lt_one,
    refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel'_right _ _, _⟩,
    rw [←add_smul, add_sub_cancel'_right, one_smul, h],
  end⟩

end densely_ordered

lemma segment_eq_image (x y : E) : [x -[k] y] = (λ θ : k, (1 - θ) • x + θ • y) '' Icc (0 : k) 1 :=
set.ext $ λ z,
  ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
    ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel]⟩,
    λ ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩, ⟨1-θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

lemma segment_eq_image₂ (x y : E) :
  [x -[k] y] = (λ p : k × k, p.1 • x + p.2 • y) '' {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} :=
by simp only [segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

lemma open_segment_eq_image (x y : E) :
  open_segment k x y = (λ (θ : k), (1 - θ) • x + θ • y) '' Ioo (0 : k) 1 :=
set.ext $ λ z,
  ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
    ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel]⟩,
    λ ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩, ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

lemma open_segment_eq_image₂ (x y : E) :
  open_segment k x y = (λ p:k×k, p.1 • x + p.2 • y) '' {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1} :=
by simp only [open_segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

lemma segment_image (f : E →ₗ[k] F) (a b : E) : f '' [a -[k] b] = [f a -[k] f b] :=
set.ext (λ x, by simp_rw [segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul])

@[simp] lemma open_segment_image (f : E →ₗ[k] F) (a b : E) :
  f '' open_segment k a b = open_segment k (f a) (f b) :=
set.ext (λ x, by simp_rw [open_segment_eq_image, mem_image, exists_exists_and_eq_and, map_add,
  map_smul])

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module k E]

lemma segment_eq_image' (x y : E) :
  [x -[k] y] = (λ (θ : k), x + θ • (y - x)) '' Icc (0 : k) 1 :=
by { convert segment_eq_image k x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma open_segment_eq_image' (x y : E) :
  open_segment k x y = (λ (θ : k), x + θ • (y - x)) '' Ioo (0 : k) 1 :=
by { convert open_segment_eq_image k x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b -[k] a + c] ↔ x ∈ [b -[k] c] :=
begin
  rw [segment_eq_image', segment_eq_image'],
  refine exists_congr (λ θ, and_congr iff.rfl _),
  simp only [add_sub_add_left_eq_sub, add_assoc, add_right_inj],
end

@[simp] lemma mem_open_segment_translate (a : E) {x b c : E} :
  a + x ∈ open_segment k (a + b) (a + c)  ↔ x ∈ open_segment k b c :=
begin
  rw [open_segment_eq_image', open_segment_eq_image'],
  refine exists_congr (λ θ, and_congr iff.rfl _),
  simp only [add_sub_add_left_eq_sub, add_assoc, add_right_inj],
end

lemma segment_translate_preimage (a b c : E) : (λ x, a + x) ⁻¹' [a + b -[k] a + c] = [b -[k] c] :=
set.ext $ λ x, mem_segment_translate k a

lemma open_segment_translate_preimage (a b c : E) :
  (λ x, a + x) ⁻¹' open_segment k (a + b) (a + c) = open_segment k b c :=
set.ext $ λ x, mem_open_segment_translate k a

lemma segment_translate_image (a b c : E) : (λ x, a + x) '' [b -[k] c] = [a + b -[k] a + c] :=
segment_translate_preimage k a b c ▸ image_preimage_eq _ $ add_left_surjective a

lemma open_segment_translate_image (a b c : E) :
  (λ x, a + x) '' open_segment k b c = open_segment k (a + b) (a + c) :=
open_segment_translate_preimage k a b c ▸ image_preimage_eq _ $ add_left_surjective a

end add_comm_group
end ordered_ring

section linear_ordered_field
variables [linear_ordered_field k]

section add_comm_group
variables [add_comm_group E] [module k E] [add_comm_group F] [module k F]

@[simp] lemma left_mem_open_segment_iff [no_zero_smul_divisors k E] {x y : E} :
  x ∈ open_segment k x y ↔ x = y :=
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
  y ∈ open_segment k x y ↔ x = y :=
by rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

end add_comm_group
end linear_ordered_field

/-!
#### Segments in an ordered space
Relates `segment`, `open_segment` and `set.Icc`, `set.Ico`, `set.Ioc`, `set.Ioo`
-/
section ordered_semiring
variables [ordered_semiring k]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid E] [module k E] [ordered_smul k E] {k}

lemma segment_subset_Icc {x y : E} (h : x ≤ y) : [x -[k] y] ⊆ Icc x y :=
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
variables [ordered_cancel_add_comm_monoid E] [module k E] [ordered_smul k E] {k}

lemma open_segment_subset_Ioo {x y : E} (h : x < y) : open_segment k x y ⊆ Ioo x y :=
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
variables [linear_ordered_field k] {k}

lemma Icc_subset_segment {x y : k} : Icc x y ⊆ [x -[k] y] :=
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

@[simp] lemma segment_eq_Icc {x y : k} (h : x ≤ y) : [x -[k] y] = Icc x y :=
(segment_subset_Icc h).antisymm Icc_subset_segment

lemma Ioo_subset_open_segment {x y : k} : Ioo x y ⊆ open_segment k x y :=
λ z hz, mem_open_segment_of_ne_left_right _ hz.1.ne hz.2.ne'
    (Icc_subset_segment $ Ioo_subset_Icc_self hz)

@[simp] lemma open_segment_eq_Ioo {x y : k} (h : x < y) : open_segment k x y = Ioo x y :=
(open_segment_subset_Ioo h).antisymm Ioo_subset_open_segment

lemma segment_eq_Icc' (x y : k) : [x -[k] y] = Icc (min x y) (max x y) :=
begin
  cases le_total x y,
  { rw [segment_eq_Icc h, max_eq_right h, min_eq_left h] },
  { rw [segment_symm, segment_eq_Icc h, max_eq_left h,  min_eq_right h] }
end

lemma open_segment_eq_Ioo' {x y : k} (hxy : x ≠ y) :
  open_segment k x y = Ioo (min x y) (max x y) :=
begin
  cases hxy.lt_or_lt,
  { rw [open_segment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le] },
  { rw [open_segment_symm, open_segment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le] }
end

lemma segment_eq_interval (x y : k) : [x -[k] y] = interval x y :=
segment_eq_Icc' _ _

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
lemma convex.mem_Icc {x y : k} (h : x ≤ y) {z : k} :
  z ∈ Icc x y ↔ ∃ (a b : k), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  rw ←segment_eq_Icc h,
  simp_rw [←exists_prop],
  refl,
end

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
lemma convex.mem_Ioo {x y : k} (h : x < y) {z : k} :
  z ∈ Ioo x y ↔ ∃ (a b : k), 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z :=
begin
  rw ←open_segment_eq_Ioo h,
  simp_rw [←exists_prop],
  refl,
end

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
lemma convex.mem_Ioc {x y : k} (h : x < y) {z : k} :
  z ∈ Ioc x y ↔ ∃ (a b : k), 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z :=
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
lemma convex.mem_Ico {x y : k} (h : x < y) {z : k} :
  z ∈ Ico x y ↔ ∃ (a b : k), 0 < a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z :=
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
variables [ordered_semiring k]

section add_comm_monoid
variables [add_comm_monoid E] [module k E] [add_comm_monoid F] [module k F]

/-- Convexity of sets. -/
def convex (s : set E) :=
∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : k⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
  a • x + b • y ∈ s

variables {k} {s : set E}

lemma convex_iff_forall_pos :
  convex k s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → ∀ ⦃a b : k⦄, 0 < a → 0 < b → a + b = 1
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
  convex k s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → [x -[k] y] ⊆ s :=
begin
  split,
  { rintro h x y hx hy z ⟨a, b, ha, hb, hab, rfl⟩,
    exact h hx hy ha hb hab },
  { rintro h x y hx hy a b ha hb hab,
    exact h hx hy ⟨a, b, ha, hb, hab, rfl⟩ }
end

lemma convex_iff_open_segment_subset :
  convex k s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → open_segment k x y ⊆ s :=
begin
  rw convex_iff_segment_subset,
  exact forall₂_congr (λ x y, forall₂_congr $ λ hx hy,
    (open_segment_subset_iff_segment_subset hx hy).symm),
end

lemma convex.segment_subset (h : convex k s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : [x -[k] y] ⊆ s :=
convex_iff_segment_subset.1 h hx hy

lemma convex.open_segment_subset (h : convex k s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  open_segment k x y ⊆ s :=
convex_iff_open_segment_subset.1 h hx hy

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
lemma convex_iff_pointwise_add_subset :
  convex k s ↔ ∀ ⦃a b : k⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
iff.intro
  begin
    rintro hA a b ha hb hab w ⟨au, bv, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩,
    exact hA hu hv ha hb hab
  end
  (λ h x y hx hy a b ha hb hab,
    (h ha hb hab) (set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩))

lemma convex_empty : convex k (∅ : set E) :=  by finish

lemma convex_singleton (c : E) : convex k ({c} : set E) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [set.eq_of_mem_singleton hx, set.eq_of_mem_singleton hy, ←add_smul, hab, one_smul],
  exact mem_singleton c
end

lemma convex_univ : convex k (set.univ : set E) := λ _ _ _ _ _ _ _ _ _, trivial

lemma convex.inter {t : set E} (hs: convex k s) (ht: convex k t) : convex k (s ∩ t) :=
λ x y (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) a b (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb hab⟩

lemma convex_sInter {S : set (set E)} (h : ∀ s ∈ S, convex k s) : convex k (⋂₀ S) :=
assume x y hx hy a b ha hb hab s hs,
h s hs (hx s hs) (hy s hs) ha hb hab

lemma convex_Inter {ι : Sort*} {s : ι → set E} (h : ∀ i : ι, convex k (s i)) : convex k (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

lemma convex.prod {s : set E} {t : set F} (hs : convex k s) (ht : convex k t) :
  convex k (s.prod t) :=
begin
  intros x y hx hy a b ha hb hab,
  apply mem_prod.2,
  exact ⟨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma directed.convex_Union {ι : Sort*} {s : ι → set E} (hdir : directed has_subset.subset s)
  (hc : ∀ ⦃i : ι⦄, convex k (s i)) :
  convex k (⋃ i, s i) :=
begin
  rintro x y hx hy a b ha hb hab,
  rw mem_Union at ⊢ hx hy,
  obtain ⟨i, hx⟩ := hx,
  obtain ⟨j, hy⟩ := hy,
  obtain ⟨k, hik, hjk⟩ := hdir i j,
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩,
end

lemma directed_on.convex_sUnion {c : set (set E)} (hdir : directed_on has_subset.subset c)
  (hc : ∀ ⦃A : set E⦄, A ∈ c → convex k A) :
  convex k (⋃₀c) :=
begin
  rw sUnion_eq_Union,
  exact (directed_on_iff_directed.1 hdir).convex_Union (λ A, hc A.2),
end

lemma convex.linear_image (hs : convex k s) (f : E →ₗ[k] F) : convex k (s.image f) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx,
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy,
  exact ⟨a • x' + b • y', hs hx' hy' ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩,
end

lemma convex.is_linear_image (hs : convex k s) {f : E → F} (hf : is_linear_map k f) :
  convex k (f '' s) :=
hs.linear_image $ hf.mk' f

lemma convex.linear_preimage {s : set F} (hs : convex k s) (f : E →ₗ[k] F) :
  convex k (s.preimage f) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul],
  exact hs hx hy ha hb hab,
end

lemma convex.is_linear_preimage {s : set F} (hs : convex k s) {f : E → F} (hf : is_linear_map k f) :
  convex k (preimage f s) :=
hs.linear_preimage $ hf.mk' f

lemma convex.add {t : set E}  (hs : convex k s) (ht : convex k t) : convex k (s + t) :=
by { rw ← add_image_prod, exact (hs.prod ht).is_linear_image is_linear_map.is_linear_map_add }

lemma convex.translate (hs : convex k s) (z : E) : convex k ((λ x, z + x) '' s) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx,
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy,
  refine ⟨a • x' + b • y', hs hx' hy' ha hb hab, _⟩,
  rw [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul],
end

/-- The translation of a convex set is also convex. -/
lemma convex.translate_preimage_right (hs : convex k s) (z : E) : convex k ((λ x, z + x) ⁻¹' s) :=
begin
  intros x y hx hy a b ha hb hab,
  have h := hs hx hy ha hb hab,
  rwa [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul] at h,
end

/-- The translation of a convex set is also convex. -/
lemma convex.translate_preimage_left (hs : convex k s) (z : E) : convex k ((λ x, x + z) ⁻¹' s) :=
by simpa only [add_comm] using hs.translate_preimage_right z

lemma convex_Iio (r : k) : convex k (Iio r) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw zero_add at hab,
    rwa [zero_smul, zero_add, hab, one_smul] },
  rw [smul_eq_mul, smul_eq_mul],
  rw mem_Iio at hx hy,
  calc
    a * x + b * y
        < a * r + b * r : add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx ha') (mul_le_mul_of_nonneg_left hy.le hb)
  ... = r : by rw [←add_mul, hab, one_mul]
end

lemma convex_Ioi (r : k) : convex k (Ioi r) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw zero_add at hab,
    rwa [zero_smul, zero_add, hab, one_smul] },
  rw [smul_eq_mul, smul_eq_mul],
  rw mem_Ioi at hx hy,
  calc
    r   = a * r + b * r : by rw [←add_mul, hab, one_mul]
    ... < a * x + b * y : add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx ha') (mul_le_mul_of_nonneg_left hy.le hb),
end

lemma convex_Iic (r : k) : convex k (Iic r) :=
λ x y hx hy a b ha hb hab,
calc
  a * x + b * y
      ≤ a * r + b * r : add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  ... = r : by rw [←add_mul, hab, one_mul]

lemma convex_Ici (r : k) : convex k (Ici r) :=
λ x y hx hy a b ha hb hab,
  calc
    r   = a * r + b * r : by rw [←add_mul, hab, one_mul]
    ... ≤ a * x + b * y : add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma convex_Ioo (r s : k) : convex k (Ioo r s) :=
Ioi_inter_Iio.subst ((convex_Ioi r).inter $ convex_Iio s)

lemma convex_Ico (r s : k) : convex k (Ico r s) :=
Ici_inter_Iio.subst ((convex_Ici r).inter $ convex_Iio s)

lemma convex_Ioc (r s : k) : convex k (Ioc r s) :=
Ioi_inter_Iic.subst ((convex_Ioi r).inter $ convex_Iic s)

lemma convex_Icc (r s : k) : convex k (Icc r s) :=
Ici_inter_Iic.subst ((convex_Ici r).inter $ convex_Iic s)

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module k E] {k} {s t : set E}

lemma convex.combo_eq_vadd {a b : k} {x y : E} (h : a + b = 1) :
  a • x + b • y = b • (y - x) + x :=
calc
  a • x + b • y = (b • y - b • x) + (a • x + b • x) : by abel
            ... = b • (y - x) + x                   : by rw [smul_sub, ←add_smul, h, one_smul]

lemma convex.sub (hs : convex k s) (ht : convex k t) :
  convex k ((λ x : E × E, x.1 - x.2) '' (s.prod t)) :=
(hs.prod ht).is_linear_image is_linear_map.is_linear_map_sub

lemma convex_segment (x y : E) : convex k [x -[k] y] :=
begin
  rintro p q ⟨ap, bp, hap, hbp, habp, rfl⟩ ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab,
  refine ⟨a * ap + b * aq, a * bp + b * bq,
    add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
    add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), _, _⟩,
  { rw [add_add_add_comm, ←mul_add, ←mul_add, habp, habq, mul_one, mul_one, hab] },
  { simp_rw [add_smul, mul_smul, smul_add],
    exact add_add_add_comm _ _ _ _ }
end

lemma convex_open_segment (a b : E) : convex k (open_segment k a b) :=
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

lemma convex_halfspace_lt {f : E → k} (h : is_linear_map k f) (r : k) :
  convex k {w | f w < r} :=
(convex_Iio r).is_linear_preimage h

lemma convex_halfspace_le {f : E → k} (h : is_linear_map k f) (r : k) :
  convex k {w | f w ≤ r} :=
(convex_Iic r).is_linear_preimage h

lemma convex_halfspace_gt {f : E → k} (h : is_linear_map k f) (r : k) :
  convex k {w | r < f w} :=
(convex_Ioi r).is_linear_preimage h

lemma convex_halfspace_ge {f : E → k} (h : is_linear_map k f) (r : k) :
  convex k {w | r ≤ f w} :=
(convex_Ici r).is_linear_preimage h

lemma convex_hyperplane {f : E → k} (h : is_linear_map k f) (r : k) :
  convex k {w | f w = r} :=
begin
  simp_rw le_antisymm_iff,
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r),
end

end add_comm_group
end ordered_semiring

section linear_ordered_semiring
variables [linear_ordered_semiring k] {k}

lemma convex_interval (r s : k) : convex k (interval r s) :=
convex_Icc _ _

end linear_ordered_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring k]

section add_comm_monoid
variables [add_comm_monoid E] [module k E] [add_comm_monoid F] [module k F] {k} {s : set E}

lemma convex.smul (hs : convex k s) (c : k) : convex k (c • s) :=
hs.linear_image (linear_map.lsmul _ _ c)

lemma convex.smul_preimage (hs : convex k s) (c : k) : convex k ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma convex.affinity (hs : convex k s) (z : E) (c : k) : convex k ((λ x, z + c • x) '' s) :=
begin
  have h:= (hs.smul c).translate z,
  rwa [←image_smul, image_image] at h,
end

end add_comm_monoid
end ordered_comm_semiring

section ordered_ring
variables [ordered_ring k]

section add_comm_monoid
variables [add_comm_monoid E] [module k E] [add_comm_monoid F] [module k F] {k} {s : set E}

lemma convex.add_smul_mem (hs : convex k s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s)
  {t : k} (ht : t ∈ Icc (0 : k) 1) : x + t • y ∈ s :=
begin
  have h : x + t • y = (1 - t) • x + t • (x + y),
  { rw [smul_add, ←add_assoc, ←add_smul, sub_add_cancel, one_smul] },
  rw h,
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _),
end

lemma convex.smul_mem_of_zero_mem (hs : convex k s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
  {t : k} (ht : t ∈ Icc (0 : k) 1) : t • x ∈ s :=
by simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

lemma set.ord_connected.convex_of_total {s : set k} (hs : s.ord_connected)
  (h : ∀ x y ∈ s, x ≤ y ∨ y ≤ x) :
  convex k s :=
begin
  intros x y hx hy a b ha hb hab,
  obtain hxy | hyx := h x y hx hy,
  { refine hs.out hx hy (mem_Icc.2 ⟨_, _⟩),
    { rw [convex.combo_eq_vadd hab, smul_eq_mul],
      exact le_add_of_nonneg_left (mul_nonneg hb $ sub_nonneg_of_le hxy) },
    { rw add_comm at hab,
      rw [add_comm, convex.combo_eq_vadd hab, smul_eq_mul],
      exact add_le_of_nonpos_left (mul_nonpos_of_nonneg_of_nonpos ha $
        sub_nonpos_of_le hxy) } },
  { refine hs.out hy hx (mem_Icc.2 ⟨_, _⟩),
    { rw add_comm at hab,
      rw [add_comm, convex.combo_eq_vadd hab, smul_eq_mul],
      exact le_add_of_nonneg_left (mul_nonneg ha $ sub_nonneg_of_le hyx) },
    { rw [convex.combo_eq_vadd hab, smul_eq_mul],
      exact add_le_of_nonpos_left (mul_nonpos_of_nonneg_of_nonpos hb $
        sub_nonpos_of_le hyx) } }
end

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module k E] [add_comm_group F] [module k F] {k} {s : set E}

lemma convex.add_smul_sub_mem (h : convex k s) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {t : k} (ht : t ∈ Icc (0 : k) 1) : x + t • (y - x) ∈ s :=
begin
  apply h.segment_subset hx hy,
  rw segment_eq_image',
  exact mem_image_of_mem _ ht,
end

/--
Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
lemma convex.combo_affine_apply {a b : k} {x y : E} {f : E →ᵃ[k] F} (h : a + b = 1) :
  f (a • x + b • y) = a • f x + b • f y :=
begin
  simp only [convex.combo_eq_vadd h, ← vsub_eq_sub],
  exact f.apply_line_map _ _ _,
end

/-- The preimage of a convex set under an affine map is convex. -/
lemma convex.affine_preimage (f : E →ᵃ[k] F) {s : set F} (hs : convex k s) :
  convex k (f ⁻¹' s) :=
begin
  intros x y xs ys a b ha hb hab,
  rw [mem_preimage, convex.combo_affine_apply hab],
  exact hs xs ys ha hb hab,
end

/-- The image of a convex set under an affine map is convex. -/
lemma convex.affine_image (f : E →ᵃ[k] F) {s : set E} (hs : convex k s) :
  convex k (f '' s) :=
begin
  rintro x y ⟨x', ⟨hx', hx'f⟩⟩ ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab,
  refine ⟨a • x' + b • y', ⟨hs hx' hy' ha hb hab, _⟩⟩,
  rw [convex.combo_affine_apply hab, hx'f, hy'f]
end

lemma convex.neg (hs : convex k s) : convex k ((λ z, -z) '' s) :=
hs.is_linear_image is_linear_map.is_linear_map_neg

lemma convex.neg_preimage (hs : convex k s) : convex k ((λ z, -z) ⁻¹' s) :=
hs.is_linear_preimage is_linear_map.is_linear_map_neg

end add_comm_group

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field k]

section add_comm_monoid
variables [add_comm_monoid E] [module k E] [add_comm_monoid F] [module k F] {k} {s : set E}

/-- Alternative definition of set convexity, using division. -/
lemma convex_iff_div :
  convex k s ↔ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : k⦄,
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

lemma convex.mem_smul_of_zero_mem (h : convex k s) {x : E} (zero_mem : (0 : E) ∈ s)
  (hx : x ∈ s) {t : k} (ht : 1 ≤ t) :
  x ∈ t • s :=
begin
  rw mem_smul_set_iff_inv_smul_mem (zero_lt_one.trans_le ht).ne',
  exact h.smul_mem_of_zero_mem zero_mem hx ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one ht⟩,
end

lemma convex.add_smul (h_conv : convex k s) {p q : k} (hp : 0 ≤ p) (hq : 0 ≤ q) :
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

lemma convex_iff_ord_connected {s : set k} : convex k s ↔ s.ord_connected :=
begin
  simp_rw [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset],
  exact forall_congr (λ x, forall_swap)
end

lemma convex.ord_connected {s : set k} (hs : convex k s) : s.ord_connected :=
convex_iff_ord_connected.1 hs

end add_comm_monoid
end linear_ordered_field

lemma convex_halfspace_re_lt (r : ℝ) : convex ℝ {c : ℂ | c.re < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_le (r : ℝ) : convex ℝ {c : ℂ | c.re ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_gt (r : ℝ) : convex ℝ {c : ℂ | r < c.re } :=
convex_halfspace_gt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_ge (r : ℝ) : convex ℝ {c : ℂ | r ≤ c.re} :=
convex_halfspace_ge (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_im_lt (r : ℝ) : convex ℝ {c : ℂ | c.im < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_le (r : ℝ) : convex ℝ {c : ℂ | c.im ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_gt (r : ℝ) : convex ℝ {c : ℂ | r < c.im } :=
convex_halfspace_gt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_ge (r : ℝ) : convex ℝ {c : ℂ | r ≤ c.im} :=
convex_halfspace_ge (is_linear_map.mk complex.add_im complex.smul_im) _

variables [ordered_semiring k]

section add_comm_monoid
variables [add_comm_monoid E] [module k E] [add_comm_monoid F] [module k F] {k} {s : set E}

/-! ### Convex combinations in intervals -/

variables {α : Type*} [linear_ordered_field α]


section submodule

open submodule

lemma submodule.convex (K : submodule k E) : convex k (↑K : set E) :=
by { repeat {intro}, refine add_mem _ (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma subspace.convex (K : subspace k E) : convex k (↑K : set E) := K.convex

end submodule

end sets

/-! ### Convex and concave functions -/

section functions

variables {β : Type*} [ordered_add_comm_monoid β] [module k β]

/-- Convexity of functions -/
def convex_on (s : set E) (f : E → β) : Prop :=
  convex k s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : k⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
def concave_on (s : set E) (f : E → β) : Prop :=
  convex k s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : k⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

section
variables [ordered_smul k β]

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] lemma neg_convex_on_iff {γ : Type*} [ordered_add_comm_group γ] [module k γ]
  (s : set E) (f : E → γ) : convex_on k s (-f) ↔ concave_on k s f :=
begin
  split,
  { rintro ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm] at h,
    exact h },
  { rintro ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm, h] }
end

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] lemma neg_concave_on_iff {γ : Type*} [ordered_add_comm_group γ] [module k γ]
  (s : set E) (f : E → γ) : concave_on k s (-f) ↔ convex_on k s f :=
by rw [← neg_convex_on_iff s (-f), neg_neg f]

end

lemma convex_on_id {s : set k} (hs : convex k s) : convex_on k s id := ⟨hs, by { intros, refl }⟩

lemma concave_on_id {s : set k} (hs : convex k s) : concave_on k s id := ⟨hs, by { intros, refl }⟩

lemma convex_on_const (c : β) (hs : convex k s) : convex_on k s (λ x : E, c) :=
⟨hs, by { intros, simp only [← add_smul, *, one_smul] }⟩

lemma concave_on_const (c : β) (hs : convex k s) : concave_on k s (λ x : E, c) :=
@convex_on_const _ _ _ _ (order_dual β) _ _ c hs

variables {t : set E}

lemma convex_on_iff_div {f : E → β} :
  convex_on k s f ↔ convex k s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀  ⦃a b : k⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) • f x + (b/(a+b)) • f y :=
and_congr iff.rfl
⟨begin
  intros h x y hx hy a b ha hb hab,
  apply h hx hy (div_nonneg ha $ le_of_lt hab) (div_nonneg hb $ le_of_lt hab),
  rw [←add_div],
  exact div_self (ne_of_gt hab)
end,
begin
  intros h x y hx hy a b ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy ha hb,
end⟩

lemma concave_on_iff_div {f : E → β} :
  concave_on k s f ↔ convex k s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : k⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    (a/(a+b)) • f x + (b/(a+b)) • f y ≤ f ((a/(a+b)) • x + (b/(a+b)) • y) :=
@convex_on_iff_div _ _ _ _ (order_dual β) _ _ _

/-- For a function on a convex set in a linear ordered space, in order to prove that it is convex
it suffices to verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y`
and positive `a`, `b`. The main use case is `E = k` however one can apply it, e.g., to `k^n` with
lexicographic order. -/
lemma linear_order.convex_on_of_lt {f : E → β} [linear_order E] (hs : convex k s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : k⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y) : convex_on k s f :=
begin
  use hs,
  intros x y hx hy a b ha hb hab,
  wlog hxy : x<=y using [x y a b, y x b a],
  { exact le_total _ _ },
  { cases eq_or_lt_of_le hxy with hxy hxy,
      by { subst y, rw [← add_smul, ← add_smul, hab, one_smul, one_smul] },
    cases eq_or_lt_of_le ha with ha ha,
      by { subst a, rw [zero_add] at hab, subst b, simp },
    cases eq_or_lt_of_le hb with hb hb,
      by { subst b, rw [add_zero] at hab, subst a, simp },
    exact hf hx hy hxy ha hb hab }
end

/-- For a function on a convex set in a linear ordered space, in order to prove that it is concave
it suffices to verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` only for `x < y`
and positive `a`, `b`. The main use case is `E = k` however one can apply it, e.g., to `k^n` with
lexicographic order. -/
lemma linear_order.concave_on_of_lt {f : E → β} [linear_order E] (hs : convex k s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : k⦄, 0 < a → 0 < b → a + b = 1 →
     a • f x + b • f y ≤ f (a • x + b • y)) : concave_on k s f :=
@linear_order.convex_on_of_lt _ _ _ _ (order_dual β) _ _ f _ hs hf

/-- For a function `f` defined on a convex subset `D` of `k`, if for any three points `x < y < z`
the slope of the secant line of `f` on `[x -[k] y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
lemma convex_on_real_of_slope_mono_adjacent {s : set k} (hs : convex k s) {f : k → k}
  (hf : ∀ {x y z : E}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on k s f :=
linear_order.convex_on_of_lt hs
begin
  assume x z hx hz hxz a b ha hb hab,
  let y := a * x + b * z,
  have hxy : x < y,
  { rw [← one_mul x, ← hab, add_mul],
    exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
  have hyz : y < z,
  { rw [← one_mul z, ← hab, add_mul],
    exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
  have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x),
    from (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
  have A : z - y + (y - x) = z - x, by abel,
  have B : 0 < z - x, from sub_pos.2 (lt_trans hxy hyz),
  rw [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add, A,
    ← le_div_iff B, add_div, mul_div_assoc, mul_div_assoc,
    mul_comm (f x), mul_comm (f z)] at this,
  rw [eq_comm, ← sub_eq_iff_eq_add] at hab; subst a,
  convert this; symmetry; simp only [div_eq_iff (ne_of_gt B), y]; ring
end

/-- For a function `f` defined on a subset `D` of `k`, if `f` is convex on `D`, then for any three
points `x < y < z`, the slope of the secant line of `f` on `[x -[k] y]` is less than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent {s : set k} {f : k → k} (hf : convex_on k s f)
  {x y z : E} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
begin
  have h₁ : 0 < y - x := by linarith,
  have h₂ : 0 < z - y := by linarith,
  have h₃ : 0 < z - x := by linarith,
  suffices : f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y),
    by { ring_nf at this ⊢, linarith },
  set a := (z - y) / (z - x),
  set b := (y - x) / (z - x),
  have heqz : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith], },
  have key, from
    hf.2 hx hz
      (show 0 ≤ a, by apply div_nonneg; linarith)
      (show 0 ≤ b, by apply div_nonneg; linarith)
      (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith], }),
  rw heqz at key,
  replace key := mul_le_mul_of_nonneg_left key (le_of_lt h₃),
  field_simp [ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃, mul_comm (z - x) _] at key ⊢,
  rw div_le_div_right,
  { linarith, },
  { nlinarith, },
end

/-- For a function `f` defined on a convex subset `D` of `k`, `f` is convex on `D` iff for any three
points `x < y < z` the slope of the secant line of `f` on `[x -[k] y]` is less than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on_real_iff_slope_mono_adjacent {s : set k} (hs : convex k s) {f : k → k} :
  convex_on k s f ↔
  (∀ {x y z : E}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :=
⟨convex_on.slope_mono_adjacent, convex_on_real_of_slope_mono_adjacent hs⟩

/-- For a function `f` defined on a convex subset `D` of `k`, if for any three points `x < y < z`
the slope of the secant line of `f` on `[x -[k] y]` is greater than or equal to the slope of the
secant line of `f` on `[x, z]`, then `f` is concave on `D`. -/
lemma concave_on_real_of_slope_mono_adjacent {s : set k} (hs : convex k s) {f : k → k}
  (hf : ∀ {x y z : E}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on k s f :=
begin
  rw [←neg_convex_on_iff],
  apply convex_on_real_of_slope_mono_adjacent hs,
  intros x y z xs zs xy yz,
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  simp only [hf xs zs xy yz, neg_sub_neg, pi.neg_apply],
end

/-- For a function `f` defined on a subset `D` of `k`, if `f` is concave on `D`, then for any three
points `x < y < z`, the slope of the secant line of `f` on `[x -[k] y]` is greater than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_mono_adjacent {s : set k} {f : k → k} (hf : concave_on k s f)
  {x y z : E} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
begin
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  rw [←neg_sub_neg (f y), ←neg_sub_neg (f z)],
  simp_rw [←pi.neg_apply],
  rw [←neg_convex_on_iff] at hf,
  apply convex_on.slope_mono_adjacent hf; assumption,
end

/-- For a function `f` defined on a convex subset `D` of `k`, `f` is concave on `D` iff for any
three points `x < y < z` the slope of the secant line of `f` on `[x -[k] y]` is greater than or
equal to the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_real_iff_slope_mono_adjacent {s : set k} (hs : convex k s) {f : k → k} :
  concave_on k s f ↔
  (∀ {x y z : E}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :=
⟨concave_on.slope_mono_adjacent, concave_on_real_of_slope_mono_adjacent hs⟩

lemma convex_on.subset {f : E → β} (h_convex_on : convex_on k t f)
  (h_subset : s ⊆ t) (h_convex : convex k s) : convex_on k s f :=
begin
  apply and.intro h_convex,
  intros x y hx hy,
  exact h_convex_on.2 (h_subset hx) (h_subset hy),
end

lemma concave_on.subset {f : E → β} (h_concave_on : concave_on k t f)
  (h_subset : s ⊆ t) (h_convex : convex k s) : concave_on k s f :=
@convex_on.subset _ _ _ _ (order_dual β) _ _ t f h_concave_on h_subset h_convex

lemma convex_on.add {f g : E → β} (hf : convex_on k s f) (hg : convex_on k s g) :
  convex_on k s (λ x, f x + g x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a • f x + b • f y) + (a • g x + b • g y)
      : add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    ... = a • f x + a • g x + b • f y + b • g y : by abel
    ... = a • (f x + g x) + b • (f y + g y) : by simp [smul_add, add_assoc]
end

lemma concave_on.add {f g : E → β} (hf : concave_on k s f) (hg : concave_on k s g) :
  concave_on k s (λ x, f x + g x) :=
@convex_on.add _ _ _ _ (order_dual β) _ _ f g hf hg

lemma convex_on.smul [ordered_smul k β] {f : E → β} {c : k} (hc : 0 ≤ c)
  (hf : convex_on k s f) : convex_on k s (λ x, c • f x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    c • f (a • x + b • y) ≤ c • (a • f x + b • f y)
      : smul_le_smul_of_nonneg (hf.2 hx hy ha hb hab) hc
    ... = a • (c • f x) + b • (c • f y) : by simp only [smul_add, smul_comm c]
end

lemma concave_on.smul [ordered_smul k β] {f : E → β} {c : k} (hc : 0 ≤ c)
  (hf : concave_on k s f) : concave_on k s (λ x, c • f x) :=
@convex_on.smul _ _ _ _ (order_dual β) _ _ _ f c hc hf

section linear_order
section monoid

variables {γ : Type*} [linear_ordered_add_comm_monoid γ] [module k γ] [ordered_smul k γ]
  {f g : E → γ}

/-- The pointwise maximum of convex functions is convex. -/
lemma convex_on.sup (hf : convex_on k s f) (hg : convex_on k s g) :
  convex_on k s (f ⊔ g) :=
begin
   refine ⟨hf.left, λ x y hx hy a b ha hb hab, sup_le _ _⟩,
   { calc f (a • x + b • y) ≤ a • f x + b • f y : hf.right hx hy ha hb hab
      ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
      (smul_le_smul_of_nonneg le_sup_left ha)
      (smul_le_smul_of_nonneg le_sup_left hb) },
   { calc g (a • x + b • y) ≤ a • g x + b • g y : hg.right hx hy ha hb hab
      ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
      (smul_le_smul_of_nonneg le_sup_right ha)
      (smul_le_smul_of_nonneg le_sup_right hb) }
end

/-- The pointwise minimum of concave functions is concave. -/
lemma concave_on.inf (hf : concave_on k s f) (hg : concave_on k s g) :
  concave_on k s (f ⊓ g) :=
@convex_on.sup _ _ _ _ (order_dual γ) _ _ _ _ _ hf hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment' (hf : convex_on k s f) {x y : E} {a b : k}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • max (f x) (f y) + b • max (f x) (f y) :
    add_le_add (smul_le_smul_of_nonneg (le_max_left _ _) ha)
      (smul_le_smul_of_nonneg (le_max_right _ _) hb)
  ... = max (f x) (f y) : by rw [←add_smul, hab, one_smul]

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment' (hf : concave_on k s f) {x y : E} {a b : k}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min (f x) (f y) ≤ f (a • x + b • y) :=
@convex_on.le_on_segment' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment (hf : convex_on k s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x -[k] y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment {f : E → γ} (hf : concave_on k s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x -[k] y]) :
    min (f x) (f y) ≤ f z :=
@convex_on.le_on_segment _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz

end monoid

variables {γ : Type*} [linear_ordered_cancel_add_comm_monoid γ] [module k γ] [ordered_smul k γ]
  {f : E → γ}

-- could be shown without contradiction but yeah
lemma convex_on.le_left_of_right_le' (hf : convex_on k s f) {x y : E} {a b : k}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
  (hxy : f y ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f x :=
begin
  apply le_of_not_lt (λ h, lt_irrefl (f (a • x + b • y)) _),
  calc
    f (a • x + b • y)
        ≤ a • f x + b • f y : hf.2 hx hy ha.le hb hab
    ... < a • f (a • x + b • y) + b • f (a • x + b • y)
        : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos h ha) (smul_le_smul_of_nonneg hxy hb)
    ... = f (a • x + b • y) : by rw [←add_smul, hab, one_smul],
end

lemma concave_on.left_le_of_le_right' (hf : concave_on k s f) {x y : E} {a b : k}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
  (hxy : f (a • x + b • y) ≤ f y) :
  f x ≤ f (a • x + b • y) :=
@convex_on.le_left_of_right_le' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab hxy

lemma convex_on.le_right_of_left_le' (hf : convex_on k s f) {x y : E} {a b : k}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f x ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f y :=
begin
  rw add_comm at ⊢ hab hxy,
  exact hf.le_left_of_right_le' hy hx hb ha hab hxy,
end

lemma concave_on.le_right_of_left_le' (hf : concave_on k s f) {x y : E} {a b : k}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f (a • x + b • y) ≤ f x) :
  f y ≤ f (a • x + b • y) :=
@convex_on.le_right_of_left_le' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab hxy

lemma convex_on.le_left_of_right_le (hf : convex_on k s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment k x y) (hyz : f y ≤ f z) :
  f z ≤ f x :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz,
end

lemma concave_on.left_le_of_le_right (hf : concave_on k s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment k x y) (hyz : f z ≤ f y) :
  f x ≤ f z :=
@convex_on.le_left_of_right_le _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz hyz

lemma convex_on.le_right_of_left_le (hf : convex_on k s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment k x y) (hxz : f x ≤ f z) :
  f z ≤ f y :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz,
end

lemma concave_on.le_right_of_left_le (hf : concave_on k s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment k x y) (hxz : f z ≤ f x) :
  f y ≤ f z :=
@convex_on.le_right_of_left_le _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz hxz

end linear_order

lemma convex_on.convex_le [ordered_smul k β] {f : E → β} (hf : convex_on k s f) (r : β) :
  convex k {x ∈ s | f x ≤ r} :=
λ x y hx hy a b ha hb hab,
begin
  refine ⟨hf.1 hx.1 hy.1 ha hb hab, _⟩,
  calc
    f (a • x + b • y) ≤ a • (f x) + b • (f y) : hf.2 hx.1 hy.1 ha hb hab
                  ... ≤ a • r + b • r         : add_le_add (smul_le_smul_of_nonneg hx.2 ha)
                                                  (smul_le_smul_of_nonneg hy.2 hb)
                  ... ≤ r                     : by simp [←add_smul, hab]
end

lemma concave_on.concave_le [ordered_smul k β] {f : E → β} (hf : concave_on k s f) (r : β) :
  convex k {x ∈ s | r ≤ f x} :=
@convex_on.convex_le _ _ _ _ (order_dual β) _ _ _ f hf r

lemma convex_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ]
  [module k γ] [ordered_smul k γ]
  {f : E → γ} (hf : convex_on k s f) (r : γ) : convex k {x ∈ s | f x < r} :=
begin
  intros a b as bs xa xb hxa hxb hxaxb,
  refine ⟨hf.1 as.1 bs.1 hxa hxb hxaxb, _⟩,
  by_cases H : xa = 0,
  { have H' : xb = 1 := by rwa [H, zero_add] at hxaxb,
    rw [H, H', zero_smul, one_smul, zero_add],
    exact bs.2 },
  { calc
      f (xa • a + xb • b) ≤ xa • (f a) + xb • (f b) : hf.2 as.1 bs.1 hxa hxb hxaxb
                      ... < xa • r + xb • (f b)     : (add_lt_add_iff_right (xb • (f b))).mpr
                                                        (smul_lt_smul_of_pos as.2
                                                          (lt_of_le_of_ne hxa (ne.symm H)))
                      ... ≤ xa • r + xb • r         : (add_le_add_iff_left (xa • r)).mpr
                                                        (smul_le_smul_of_nonneg bs.2.le hxb)
                      ... = r                       : by simp only [←add_smul, hxaxb, one_smul] }
end

lemma concave_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ]
  [module k γ] [ordered_smul k γ]
  {f : E → γ} (hf : concave_on k s f) (r : γ) : convex k {x ∈ s | r < f x} :=
@convex_on.convex_lt _ _ _ _ (order_dual γ) _ _ _ f hf r

lemma convex_on.convex_epigraph {γ : Type*} [ordered_add_comm_group γ]
  [module k γ] [ordered_smul k γ]
  {f : E → γ} (hf : convex_on k s f) :
  convex k {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  rintro ⟨x, r⟩ ⟨y, t⟩ ⟨hx, hr⟩ ⟨hy, ht⟩ a b ha hb hab,
  refine ⟨hf.1 hx hy ha hb hab, _⟩,
  calc f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • r + b • t : add_le_add (smul_le_smul_of_nonneg hr ha)
                            (smul_le_smul_of_nonneg ht hb)
end

lemma concave_on.convex_hypograph {γ : Type*} [ordered_add_comm_group γ]
  [module k γ] [ordered_smul k γ]
  {f : E → γ} (hf : concave_on k s f) :
  convex k {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on.convex_epigraph _ _ _ _ (order_dual γ) _ _ _ f hf

lemma convex_on_iff_convex_epigraph {γ : Type*} [ordered_add_comm_group γ]
  [module k γ] [ordered_smul k γ]
  {f : E → γ} :
  convex_on k s f ↔ convex k {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  refine ⟨convex_on.convex_epigraph, λ h, ⟨_, _⟩⟩,
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).1 },
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).2 }
end

lemma concave_on_iff_convex_hypograph {γ : Type*} [ordered_add_comm_group γ]
  [module k γ] [ordered_smul k γ]
  {f : E → γ} :
  concave_on k s f ↔ convex k {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on_iff_convex_epigraph _ _ _ _ (order_dual γ) _ _ _ f

/- A linear map is convex. -/
lemma linear_map.convex_on (f : E →ₗ[k] β) {s : set E} (hs : convex k s) : convex_on k s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/- A linear map is concave. -/
lemma linear_map.concave_on (f : E →ₗ[k] β) {s : set E} (hs : convex k s) : concave_on k s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- If a function is convex on `s`, it remains convex k when precomposed by an affine map. -/
lemma convex_on.comp_affine_map {f : F → β} (g : E →ᵃ[k] F) {s : set F}
  (hf : convex_on k s f) : convex_on k (g ⁻¹' s) (f ∘ g) :=
begin
  refine ⟨hf.1.affine_preimage  _,_⟩,
  intros x y xs ys a b ha hb hab,
  calc
    (f ∘ g) (a • x + b • y) = f (g (a • x + b • y))         : rfl
                       ...  = f (a • (g x) + b • (g y))     : by rw [convex.combo_affine_apply hab]
                       ...  ≤ a • f (g x) + b • f (g y)     : hf.2 xs ys ha hb hab
                       ...  = a • (f ∘ g) x + b • (f ∘ g) y : rfl
end

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
lemma concave_on.comp_affine_map {f : F → β} (g : E →ᵃ[k] F) {s : set F}
  (hf : concave_on k s f) : concave_on k (g ⁻¹' s) (f ∘ g) :=
@convex_on.comp_affine_map _ _ _ _ _ _ (order_dual β) _ _ f g s hf

/-- If `g` is convex on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
lemma convex_on.comp_linear_map {g : F → β} {s : set F} (hg : convex_on k s g) (f : E →ₗ[k] F) :
  convex_on k (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If `g` is concave on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
lemma concave_on.comp_linear_map {g : F → β} {s : set F} (hg : concave_on k s g) (f : E →ₗ[k] F) :
  concave_on k (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If a function is convex on `s`, it remains convex after a translation. -/
lemma convex_on.translate_right {f : E → β} {s : set E} {a : E} (hf : convex_on k s f) :
  convex_on k ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const k E a +ᵥ affine_map.id k E

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_right {f : E → β} {s : set E} {a : E} (hf : concave_on k s f) :
  concave_on k ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const k E a +ᵥ affine_map.id k E

/-- If a function is convex on `s`, it remains convex k after a translation. -/
lemma convex_on.translate_left {f : E → β} {s : set E} {a : E} (hf : convex_on k s f) :
  convex_on k ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_left {f : E → β} {s : set E} {a : E} (hf : concave_on k s f) :
  concave_on k ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right

end functions

/-! ### Center of mass -/

section center_mass

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
noncomputable def finset.center_mass (t : finset ι) (w : ι → k) (z : ι → E) : E :=
(∑ i in t, w i)⁻¹ • (∑ i in t, w i • z i)

variables (i j : ι) (c : k) (t : finset ι) (w : ι → k) (z : ι → E)

open finset

lemma finset.center_mass_empty : (∅ : finset ι).center_mass w z = 0 :=
by simp only [center_mass, sum_empty, smul_zero]

lemma finset.center_mass_pair (hne : i ≠ j) :
  ({i, j} : finset ι).center_mass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j :=
by simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]

variable {w}

lemma finset.center_mass_insert (ha : i ∉ t) (hw : ∑ j in t, w j ≠ 0) :
  (insert i t).center_mass w z = (w i / (w i + ∑ j in t, w j)) • z i +
    ((∑ j in t, w j) / (w i + ∑ j in t, w j)) • t.center_mass w z :=
begin
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul],
  congr' 2,
  rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div]
end

lemma finset.center_mass_singleton (hw : w i ≠ 0) : ({i} : finset ι).center_mass w z = z i :=
by rw [center_mass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]

lemma finset.center_mass_eq_of_sum_1 (hw : ∑ i in t, w i = 1) :
  t.center_mass w z = ∑ i in t, w i • z i :=
by simp only [finset.center_mass, hw, inv_one, one_smul]

lemma finset.center_mass_smul : t.center_mass w (λ i, c • z i) = c • t.center_mass w z :=
by simp only [finset.center_mass, finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
lemma finset.center_mass_segment'
  (s : finset ι) (t : finset ι') (ws : ι → k) (zs : ι → E) (wt : ι' → k) (zt : ι' → E)
  (hws : ∑ i in s, ws i = 1) (hwt : ∑ i in t, wt i = 1) (a b : k) (hab : a + b = 1) :
  a • s.center_mass ws zs + b • t.center_mass wt zt =
    (s.map function.embedding.inl ∪ t.map function.embedding.inr).center_mass
      (sum.elim (λ i, a * ws i) (λ j, b * wt j))
      (sum.elim zs zt) :=
begin
  rw [s.center_mass_eq_of_sum_1 _ hws, t.center_mass_eq_of_sum_1 _ hwt,
    smul_sum, smul_sum, ← finset.sum_sum_elim, finset.center_mass_eq_of_sum_1],
  { congr' with ⟨⟩; simp only [sum.elim_inl, sum.elim_inr, mul_smul] },
  { rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab] }
end

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
lemma finset.center_mass_segment
  (s : finset ι) (w₁ w₂ : ι → k) (z : ι → E)
  (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : k) (hab : a + b = 1) :
  a • s.center_mass w₁ z + b • s.center_mass w₂ z =
    s.center_mass (λ i, a * w₁ i + b * w₂ i) z :=
have hw : ∑ i in s, (a * w₁ i + b * w₂ i) = 1,
  by simp only [mul_sum.symm, sum_add_distrib, mul_one, *],
by simp only [finset.center_mass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

lemma finset.center_mass_ite_eq (hi : i ∈ t) :
  t.center_mass (λ j, if (i = j) then 1 else 0) z = z i :=
begin
  rw [finset.center_mass_eq_of_sum_1],
  transitivity ∑ j in t, if (i = j) then z i else 0,
  { congr' with i, split_ifs, exacts [h ▸ one_smul _ _, zero_smul _ _] },
  { rw [sum_ite_eq, if_pos hi] },
  { rw [sum_ite_eq, if_pos hi] }
end

variables {t w}

lemma finset.center_mass_subset {t' : finset ι} (ht : t ⊆ t')
  (h : ∀ i ∈ t', i ∉ t → w i = 0) :
  t.center_mass w z = t'.center_mass w z :=
begin
  rw [center_mass, sum_subset ht h, smul_sum, center_mass, smul_sum],
  apply sum_subset ht,
  assume i hit' hit,
  rw [h i hit' hit, zero_smul, smul_zero]
end

lemma finset.center_mass_filter_ne_zero :
  (t.filter (λ i, w i ≠ 0)).center_mass w z = t.center_mass w z :=
finset.center_mass_subset z (filter_subset _ _) $ λ i hit hit',
  by simpa only [hit, mem_filter, true_and, ne.def, not_not] using hit'

variable {z}

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
lemma convex.center_mass_mem (hs : convex k s) :
  (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i in t, w i) → (∀ i ∈ t, z i ∈ s) → t.center_mass w z ∈ s :=
begin
  induction t using finset.induction with i t hi ht, { simp [lt_irrefl] },
  intros h₀ hpos hmem,
  have zi : z i ∈ s, from hmem _ (mem_insert_self _ _),
  have hs₀ : ∀ j ∈ t, 0 ≤ w j, from λ j hj, h₀ j $ mem_insert_of_mem hj,
  rw [sum_insert hi] at hpos,
  by_cases hsum_t : ∑ j in t, w j = 0,
  { have ws : ∀ j ∈ t, w j = 0, from (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t,
    have wz : ∑ j in t, w j • z j = 0, from sum_eq_zero (λ i hi, by simp [ws i hi]),
    simp only [center_mass, sum_insert hi, wz, hsum_t, add_zero],
    simp only [hsum_t, add_zero] at hpos,
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul],
    exact zi },
  { rw [finset.center_mass_insert _ _ _ hi hsum_t],
    refine convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos,
    { exact lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_t) },
    { intros j hj, exact hmem j (mem_insert_of_mem hj) },
    { exact h₀ _ (mem_insert_self _ _) } }
end

lemma convex.sum_mem (hs : convex k s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hz : ∀ i ∈ t, z i ∈ s) :
  ∑ i in t, w i • z i ∈ s :=
by simpa only [h₁, center_mass, inv_one, one_smul] using
  hs.center_mass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

lemma convex_iff_sum_mem :
  convex k s ↔
    (∀ (t : finset E) (w : E → k),
      (∀ i ∈ t, 0 ≤ w i) → ∑ i in t, w i = 1 → (∀ x ∈ t, x ∈ s) → ∑ x in t, w x • x ∈ s ) :=
begin
  refine ⟨λ hs t w hw₀ hw₁ hts, hs.sum_mem hw₀ hw₁ hts, _⟩,
  intros h x y hx hy a b ha hb hab,
  by_cases h_cases: x = y,
  { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
  { convert h {x, y} (λ z, if z = y then b else a) _ _ _,
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl] },
    { simp_intros i hi,
      cases hi; subst i; simp [ha, hb, if_neg h_cases] },
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab] },
    { simp_intros i hi,
      cases hi; subst i; simp [hx, hy, if_neg h_cases] } }
end

/-- Jensen's inequality, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le {f : E → k} (hf : convex_on k s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (hpos : 0 < ∑ i in t, w i)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (t.center_mass w z) ≤ t.center_mass w (f ∘ z) :=
begin
  have hmem' : ∀ i ∈ t, (z i, (f ∘ z) i) ∈ {p : E × k | p.1 ∈ s ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_refl _⟩,
  convert (hf.convex_epigraph.center_mass_mem h₀ hpos hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum, prod.smul_snd, prod.snd_sum]
end

/-- Jensen's inequality, `finset.sum` version. -/
lemma convex_on.map_sum_le {f : E → k} (hf : convex_on k s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (∑ i in t, w i • z i) ≤ ∑ i in t, w i * (f (z i)) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-- If a function `f` is convex on `s` takes value `y` at the center of mass of some points
`z i ∈ s`, then for some `i` we have `y ≤ f (z i)`. -/
lemma convex_on.exists_ge_of_center_mass {f : E → k} (h : convex_on k s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hws : 0 < ∑ i in t, w i) (hz : ∀ i ∈ t, z i ∈ s) :
  ∃ i ∈ t, f (t.center_mass w z) ≤ f (z i) :=
begin
  set y := t.center_mass w z,
  have : f y ≤ t.center_mass w (f ∘ z) := h.map_center_mass_le hw₀ hws hz,
  rw ← sum_filter_ne_zero at hws,
  rw [← finset.center_mass_filter_ne_zero (f ∘ z), center_mass, smul_eq_mul,
    ← div_eq_inv_mul, le_div_iff hws, mul_sum] at this,
  replace : ∃ i ∈ t.filter (λ i, w i ≠ 0), f y * w i ≤ w i • (f ∘ z) i :=
    exists_le_of_sum_le (nonempty_of_sum_ne_zero (ne_of_gt hws)) this,
  rcases this with ⟨i, hi, H⟩,
  rw [mem_filter] at hi,
  use [i, hi.1],
  simp only [smul_eq_mul, mul_comm (w i)] at H,
  refine (mul_le_mul_right _).1 H,
  exact lt_of_le_of_ne (hw₀ i hi.1) hi.2.symm
end

end center_mass

/-! ### Convex hull -/

section convex_hull

variable {t : set E}

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convex_hull : closure_operator (set E) :=
closure_operator.mk₃
  (λ s, ⋂ (t : set E) (hst : s ⊆ t) (ht : convex k t), t)
  convex
  (λ s, set.subset_Inter (λ t, set.subset_Inter $ λ hst, set.subset_Inter $ λ ht, hst))
  (λ s, convex_Inter $ λ t, convex_Inter $ λ ht, convex_Inter id)
  (λ s t hst ht, set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $
  set.Inter_subset _ ht)

variable (s)

lemma subset_convex_hull : s ⊆ convex_hull k s :=
convex_hull.le_closure s

lemma convex_convex_hull : convex k (convex_hull k s) :=
closure_operator.closure_mem_mk₃ s

variable {s}

lemma convex_hull_min (hst : s ⊆ t) (ht : convex k t) : convex_hull k s ⊆ t :=
closure_operator.closure_le_mk₃_iff (show s ≤ t, from hst) ht

lemma convex_hull_mono (hst : s ⊆ t) : convex_hull k s ⊆ convex_hull k t :=
convex_hull.monotone hst

lemma convex.convex_hull_eq {s : set E} (hs : convex k s) : convex_hull k s = s :=
closure_operator.mem_mk₃_closed hs

@[simp]
lemma convex_hull_empty :
  convex_hull k (∅ : set E) = ∅ :=
convex_empty.convex_hull_eq

@[simp]
lemma convex_hull_empty_iff :
  convex_hull k s = ∅ ↔ s = ∅ :=
begin
  split,
  { intro h,
    rw [←set.subset_empty_iff, ←h],
    exact subset_convex_hull k _ },
  { rintro rfl,
    exact convex_hull_empty }
end

@[simp] lemma convex_hull_nonempty_iff :
  (convex_hull k s).nonempty ↔ s.nonempty :=
begin
  rw [←ne_empty_iff_nonempty, ←ne_empty_iff_nonempty, ne.def, ne.def],
  exact not_congr convex_hull_empty_iff,
end

@[simp]
lemma convex_hull_singleton {x : E} : convex_hull k ({x} : set E) = {x} :=
(convex_singleton x).convex_hull_eq

lemma convex.convex_remove_iff_not_mem_convex_hull_remove {s : set E} (hs : convex k s) (x : E) :
  convex k (s \ {x}) ↔ x ∉ convex_hull k (s \ {x}) :=
begin
  split,
  { rintro hsx hx,
    rw hsx.convex_hull_eq at hx,
    exact hx.2 (mem_singleton _) },
  rintro hx,
  suffices h : s \ {x} = convex_hull k (s \ {x}), { convert convex_convex_hull k _ },
  exact subset.antisymm (subset_convex_hull k _) (λ y hy, ⟨convex_hull_min (diff_subset _ _) hs hy,
    by { rintro (rfl : y = x), exact hx hy }⟩),
end

lemma is_linear_map.image_convex_hull {f : E → F} (hf : is_linear_map k f) :
  f '' (convex_hull k s) = convex_hull k (f '' s) :=
begin
  refine set.subset.antisymm _ _,
  { rw [set.image_subset_iff],
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull k $ f '' s)
      ((convex_convex_hull k (f '' s)).is_linear_preimage hf) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull k s)
     ((convex_convex_hull k s).is_linear_image hf) }
end

lemma linear_map.image_convex_hull (f : E →ₗ[k] F) :
  f '' (convex_hull k s) = convex_hull k (f '' s) :=
f.is_linear.image_convex_hull

lemma affine_map.image_convex_hull (f : E →ᵃ[k] F) :
  f '' (convex_hull k s) = convex_hull k (f '' s) :=
begin
  apply set.subset.antisymm,
  { rw set.image_subset_iff,
    refine convex_hull_min _ ((convex_convex_hull (⇑f '' s)).affine_preimage f),
    rw ← set.image_subset_iff,
    exact subset_convex_hull (f '' s), },
  { refine convex_hull_min _ ((convex_convex_hull s).affine_image f),
    apply set.image_subset,
    exact subset_convex_hull s, },
end

lemma finset.center_mass_mem_convex_hull (t : finset ι) {w : ι → k} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : 0 < ∑ i in t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
  t.center_mass w z ∈ convex_hull k s :=
(convex_convex_hull k s).center_mass_mem hw₀ hws (λ i hi, subset_convex_hull k s $ hz i hi)

-- TODO : Do we need other versions of the next lemma?

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
lemma convex_hull_eq (s : set E) :
  convex_hull k s = {x : E | ∃ (ι : Type u') (t : finset ι) (w : ι → k) (z : ι → E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s),
    t.center_mass w z = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    use [punit, {punit.star}, λ _, 1, λ _, x, λ _ _, zero_le_one,
      finset.sum_singleton, λ _ _, hx],
    simp only [finset.center_mass, finset.sum_singleton, inv_one, one_smul] },
  { rintro x y ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, _, _, _, _, rfl⟩,
    { rintro i hi,
      rw [finset.mem_union, finset.mem_map, finset.mem_map] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr];
        apply_rules [mul_nonneg, hwx₀, hwy₀] },
    { simp [finset.sum_sum_elim, finset.mul_sum.symm, *] },
    { intros i hi,
      rw [finset.mem_union, finset.mem_map, finset.mem_map] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩; apply_rules [hzx, hzy] } },
  { rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    exact t.center_mass_mem_convex_hull k hw₀ (hw₁.symm ▸ zero_lt_one) hz }
end

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then `f` can't have a maximum on `convex_hull k s` outside of `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull {f : E → k} (hf : convex_on k (convex_hull k s) f)
  {x} (hx : x ∈ convex_hull k s) : ∃ y ∈ s, f x ≤ f y :=
begin
  rw convex_hull_eq at hx,
  rcases hx with ⟨α, t, w, z, hw₀, hw₁, hz, rfl⟩,
  rcases hf.exists_ge_of_center_mass hw₀ (hw₁.symm ▸ zero_lt_one)
    (λ i hi, subset_convex_hull k s (hz i hi)) with ⟨i, hit, Hi⟩,
  exact ⟨z i, hz i hit, Hi⟩
end

lemma finset.convex_hull_eq (s : finset E) :
  convex_hull k ↑s = {x : E | ∃ (w : E → k) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in s, w y = 1),
    s.center_mass w id = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    rw [finset.mem_coe] at hx,
    refine ⟨_, _, _, finset.center_mass_ite_eq _ _ _ hx⟩,
    { intros, split_ifs, exacts [zero_le_one, le_refl 0] },
    { rw [finset.sum_ite_eq, if_pos hx] } },
  { rintro x y ⟨wx, hwx₀, hwx₁, rfl⟩ ⟨wy, hwy₀, hwy₁, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, rfl⟩,
    { rintro i hi,
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀], },
    { simp only [finset.sum_add_distrib, finset.mul_sum.symm, mul_one, *] } },
  { rintro _ ⟨w, hw₀, hw₁, rfl⟩,
    exact s.center_mass_mem_convex_hull k (λ x hx, hw₀ _  hx)
      (hw₁.symm ▸ zero_lt_one) (λ x hx, hx) }
end

lemma set.finite.convex_hull_eq {s : set E} (hs : finite s) :
  convex_hull k s = {x : E | ∃ (w : E → k) (hw₀ : ∀ y ∈ s, 0 ≤ w y)
    (hw₁ : ∑ y in hs.to_finset, w y = 1), hs.to_finset.center_mass w id = x} :=
by simpa only [set.finite.coe_to_finset, set.finite.mem_to_finset, exists_prop]
  using hs.to_finset.convex_hull_eq

lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull k s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull k ↑t :=
begin
  refine subset.antisymm _ _,
  { rw [convex_hull_eq.{u}],
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    simp only [mem_Union],
    refine ⟨t.image z, _, _⟩,
    { rw [finset.coe_image, image_subset_iff],
      exact hz },
    { apply t.center_mass_mem_convex_hull hw₀,
      { simp only [hw₁, zero_lt_one] },
      { exact λ i hi, finset.mem_coe.2 (finset.mem_image_of_mem _ hi) } } },
   { exact Union_subset (λ i, Union_subset convex_hull_mono), },
end

lemma is_linear_map.convex_hull_image {f : E → F} (hf : is_linear_map k f) (s : set E) :
  convex_hull k (f '' s) = f '' convex_hull k s :=
set.subset.antisymm (convex_hull_min (image_subset _ (subset_convex_hull k s)) $
  (convex_convex_hull k s).is_linear_image hf)
  (image_subset_iff.2 $ convex_hull_min
    (image_subset_iff.1 $ subset_convex_hull k _)
    ((convex_convex_hull k _).is_linear_preimage hf))

lemma linear_map.convex_hull_image (f : E →ₗ[k] F) (s : set E) :
  convex_hull k (f '' s) = f '' convex_hull k s :=
f.is_linear.convex_hull_image s

end convex_hull

/-! ### Simplex -/

section simplex

variables (ι) [fintype ι] {f : ι → k}

/-- The standard simplex in the space of functions `ι → k` is the set
of vectors with non-negative coordinates with total sum `1`. -/
def std_simplex (ι : Type*) [fintype ι] : set (ι → k) :=
{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

lemma std_simplex_eq_inter :
  std_simplex ι = (⋂ x, {f | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} :=
by { ext f, simp only [std_simplex, set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] }

lemma convex_std_simplex : convex k (std_simplex ι) :=
begin
  refine λ f g hf hg a b ha hb hab, ⟨λ x, _, _⟩,
  { apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1] },
  { erw [finset.sum_add_distrib, ← finset.smul_sum, ← finset.smul_sum, hf.2, hg.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    exact hab }
end

variable {ι}

lemma ite_eq_mem_std_simplex (i : ι) : (λ j, ite (i = j) (1 : k) 0) ∈ std_simplex ι :=
⟨λ j, by simp only; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)]⟩

/-- `std_simplex ι` is the convex hull of the canonical basis in `ι → k`. -/
lemma convex_hull_basis_eq_std_simplex :
  convex_hull k (range $ λ (i j:ι), if i = j then (1 : k) else 0) = std_simplex ι :=
begin
  refine subset.antisymm (convex_hull_min _ (convex_std_simplex ι)) _,
  { rintro _ ⟨i, rfl⟩,
    exact ite_eq_mem_std_simplex i },
  { rintro w ⟨hw₀, hw₁⟩,
    rw [pi_eq_sum_univ w, ← finset.univ.center_mass_eq_of_sum_1 _ hw₁],
    exact finset.univ.center_mass_mem_convex_hull k (λ i hi, hw₀ i)
      (hw₁.symm ▸ zero_lt_one) (λ i hi, mem_range_self i) }
end

variable {ι}

/-- The convex hull of a finite set is the image of the standard simplex in `s → k`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → k) →ₗ[k] k` so that later we will not need
to prove that this map is linear. -/
lemma set.finite.convex_hull_eq_image {s : set E} (hs : finite s) :
  convex_hull k s = by haveI := hs.fintype; exact
    (⇑(∑ x : s, (@linear_map.proj k s _ (λ i, k) _ _ x).smul_right x.1)) '' (std_simplex s) :=
begin
  rw [← convex_hull_basis_eq_std_simplex, ← linear_map.convex_hull_image, ← set.range_comp, (∘)],
  apply congr_arg,
  convert subtype.range_coe.symm,
  ext x,
  simp [linear_map.sum_apply, ite_smul, finset.filter_eq]
end

/-- All values of a function `f ∈ std_simplex ι` belong to `[0, 1]`. -/
lemma mem_Icc_of_mem_std_simplex (hf : f ∈ std_simplex ι) (x) :
  f x ∈ I :=
⟨hf.1 x, hf.2 ▸ finset.single_le_sum (λ y hy, hf.1 y) (finset.mem_univ x)⟩

end simplex
