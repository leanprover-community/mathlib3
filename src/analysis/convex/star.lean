/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.basic

/-!
# Star-convex sets

This files defines star-convex sets (aka star domains, star-shaped set, radially convex set).

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `has_star` and co.

## Main declarations

* `star_convex 𝕜 x s`: `s` is star-convex at `x` with scalars `𝕜`.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.

## TODO

Balanced sets are star-convex.

The closure of a star-convex set is star-convex.

Star-convex sets are contractible.

A nonempty open star-convex set in `ℝ^n` is diffeomorphic to the entire space.
-/

open set
open_locale convex pointwise

variables {𝕜 E F β : Type*}

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E] [has_scalar 𝕜 F] (x : E) (s : set E)

/-- Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a point in `s` is
contained in `s`. -/
def star_convex : Prop :=
∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

variables {𝕜 x s} {t : set E}

lemma convex_iff_forall_star_convex : convex 𝕜 s ↔ ∀ x ∈ s, star_convex 𝕜 x s :=
forall_congr $ λ x, forall_swap

lemma convex.star_convex (h : convex 𝕜 s) (hx : x ∈ s) : star_convex 𝕜 x s :=
convex_iff_forall_star_convex.1 h _ hx

lemma star_convex_iff_segment_subset : star_convex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s :=
begin
  split,
  { rintro h y hy z ⟨a, b, ha, hb, hab, rfl⟩,
    exact h hy ha hb hab },
  { rintro h y hy a b ha hb hab,
    exact h hy ⟨a, b, ha, hb, hab, rfl⟩ }
end

lemma star_convex.segment_subset (h : star_convex 𝕜 x s) {y : E} (hy : y ∈ s) : [x -[𝕜] y] ⊆ s :=
star_convex_iff_segment_subset.1 h hy

lemma star_convex.open_segment_subset (h : star_convex 𝕜 x s) {y : E} (hy : y ∈ s) :
  open_segment 𝕜 x y ⊆ s :=
(open_segment_subset_segment 𝕜 x y).trans (h.segment_subset hy)

/-- Alternative definition of star-convexity, in terms of pointwise set operations. -/
lemma star_convex_iff_pointwise_add_subset :
  star_convex 𝕜 x s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • {x} + b • s ⊆ s :=
begin
  refine ⟨_, λ h y hy a b ha hb hab,
    h ha hb hab (add_mem_add (smul_mem_smul_set $ mem_singleton _) ⟨_, hy, rfl⟩)⟩,
  rintro hA a b ha hb hab w ⟨au, bv, ⟨u, (rfl : u = x), rfl⟩, ⟨v, hv, rfl⟩, rfl⟩,
  exact hA hv ha hb hab,
end

lemma star_convex_empty (x : E) : star_convex 𝕜 x ∅ := λ y hy, hy.elim

lemma star_convex_univ (x : E) : star_convex 𝕜 x univ := λ _ _ _ _ _ _ _, trivial

lemma star_convex.inter (hs : star_convex 𝕜 x s) (ht : star_convex 𝕜 x t) :
  star_convex 𝕜 x (s ∩ t) :=
λ y hy a b ha hb hab, ⟨hs hy.left ha hb hab, ht hy.right ha hb hab⟩

lemma star_convex_sInter {S : set (set E)} (h : ∀ s ∈ S, star_convex 𝕜 x s) :
  star_convex 𝕜 x (⋂₀ S) :=
λ y hy a b ha hb hab s hs, h s hs (hy s hs) ha hb hab

lemma star_convex_Inter {ι : Sort*} {s : ι → set E} (h : ∀ i, star_convex 𝕜 x (s i)) :
  star_convex 𝕜 x (⋂ i, s i) :=
(sInter_range s) ▸ star_convex_sInter $ forall_range_iff.2 h

lemma star_convex.union (hs : star_convex 𝕜 x s) (ht : star_convex 𝕜 x t) :
  star_convex 𝕜 x (s ∪ t) :=
begin
  rintro y (hy | hy) a b ha hb hab,
  { exact or.inl (hs hy ha hb hab) },
  { exact or.inr (ht hy ha hb hab) }
end

lemma star_convex_Union {ι : Sort*} {s : ι → set E} (hs : ∀ i, star_convex 𝕜 x (s i)) :
  star_convex 𝕜 x (⋃ i, s i) :=
begin
  rintro y hy a b ha hb hab,
  rw mem_Union at ⊢ hy,
  obtain ⟨i, hy⟩ := hy,
  exact ⟨i, hs i hy ha hb hab⟩,
end

lemma star_convex_sUnion {S : set (set E)} (hS : ∀ s ∈ S, star_convex 𝕜 x s) :
  star_convex 𝕜 x (⋃₀ S) :=
begin
  rw sUnion_eq_Union,
  exact star_convex_Union (λ s, hS _ s.2),
end

lemma star_convex.prod {y : F} {s : set E} {t : set F} (hs : star_convex 𝕜 x s)
  (ht : star_convex 𝕜 y t) :
  star_convex 𝕜 (x, y) (s ×ˢ t) :=
λ y hy a b ha hb hab, ⟨hs hy.1 ha hb hab, ht hy.2 ha hb hab⟩

lemma star_convex_pi {ι : Type*} {E : ι → Type*} [Π i, add_comm_monoid (E i)]
  [Π i, has_scalar 𝕜 (E i)] {x : Π i, E i} {s : set ι} {t : Π i, set (E i)}
  (ht : ∀ i, star_convex 𝕜 (x i) (t i)) :
  star_convex 𝕜 x (s.pi t) :=
λ y hy a b ha hb hab i hi, ht i (hy i hi) ha hb hab

end has_scalar

section module
variables [module 𝕜 E] [module 𝕜 F] {x y z : E} {s : set E}

lemma star_convex.mem (hs : star_convex 𝕜 x s) (h : s.nonempty) : x ∈ s :=
begin
  obtain ⟨y, hy⟩ := h,
  convert hs hy zero_le_one le_rfl (add_zero 1),
  rw [one_smul, zero_smul, add_zero],
end

lemma convex.star_convex_iff (hs : convex 𝕜 s) (h : s.nonempty) : star_convex 𝕜 x s ↔ x ∈ s :=
⟨λ hxs, hxs.mem h, hs.star_convex⟩

lemma star_convex_iff_forall_pos (hx : x ∈ s) :
  star_convex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
begin
  refine ⟨λ h y hy a b ha hb hab, h hy ha.le hb.le hab, _⟩,
  intros h y hy a b ha hb hab,
  obtain rfl | ha := ha.eq_or_lt,
  { rw zero_add at hab,
    rwa [hab, one_smul, zero_smul, zero_add] },
  obtain rfl | hb := hb.eq_or_lt,
  { rw add_zero at hab,
    rwa [hab, one_smul, zero_smul, add_zero] },
  exact h hy ha hb hab,
end

lemma star_convex_iff_forall_ne_pos (hx : x ∈ s) :
  star_convex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    a • x + b • y ∈ s :=
begin
  refine ⟨λ h y hy _ a b ha hb hab, h hy ha.le hb.le hab, _⟩,
  intros h y hy a b ha hb hab,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_add] at hab, rwa [hab, zero_smul, one_smul, zero_add] },
  obtain rfl | hb' := hb.eq_or_lt,
  { rw [add_zero] at hab, rwa [hab, zero_smul, one_smul, add_zero] },
  obtain rfl | hxy := eq_or_ne x y,
  { rwa convex.combo_self hab },
  exact h hy hxy ha' hb' hab,
end

lemma star_convex_iff_open_segment_subset (hx : x ∈ s) :
  star_convex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → open_segment 𝕜 x y ⊆ s :=
star_convex_iff_segment_subset.trans $ forall₂_congr $ λ y hy,
  (open_segment_subset_iff_segment_subset hx hy).symm

lemma star_convex_singleton (x : E) : star_convex 𝕜 x {x} :=
begin
  rintro y (rfl : y = x) a b ha hb hab,
  exact convex.combo_self hab _,
end

lemma star_convex.linear_image (hs : star_convex 𝕜 x s) (f : E →ₗ[𝕜] F) :
  star_convex 𝕜 (f x) (s.image f) :=
begin
  intros y hy a b ha hb hab,
  obtain ⟨y', hy', rfl⟩ := hy,
  exact ⟨a • x + b • y', hs hy' ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩,
end

lemma star_convex.is_linear_image (hs : star_convex 𝕜 x s) {f : E → F} (hf : is_linear_map 𝕜 f) :
  star_convex 𝕜 (f x) (f '' s) :=
hs.linear_image $ hf.mk' f

lemma star_convex.linear_preimage {s : set F} (f : E →ₗ[𝕜] F) (hs : star_convex 𝕜 (f x) s) :
  star_convex 𝕜 x (s.preimage f) :=
begin
  intros y hy a b ha hb hab,
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul],
  exact hs hy ha hb hab,
end

lemma star_convex.is_linear_preimage {s : set F} {f : E → F} (hs : star_convex 𝕜 (f x) s)
  (hf : is_linear_map 𝕜 f) :
  star_convex 𝕜 x (preimage f s) :=
hs.linear_preimage $ hf.mk' f

lemma star_convex.add {t : set E} (hs : star_convex 𝕜 x s) (ht : star_convex 𝕜 y t) :
  star_convex 𝕜 (x + y) (s + t) :=
by { rw ←add_image_prod, exact (hs.prod ht).is_linear_image is_linear_map.is_linear_map_add }

lemma star_convex.add_left (hs : star_convex 𝕜 x s) (z : E) :
  star_convex 𝕜 (z + x) ((λ x, z + x) '' s) :=
begin
  intros y hy a b ha hb hab,
  obtain ⟨y', hy', rfl⟩ := hy,
  refine ⟨a • x + b • y', hs hy' ha hb hab, _⟩,
  rw [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul],
end

lemma star_convex.add_right (hs : star_convex 𝕜 x s) (z : E) :
  star_convex 𝕜 (x + z) ((λ x, x + z) '' s) :=
begin
  intros y hy a b ha hb hab,
  obtain ⟨y', hy', rfl⟩ := hy,
  refine ⟨a • x + b • y', hs hy' ha hb hab, _⟩,
  rw [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul],
end

/-- The translation of a star-convex set is also star-convex. -/
lemma star_convex.preimage_add_right (hs : star_convex 𝕜 (z + x) s) :
  star_convex 𝕜 x ((λ x, z + x) ⁻¹' s) :=
begin
  intros y hy a b ha hb hab,
  have h := hs hy ha hb hab,
  rwa [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul] at h,
end

/-- The translation of a star-convex set is also star-convex. -/
lemma star_convex.preimage_add_left (hs : star_convex 𝕜 (x + z) s) :
  star_convex 𝕜 x ((λ x, x + z) ⁻¹' s) :=
begin
  rw add_comm at hs,
  simpa only [add_comm] using hs.preimage_add_right,
end

end module
end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] {x y : E}

lemma star_convex.sub' {s : set (E × E)} (hs : star_convex 𝕜 (x, y) s) :
  star_convex 𝕜 (x - y) ((λ x : E × E, x.1 - x.2) '' s) :=
hs.is_linear_image is_linear_map.is_linear_map_sub

end add_comm_group
end ordered_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F] [module 𝕜 E] [module 𝕜 F] {x : E} {s : set E}

lemma star_convex.smul (hs : star_convex 𝕜 x s) (c : 𝕜) : star_convex 𝕜 (c • x) (c • s) :=
hs.linear_image $ linear_map.lsmul _ _ c

lemma star_convex.preimage_smul {c : 𝕜} (hs : star_convex 𝕜 (c • x) s) :
  star_convex 𝕜 x ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma star_convex.affinity (hs : star_convex 𝕜 x s) (z : E) (c : 𝕜) :
  star_convex 𝕜 (z + c • x) ((λ x, z + c • x) '' s) :=
begin
  have h := (hs.smul c).add_left z,
  rwa [←image_smul, image_image] at h,
end

end add_comm_monoid
end ordered_comm_semiring

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [smul_with_zero 𝕜 E]{s : set E}

lemma star_convex_zero_iff :
  star_convex 𝕜 0 s ↔ ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃a : 𝕜⦄, 0 ≤ a → a ≤ 1 → a • x ∈ s :=
begin
  refine forall_congr (λ x, forall_congr $ λ hx, ⟨λ h a ha₀ ha₁, _, λ h a b ha hb hab, _⟩),
  { simpa only [sub_add_cancel, eq_self_iff_true, forall_true_left, zero_add, smul_zero'] using
      h (sub_nonneg_of_le ha₁) ha₀ },
  { rw [smul_zero', zero_add],
    exact h hb (by { rw ←hab, exact le_add_of_nonneg_left ha }) }
end

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {x y : E} {s t : set E}

lemma star_convex.add_smul_mem (hs : star_convex 𝕜 x s) (hy : x + y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
  (ht₁ : t ≤ 1) :
  x + t • y ∈ s :=
begin
  have h : x + t • y = (1 - t) • x + t • (x + y),
  { rw [smul_add, ←add_assoc, ←add_smul, sub_add_cancel, one_smul] },
  rw h,
  exact hs hy (sub_nonneg_of_le ht₁) ht₀ (sub_add_cancel _ _),
end

lemma star_convex.smul_mem (hs : star_convex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
  (ht₁ : t ≤ 1) :
  t • x ∈ s :=
by simpa using hs.add_smul_mem (by simpa using hx) ht₀ ht₁

lemma star_convex.add_smul_sub_mem (hs : star_convex 𝕜 x s) (hy : y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
  (ht₁ : t ≤ 1) :
  x + t • (y - x) ∈ s :=
begin
  apply hs.segment_subset hy,
  rw segment_eq_image',
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩,
end

/-- The preimage of a star-convex set under an affine map is star-convex. -/
lemma star_convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : set F} (hs : star_convex 𝕜 (f x) s) :
  star_convex 𝕜 x (f ⁻¹' s) :=
begin
  intros y hy a b ha hb hab,
  rw [mem_preimage, convex.combo_affine_apply hab],
  exact hs hy ha hb hab,
end

/-- The image of a star-convex set under an affine map is star-convex. -/
lemma star_convex.affine_image (f : E →ᵃ[𝕜] F) {s : set E} (hs : star_convex 𝕜 x s) :
  star_convex 𝕜 (f x) (f '' s) :=
begin
  rintro y ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab,
  refine ⟨a • x + b • y', ⟨hs hy' ha hb hab, _⟩⟩,
  rw [convex.combo_affine_apply hab, hy'f],
end

lemma star_convex.neg (hs : star_convex 𝕜 x s) : star_convex 𝕜 (-x) (-s) :=
by { rw ←image_neg, exact hs.is_linear_image is_linear_map.is_linear_map_neg }

lemma star_convex.sub (hs : star_convex 𝕜 x s) (ht : star_convex 𝕜 y t) :
  star_convex 𝕜 (x - y) (s - t) :=
by { simp_rw sub_eq_add_neg, exact hs.add ht.neg }

end add_comm_group
end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] {x : E} {s : set E}

/-- Alternative definition of star-convexity, using division. -/
lemma star_convex_iff_div :
  star_convex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
⟨λ h y hy a b ha hb hab, begin
  apply h hy,
  { have ha', from mul_le_mul_of_nonneg_left ha (inv_pos.2 hab).le,
    rwa [mul_zero, ←div_eq_inv_mul] at ha' },
  { have hb', from mul_le_mul_of_nonneg_left hb (inv_pos.2 hab).le,
    rwa [mul_zero, ←div_eq_inv_mul] at hb' },
  { rw ←add_div,
    exact div_self hab.ne' }
end, λ h y hy a b ha hb hab,
begin
  have h', from h hy ha hb,
  rw [hab, div_one, div_one] at h',
  exact h' zero_lt_one
end⟩

lemma star_convex.mem_smul (hs : star_convex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht : 1 ≤ t) :
  x ∈ t • s :=
begin
  rw mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne',
  exact hs.smul_mem hx (inv_nonneg.2 $ zero_le_one.trans ht) (inv_le_one ht),
end

end add_comm_group
end linear_ordered_field

/-!
#### Star-convex sets in an ordered space

Relates `star_convex` and `set.ord_connected`.
-/

section ord_connected

lemma set.ord_connected.star_convex [ordered_semiring 𝕜] [ordered_add_comm_monoid E]
  [module 𝕜 E] [ordered_smul 𝕜 E] {x : E} {s : set E} (hs : s.ord_connected) (hx : x ∈ s)
  (h : ∀ y ∈ s, x ≤ y ∨ y ≤ x) :
  star_convex 𝕜 x s :=
begin
  intros y hy a b ha hb hab,
  obtain hxy | hyx := h _ hy,
  { refine hs.out hx hy (mem_Icc.2 ⟨_, _⟩),
    calc
      x   = a • x + b • x : (convex.combo_self hab _).symm
      ... ≤ a • x + b • y : add_le_add_left (smul_le_smul_of_nonneg hxy hb) _,
    calc
      a • x + b • y
          ≤ a • y + b • y : add_le_add_right (smul_le_smul_of_nonneg hxy ha) _
      ... = y             : convex.combo_self hab _ },
  { refine hs.out hy hx (mem_Icc.2 ⟨_, _⟩),
    calc
      y   = a • y + b • y : (convex.combo_self hab _).symm
      ... ≤ a • x + b • y : add_le_add_right (smul_le_smul_of_nonneg hyx ha) _,
    calc
      a • x + b • y
          ≤ a • x + b • x : add_le_add_left (smul_le_smul_of_nonneg hyx hb) _
      ... = x             : convex.combo_self hab _ }
end

lemma star_convex_iff_ord_connected [linear_ordered_field 𝕜] {x : 𝕜} {s : set 𝕜} (hx : x ∈ s) :
  star_convex 𝕜 x s ↔ s.ord_connected :=
by simp_rw [ord_connected_iff_interval_subset_left hx, star_convex_iff_segment_subset,
  segment_eq_interval]

alias star_convex_iff_ord_connected ↔ star_convex.ord_connected _

end ord_connected

/-! #### Star-convexity of submodules/subspaces -/

section submodule
open submodule

lemma submodule.star_convex [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  (K : submodule 𝕜 E) :
  star_convex 𝕜 (0 : E) K :=
K.convex.star_convex K.zero_mem

lemma subspace.star_convex [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]
  (K : subspace 𝕜 E) :
  star_convex 𝕜 (0 : E) K :=
K.convex.star_convex K.zero_mem

end submodule
