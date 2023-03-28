/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import algebra.order.module
import analysis.convex.star
import linear_algebra.affine_space.affine_subspace

/-!
# Convex sets and functions in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.
* `std_simplex 𝕜 ι`: The standard simplex in `ι → 𝕜` (currently requires `fintype ι`). It is the
  intersection of the positive quadrant with the hyperplane `s.sum = 1`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex.

## TODO

Generalize all this file to affine spaces.
-/

variables {𝕜 E F β : Type*}

open linear_map set
open_locale big_operators classical convex pointwise

/-! ### Convexity of sets -/

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F]

section has_smul
variables (𝕜) [has_smul 𝕜 E] [has_smul 𝕜 F] (s : set E) {x : E}

/-- Convexity of sets. -/
def convex : Prop := ∀ ⦃x : E⦄, x ∈ s → star_convex 𝕜 x s

variables {𝕜 s}

lemma convex.star_convex (hs : convex 𝕜 s) (hx : x ∈ s) : star_convex 𝕜 x s := hs hx

lemma convex_iff_segment_subset : convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s :=
forall₂_congr $ λ x hx, star_convex_iff_segment_subset

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
  (λ h x hx y hy a b ha hb hab,
    (h ha hb hab) (set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩))

alias convex_iff_pointwise_add_subset ↔ convex.set_combo_subset _

lemma convex_empty : convex 𝕜 (∅ : set E) := λ x, false.elim

lemma convex_univ : convex 𝕜 (set.univ : set E) := λ _ _, star_convex_univ _

lemma convex.inter {t : set E} (hs : convex 𝕜 s) (ht : convex 𝕜 t) : convex 𝕜 (s ∩ t) :=
λ x hx, (hs hx.1).inter (ht hx.2)

lemma convex_sInter {S : set (set E)} (h : ∀ s ∈ S, convex 𝕜 s) : convex 𝕜 (⋂₀ S) :=
λ x hx, star_convex_sInter $ λ s hs, h _ hs $ hx _ hs

lemma convex_Inter {ι : Sort*} {s : ι → set E} (h : ∀ i, convex 𝕜 (s i)) : convex 𝕜 (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

lemma convex_Inter₂ {ι : Sort*} {κ : ι → Sort*} {s : Π i, κ i → set E}
  (h : ∀ i j, convex 𝕜 (s i j)) :
  convex 𝕜 (⋂ i j, s i j) :=
convex_Inter $ λ i, convex_Inter $ h i

lemma convex.prod {s : set E} {t : set F} (hs : convex 𝕜 s) (ht : convex 𝕜 t) : convex 𝕜 (s ×ˢ t) :=
λ x hx, (hs hx.1).prod (ht hx.2)

lemma convex_pi {ι : Type*} {E : ι → Type*} [Π i, add_comm_monoid (E i)]
  [Π i, has_smul 𝕜 (E i)] {s : set ι} {t : Π i, set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → convex 𝕜 (t i)) :
  convex 𝕜 (s.pi t) :=
λ x hx, star_convex_pi $ λ i hi, ht hi $ hx _ hi

lemma directed.convex_Union {ι : Sort*} {s : ι → set E} (hdir : directed (⊆) s)
  (hc : ∀ ⦃i : ι⦄, convex 𝕜 (s i)) :
  convex 𝕜 (⋃ i, s i) :=
begin
  rintro x hx y hy a b ha hb hab,
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

end has_smul

section module
variables [module 𝕜 E] [module 𝕜 F] {s : set E} {x : E}

lemma convex_iff_open_segment_subset :
  convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → open_segment 𝕜 x y ⊆ s :=
forall₂_congr $ λ x, star_convex_iff_open_segment_subset

lemma convex_iff_forall_pos :
  convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
  → a • x + b • y ∈ s :=
forall₂_congr $ λ x, star_convex_iff_forall_pos

lemma convex_iff_pairwise_pos :
  convex 𝕜 s ↔ s.pairwise (λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s) :=
begin
  refine convex_iff_forall_pos.trans ⟨λ h x hx y hy _, h hx hy, _⟩,
  intros h x hx y hy a b ha hb hab,
  obtain rfl | hxy := eq_or_ne x y,
  { rwa convex.combo_self hab },
  { exact h hx hy hxy ha hb hab },
end

lemma convex.star_convex_iff (hs : convex 𝕜 s) (h : s.nonempty) : star_convex 𝕜 x s ↔ x ∈ s :=
⟨λ hxs, hxs.mem h, hs.star_convex⟩

protected lemma set.subsingleton.convex {s : set E} (h : s.subsingleton) : convex 𝕜 s :=
convex_iff_pairwise_pos.mpr (h.pairwise _)

lemma convex_singleton (c : E) : convex 𝕜 ({c} : set E) :=
subsingleton_singleton.convex

lemma convex_segment (x y : E) : convex 𝕜 [x -[𝕜] y] :=
begin
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab,
  refine ⟨a * ap + b * aq, a * bp + b * bq,
    add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
    add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), _, _⟩,
  { rw [add_add_add_comm, ←mul_add, ←mul_add, habp, habq, mul_one, mul_one, hab] },
  { simp_rw [add_smul, mul_smul, smul_add],
    exact add_add_add_comm _ _ _ _ }
end

lemma convex.linear_image (hs : convex 𝕜 s) (f : E →ₗ[𝕜] F) : convex 𝕜 (f '' s) :=
begin
  intros x hx y hy a b ha hb hab,
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
  intros x hx y hy a b ha hb hab,
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
  intros x hx y hy a b ha hb hab,
  have h := hs hx hy ha hb hab,
  rwa [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul] at h,
end

/-- The translation of a convex set is also convex. -/
lemma convex.translate_preimage_left (hs : convex 𝕜 s) (z : E) : convex 𝕜 ((λ x, x + z) ⁻¹' s) :=
by simpa only [add_comm] using hs.translate_preimage_right z

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β] [module 𝕜 β] [ordered_smul 𝕜 β]

lemma convex_Iic (r : β) : convex 𝕜 (Iic r) :=
λ x hx y hy a b ha hb hab,
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
  intros x hx y hy a b ha hb hab,
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

lemma convex_uIcc (r s : β) : convex 𝕜 (uIcc r s) := convex_Icc _ _

end linear_ordered_add_comm_monoid
end module
end add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid E] [ordered_add_comm_monoid β] [module 𝕜 E]
  [ordered_smul 𝕜 E] {s : set E} {f : E → β}

lemma monotone_on.convex_le (hf : monotone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | f x ≤ r} :=
λ x hx y hy a b ha hb hab, ⟨hs hx.1 hy.1 ha hb hab,
  (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (convex.combo_le_max x y ha hb hab)).trans
    (max_rec' _ hx.2 hy.2)⟩

lemma monotone_on.convex_lt (hf : monotone_on f s) (hs : convex 𝕜 s) (r : β) :
  convex 𝕜 {x ∈ s | f x < r} :=
λ x hx y hy a b ha hb hab, ⟨hs hx.1 hy.1 ha hb hab,
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

section strict_ordered_comm_semiring
variables [strict_ordered_comm_semiring 𝕜] [add_comm_group E] [module 𝕜 E]

lemma convex_open_segment (a b : E) : convex 𝕜 (open_segment 𝕜 a b) :=
begin
  rw convex_iff_open_segment_subset,
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩,
  refine ⟨a * ap + b * aq, a * bp + b * bq, by positivity, by positivity, _, _⟩,
  { rw [add_add_add_comm, ←mul_add, ←mul_add, habp, habq, mul_one, mul_one, hab] },
  { simp_rw [add_smul, mul_smul, smul_add, add_add_add_comm] }
end

end strict_ordered_comm_semiring

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
  intros x hx y hy a b ha hb hab,
  rw [eq_sub_of_add_eq hab, ← affine_map.line_map_apply_module],
  exact affine_map.line_map_mem b hx hy,
end

/-- The preimage of a convex set under an affine map is convex. -/
lemma convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : set F} (hs : convex 𝕜 s) :
  convex 𝕜 (f ⁻¹' s) :=
λ x hx, (hs hx).affine_preimage _

/-- The image of a convex set under an affine map is convex. -/
lemma convex.affine_image (f : E →ᵃ[𝕜] F) (hs : convex 𝕜 s) : convex 𝕜 (f '' s) :=
by { rintro _ ⟨x, hx, rfl⟩, exact (hs hx).affine_image _ }

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
  convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄,
    0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
forall₂_congr $ λ x hx, star_convex_iff_div

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
    refine mem_smul_set.2 ⟨_, h_conv h₁₂ h₂₂ _ _
      (by rw [←div_self hpq.ne', add_div] : p / (p + q) + q / (p + q) = 1),
      by simp only [← mul_smul, smul_add, mul_div_cancel' _ hpq.ne']⟩; positivity }
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
  refine convex_iff_segment_subset.mpr (λ x hx y hy, _),
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
by simp_rw [convex_iff_segment_subset, segment_eq_uIcc, ord_connected_iff_uIcc_subset]

alias convex_iff_ord_connected ↔ convex.ord_connected _

end

/-! #### Convexity of submodules/subspaces -/

namespace submodule
variables [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]

protected lemma convex (K : submodule 𝕜 E) : convex 𝕜 (↑K : set E) :=
by { repeat {intro}, refine add_mem (smul_mem _ _ _) (smul_mem _ _ _); assumption }

protected lemma star_convex (K : submodule 𝕜 E) : star_convex 𝕜 (0 : E) K := K.convex K.zero_mem

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
by { ext f, simp only [std_simplex, set.mem_inter_iff, set.mem_Inter, set.mem_set_of_eq] }

lemma convex_std_simplex : convex 𝕜 (std_simplex 𝕜 ι) :=
begin
  refine λ f hf g hg a b ha hb hab, ⟨λ x, _, _⟩,
  { apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1] },
  { erw [finset.sum_add_distrib, ← finset.smul_sum, ← finset.smul_sum, hf.2, hg.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    exact hab }
end

variable {ι}

lemma ite_eq_mem_std_simplex (i : ι) : (λ j, ite (i = j) (1:𝕜) 0) ∈ std_simplex 𝕜 ι :=
⟨λ j, by simp only; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)]⟩

end simplex
