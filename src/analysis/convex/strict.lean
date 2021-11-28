/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import analysis.convex.basic
import topology.algebra.monoid

/-!
# Strictly strict_convex sets
-/

variables {𝕜 E F β : Type*}

open set
open_locale pointwise

/-!
### Strict convexity of sets

This file defines strictly convex sets.

-/

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [topological_space E] [add_comm_monoid F] [topological_space F]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E] [has_scalar 𝕜 F] (s : set E)

/-- Convexity of sets. -/
def strict_convex : Prop :=
s.pairwise (λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ interior s)

variables {𝕜 s}

lemma strict_convex_iff_open_segment_subset :
  strict_convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → open_segment 𝕜 x y ⊆ interior s :=
begin
  split,
  { rintro h x y hx hy z ⟨a, b, ha, hb, hab, rfl⟩,
    exact h hx hy ha hb hab },
  { rintro h x y hx hy a b ha hb hab,
    exact h hx hy ⟨a, b, ha, hb, hab, rfl⟩ }
end

lemma strict_convex.segment_subset (h : strict_convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  [x -[𝕜] y] ⊆ s :=
convex_iff_segment_subset.1 h hx hy

lemma strict_convex.open_segment_subset (h : strict_convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  open_segment 𝕜 x y ⊆ s :=
(open_segment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

/-- Alternative definition of set strict_convexity, in terms of pointwise set operations. -/
lemma strict_convex_iff_pointwise_add_subset :
  strict_convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
iff.intro
  begin
    rintro hA a b ha hb hab w ⟨au, bv, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩,
    exact hA hu hv ha hb hab
  end
  (λ h x y hx hy a b ha hb hab,
    (h ha hb hab) (set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩))

lemma strict_convex_empty : strict_convex 𝕜 (∅ : set E) := by finish

lemma strict_convex_univ : strict_convex 𝕜 (set.univ : set E) := λ _ _ _ _ _ _ _ _ _, trivial

lemma strict_convex.inter {t : set E} (hs : strict_convex 𝕜 s) (ht : strict_convex 𝕜 t) : strict_convex 𝕜 (s ∩ t) :=
λ x y (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) a b (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb hab⟩

lemma strict_convex_sInter {S : set (set E)} (h : ∀ s ∈ S, strict_convex 𝕜 s) : strict_convex 𝕜 (⋂₀ S) :=
assume x y hx hy a b ha hb hab s hs,
h s hs (hx s hs) (hy s hs) ha hb hab

lemma strict_convex_Inter {ι : Sort*} {s : ι → set E} (h : ∀ i : ι, strict_convex 𝕜 (s i)) :
  strict_convex 𝕜 (⋂ i, s i) :=
(sInter_range s) ▸ strict_convex_sInter $ forall_range_iff.2 h

lemma strict_convex.prod {s : set E} {t : set F} (hs : strict_convex 𝕜 s) (ht : strict_convex 𝕜 t) :
  strict_convex 𝕜 (s.prod t) :=
begin
  intros x y hx hy a b ha hb hab,
  apply mem_prod.2,
  exact ⟨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma strict_convex_pi {ι : Type*} {E : ι → Type*} [Π i, add_comm_monoid (E i)]
  [Π i, has_scalar 𝕜 (E i)] {s : set ι} {t : Π i, set (E i)} (ht : ∀ i, strict_convex 𝕜 (t i)) :
  strict_convex 𝕜 (s.pi t) :=
λ x y hx hy a b ha hb hab i hi, ht i (hx i hi) (hy i hi) ha hb hab

lemma directed.strict_convex_Union {ι : Sort*} {s : ι → set E} (hdir : directed (⊆) s)
  (hc : ∀ ⦃i : ι⦄, strict_convex 𝕜 (s i)) :
  strict_convex 𝕜 (⋃ i, s i) :=
begin
  rintro x y hx hy a b ha hb hab,
  rw mem_Union at ⊢ hx hy,
  obtain ⟨i, hx⟩ := hx,
  obtain ⟨j, hy⟩ := hy,
  obtain ⟨k, hik, hjk⟩ := hdir i j,
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩,
end

lemma directed_on.strict_convex_sUnion {c : set (set E)} (hdir : directed_on (⊆) c)
  (hc : ∀ ⦃A : set E⦄, A ∈ c → strict_convex 𝕜 A) :
  strict_convex 𝕜 (⋃₀c) :=
begin
  rw sUnion_eq_Union,
  exact (directed_on_iff_directed.1 hdir).strict_convex_Union (λ A, hc A.2),
end

end has_scalar

section module
variables [module 𝕜 E] [module 𝕜 F] {s : set E}

lemma strict_convex.convex (hs : strict_convex 𝕜 s) : convex 𝕜 s :=
convex_iff_forall_pos.2 $ λ x y hx hy a b ha hb hab, interior_subset $ hs hx hy ha hb hab

lemma convex.strict_convex (h : is_open s) (hs : convex 𝕜 s) : strict_convex 𝕜 s :=
λ x y hx hy a b ha hb hab, h.interior_eq.symm ▸ hs hx hy ha hb hab

lemma is_open.strict_convex_iff (h : is_open s) : strict_convex 𝕜 s ↔ convex 𝕜 s :=
⟨strict_convex.convex, convex.strict_convex h⟩

lemma strict_convex_iff_forall_pos :
  strict_convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
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

lemma strict_convex_iff_pairwise_pos :
  strict_convex 𝕜 s ↔ s.pairwise (λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s) :=
begin
  refine ⟨λ h x hx y hy _ a b ha hb hab, h hx hy ha.le hb.le hab, _⟩,
  intros h x y hx hy a b ha hb hab,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_add] at hab, rwa [hab, zero_smul, one_smul, zero_add] },
  obtain rfl | hb' := hb.eq_or_lt,
  { rw [add_zero] at hab, rwa [hab, zero_smul, one_smul, add_zero] },
  obtain rfl | hxy := eq_or_ne x y,
  { rwa strict_convex.combo_self hab },
  exact h _ hx _ hy hxy ha' hb' hab,
end

lemma strict_convex_iff_open_segment_subset :
  strict_convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → open_segment 𝕜 x y ⊆ s :=
begin
  rw strict_convex_iff_segment_subset,
  exact forall₂_congr (λ x y, forall₂_congr $ λ hx hy,
    (open_segment_subset_iff_segment_subset hx hy).symm),
end

lemma strict_convex_singleton (c : E) : strict_convex 𝕜 ({c} : set E) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [set.eq_of_mem_singleton hx, set.eq_of_mem_singleton hy, ←add_smul, hab, one_smul],
  exact mem_singleton c
end

lemma strict_convex.linear_image (hs : strict_convex 𝕜 s) (f : E →ₗ[𝕜] F) : strict_convex 𝕜 (s.image f) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx,
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy,
  exact ⟨a • x' + b • y', hs hx' hy' ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩,
end

lemma strict_convex.is_linear_image (hs : strict_convex 𝕜 s) {f : E → F} (hf : is_linear_map 𝕜 f) :
  strict_convex 𝕜 (f '' s) :=
hs.linear_image $ hf.mk' f

lemma strict_convex.linear_preimage {s : set F} (hs : strict_convex 𝕜 s) (f : E →ₗ[𝕜] F) :
  strict_convex 𝕜 (s.preimage f) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul],
  exact hs hx hy ha hb hab,
end

lemma strict_convex.is_linear_preimage {s : set F} (hs : strict_convex 𝕜 s) {f : E → F} (hf : is_linear_map 𝕜 f) :
  strict_convex 𝕜 (preimage f s) :=
hs.linear_preimage $ hf.mk' f

lemma strict_convex.add {t : set E} (hs : strict_convex 𝕜 s) (ht : strict_convex 𝕜 t) : strict_convex 𝕜 (s + t) :=
by { rw ← add_image_prod, exact (hs.prod ht).is_linear_image is_linear_map.is_linear_map_add }

lemma strict_convex.translate (hs : strict_convex 𝕜 s) (z : E) : strict_convex 𝕜 ((λ x, z + x) '' s) :=
begin
  intros x y hx hy a b ha hb hab,
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx,
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy,
  refine ⟨a • x' + b • y', hs hx' hy' ha hb hab, _⟩,
  rw [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul],
end

/-- The translation of a strict_convex set is also strict_convex. -/
lemma strict_convex.translate_preimage_right (hs : strict_convex 𝕜 s) (z : E) : strict_convex 𝕜 ((λ x, z + x) ⁻¹' s) :=
begin
  intros x y hx hy a b ha hb hab,
  have h := hs hx hy ha hb hab,
  rwa [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul] at h,
end

/-- The translation of a strict_convex set is also strict_convex. -/
lemma strict_convex.translate_preimage_left (hs : strict_convex 𝕜 s) (z : E) : strict_convex 𝕜 ((λ x, x + z) ⁻¹' s) :=
by simpa only [add_comm] using hs.translate_preimage_right z

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β] [module 𝕜 β] [ordered_smul 𝕜 β]

lemma strict_convex_Iic (r : β) : strict_convex 𝕜 (Iic r) :=
λ x y hx hy a b ha hb hab,
calc
  a • x + b • y
      ≤ a • r + b • r
      : add_le_add (smul_le_smul_of_nonneg hx ha) (smul_le_smul_of_nonneg hy hb)
  ... = r : strict_convex.combo_self hab _

lemma strict_convex_Ici (r : β) : strict_convex 𝕜 (Ici r) :=
@convex_Iic 𝕜 (order_dual β) _ _ _ _ r

lemma strict_convex_Icc (r s : β) : strict_convex 𝕜 (Icc r s) :=
Ici_inter_Iic.subst ((convex_Ici r).inter $ strict_convex_Iic s)

lemma strict_convex_halfspace_le {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  strict_convex 𝕜 {w | f w ≤ r} :=
(convex_Iic r).is_linear_preimage h

lemma strict_convex_halfspace_ge {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  strict_convex 𝕜 {w | r ≤ f w} :=
(convex_Ici r).is_linear_preimage h

lemma strict_convex_hyperplane {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  strict_convex 𝕜 {w | f w = r} :=
begin
  simp_rw le_antisymm_iff,
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r),
end

end ordered_add_comm_monoid

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid β] [module 𝕜 β] [ordered_smul 𝕜 β]

lemma strict_convex_Iio (r : β) : strict_convex 𝕜 (Iio r) :=
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
    ... = r : strict_convex.combo_self hab _
end

lemma strict_convex_Ioi (r : β) : strict_convex 𝕜 (Ioi r) :=
@convex_Iio 𝕜 (order_dual β) _ _ _ _ r

lemma strict_convex_Ioo (r s : β) : strict_convex 𝕜 (Ioo r s) :=
Ioi_inter_Iio.subst ((convex_Ioi r).inter $ strict_convex_Iio s)

lemma strict_convex_Ico (r s : β) : strict_convex 𝕜 (Ico r s) :=
Ici_inter_Iio.subst ((convex_Ici r).inter $ strict_convex_Iio s)

lemma strict_convex_Ioc (r s : β) : strict_convex 𝕜 (Ioc r s) :=
Ioi_inter_Iic.subst ((convex_Ioi r).inter $ strict_convex_Iic s)

lemma strict_convex_halfspace_lt {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  strict_convex 𝕜 {w | f w < r} :=
(convex_Iio r).is_linear_preimage h

lemma strict_convex_halfspace_gt {f : E → β} (h : is_linear_map 𝕜 f) (r : β) :
  strict_convex 𝕜 {w | r < f w} :=
(convex_Ioi r).is_linear_preimage h

end ordered_cancel_add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid β] [module 𝕜 β] [ordered_smul 𝕜 β]

lemma strict_convex_interval (r s : β) : strict_convex 𝕜 (interval r s) :=
convex_Icc _ _

end linear_ordered_add_comm_monoid
end module
end add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid E] [ordered_add_comm_monoid β] [module 𝕜 E]
  [ordered_smul 𝕜 E] {s : set E} {f : E → β}

lemma monotone_on.strict_convex_le (hf : monotone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | f x ≤ r} :=
λ x y hx hy a b ha hb hab, ⟨hs hx.1 hy.1 ha hb hab,
  (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (convex.combo_le_max x y ha hb hab)).trans
    (max_rec' _ hx.2 hy.2)⟩

lemma monotone_on.strict_convex_lt (hf : monotone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | f x < r} :=
λ x y hx hy a b ha hb hab, ⟨hs hx.1 hy.1 ha hb hab,
  (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (convex.combo_le_max x y ha hb hab)).trans_lt
    (max_rec' _ hx.2 hy.2)⟩

lemma monotone_on.strict_convex_ge (hf : monotone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | r ≤ f x} :=
@monotone_on.strict_convex_le 𝕜 (order_dual E) (order_dual β) _ _ _ _ _ _ _ hf.dual hs r

lemma monotone_on.strict_convex_gt (hf : monotone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | r < f x} :=
@monotone_on.strict_convex_lt 𝕜 (order_dual E) (order_dual β) _ _ _ _ _ _ _ hf.dual hs r

lemma antitone_on.strict_convex_le (hf : antitone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | f x ≤ r} :=
@monotone_on.strict_convex_ge 𝕜 E (order_dual β) _ _ _ _ _ _ _ hf hs r

lemma antitone_on.strict_convex_lt (hf : antitone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | f x < r} :=
@monotone_on.strict_convex_gt 𝕜 E (order_dual β) _ _ _ _ _ _ _ hf hs r

lemma antitone_on.strict_convex_ge (hf : antitone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | r ≤ f x} :=
@monotone_on.strict_convex_le 𝕜 E (order_dual β) _ _ _ _ _ _ _ hf hs r

lemma antitone_on.strict_convex_gt (hf : antitone_on f s) (hs : strict_convex 𝕜 s) (r : β) :
  strict_convex 𝕜 {x ∈ s | r < f x} :=
@monotone_on.strict_convex_lt 𝕜 E (order_dual β) _ _ _ _ _ _ _ hf hs r

lemma monotone.strict_convex_le (hf : monotone f) (r : β) :
  strict_convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.monotone_on univ).strict_convex_le strict_convex_univ r)

lemma monotone.strict_convex_lt (hf : monotone f) (r : β) :
  strict_convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.monotone_on univ).strict_convex_le strict_convex_univ r)

lemma monotone.strict_convex_ge (hf : monotone f ) (r : β) :
  strict_convex 𝕜 {x | r ≤ f x} :=
set.sep_univ.subst ((hf.monotone_on univ).strict_convex_ge strict_convex_univ r)

lemma monotone.strict_convex_gt (hf : monotone f) (r : β) :
  strict_convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.monotone_on univ).strict_convex_le strict_convex_univ r)

lemma antitone.strict_convex_le (hf : antitone f) (r : β) :
  strict_convex 𝕜 {x | f x ≤ r} :=
set.sep_univ.subst ((hf.antitone_on univ).strict_convex_le strict_convex_univ r)

lemma antitone.strict_convex_lt (hf : antitone f) (r : β) :
  strict_convex 𝕜 {x | f x < r} :=
set.sep_univ.subst ((hf.antitone_on univ).strict_convex_lt strict_convex_univ r)

lemma antitone.strict_convex_ge (hf : antitone f) (r : β) :
  strict_convex 𝕜 {x | r ≤ f x} :=
set.sep_univ.subst ((hf.antitone_on univ).strict_convex_ge strict_convex_univ r)

lemma antitone.strict_convex_gt (hf : antitone f) (r : β) :
  strict_convex 𝕜 {x | r < f x} :=
set.sep_univ.subst ((hf.antitone_on univ).strict_convex_gt strict_convex_univ r)

end linear_ordered_add_comm_monoid

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] {s t : set E}

lemma strict_convex.combo_eq_vadd {a b : 𝕜} {x y : E} (h : a + b = 1) :
  a • x + b • y = b • (y - x) + x :=
calc
  a • x + b • y = (b • y - b • x) + (a • x + b • x) : by abel
            ... = b • (y - x) + x                   : by rw [smul_sub, strict_convex.combo_self h]

lemma strict_convex.sub (hs : strict_convex 𝕜 s) (ht : strict_convex 𝕜 t) :
  strict_convex 𝕜 ((λ x : E × E, x.1 - x.2) '' (s.prod t)) :=
(hs.prod ht).is_linear_image is_linear_map.is_linear_map_sub

lemma strict_convex_segment (x y : E) : strict_convex 𝕜 [x -[𝕜] y] :=
begin
  rintro p q ⟨ap, bp, hap, hbp, habp, rfl⟩ ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab,
  refine ⟨a * ap + b * aq, a * bp + b * bq,
    add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
    add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), _, _⟩,
  { rw [add_add_add_comm, ←mul_add, ←mul_add, habp, habq, mul_one, mul_one, hab] },
  { simp_rw [add_smul, mul_smul, smul_add],
    exact add_add_add_comm _ _ _ _ }
end

lemma strict_convex_open_segment (a b : E) : strict_convex 𝕜 (open_segment 𝕜 a b) :=
begin
  rw strict_convex_iff_open_segment_subset,
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

lemma strict_convex.smul (hs : strict_convex 𝕜 s) (c : 𝕜) : strict_convex 𝕜 (c • s) :=
hs.linear_image (linear_map.lsmul _ _ c)

lemma strict_convex.smul_preimage (hs : strict_convex 𝕜 s) (c : 𝕜) : strict_convex 𝕜 ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma strict_convex.affinity (hs : strict_convex 𝕜 s) (z : E) (c : 𝕜) : strict_convex 𝕜 ((λ x, z + c • x) '' s) :=
begin
  have h := (hs.smul c).translate z,
  rwa [←image_smul, image_image] at h,
end

end add_comm_monoid
end ordered_comm_semiring

section ordered_ring
variables [ordered_ring 𝕜]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {s : set E}

lemma strict_convex.add_smul_mem (hs : strict_convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s)
  {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • y ∈ s :=
begin
  have h : x + t • y = (1 - t) • x + t • (x + y),
  { rw [smul_add, ←add_assoc, ←add_smul, sub_add_cancel, one_smul] },
  rw h,
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _),
end

lemma strict_convex.smul_mem_of_zero_mem (hs : strict_convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
  {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : t • x ∈ s :=
by simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

lemma strict_convex.add_smul_sub_mem (h : strict_convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • (y - x) ∈ s :=
begin
  apply h.segment_subset hx hy,
  rw segment_eq_image',
  exact mem_image_of_mem _ ht,
end

/-- Affine subspaces are strict_convex. -/
lemma affine_subspace.strict_convex (Q : affine_subspace 𝕜 E) : strict_convex 𝕜 (Q : set E) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [eq_sub_of_add_eq hab, ← affine_map.line_map_apply_module],
  exact affine_map.line_map_mem b hx hy,
end

/--
Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
lemma strict_convex.combo_affine_apply {a b : 𝕜} {x y : E} {f : E →ᵃ[𝕜] F} (h : a + b = 1) :
  f (a • x + b • y) = a • f x + b • f y :=
begin
  simp only [convex.combo_eq_vadd h, ← vsub_eq_sub],
  exact f.apply_line_map _ _ _,
end

/-- The preimage of a strict_convex set under an affine map is strict_convex. -/
lemma strict_convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : set F} (hs : strict_convex 𝕜 s) :
  strict_convex 𝕜 (f ⁻¹' s) :=
begin
  intros x y xs ys a b ha hb hab,
  rw [mem_preimage, strict_convex.combo_affine_apply hab],
  exact hs xs ys ha hb hab,
end

/-- The image of a strict_convex set under an affine map is strict_convex. -/
lemma strict_convex.affine_image (f : E →ᵃ[𝕜] F) {s : set E} (hs : strict_convex 𝕜 s) :
  strict_convex 𝕜 (f '' s) :=
begin
  rintro x y ⟨x', ⟨hx', hx'f⟩⟩ ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab,
  refine ⟨a • x' + b • y', ⟨hs hx' hy' ha hb hab, _⟩⟩,
  rw [convex.combo_affine_apply hab, hx'f, hy'f]
end

lemma strict_convex.neg (hs : strict_convex 𝕜 s) : strict_convex 𝕜 ((λ z, -z) '' s) :=
hs.is_linear_image is_linear_map.is_linear_map_neg

lemma strict_convex.neg_preimage (hs : strict_convex 𝕜 s) : strict_convex 𝕜 ((λ z, -z) ⁻¹' s) :=
hs.is_linear_preimage is_linear_map.is_linear_map_neg

end add_comm_group
end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {s : set E}

/-- Alternative definition of set strict_convexity, using division. -/
lemma strict_convex_iff_div :
  strict_convex 𝕜 s ↔ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄,
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

lemma strict_convex.mem_smul_of_zero_mem (h : strict_convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s)
  (hx : x ∈ s) {t : 𝕜} (ht : 1 ≤ t) :
  x ∈ t • s :=
begin
  rw mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne',
  exact h.smul_mem_of_zero_mem zero_mem hx ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one ht⟩,
end

lemma strict_convex.add_smul (h_conv : strict_convex 𝕜 s) {p q : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) :
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

lemma set.ord_connected.strict_convex_of_chain [ordered_semiring 𝕜] [ordered_add_comm_monoid E]
  [module 𝕜 E] [ordered_smul 𝕜 E] {s : set E} (hs : s.ord_connected) (h : zorn.chain (≤) s) :
  strict_convex 𝕜 s :=
begin
  intros x y hx hy a b ha hb hab,
  obtain hxy | hyx := h.total_of_refl hx hy,
  { refine hs.out hx hy (mem_Icc.2 ⟨_, _⟩),
    calc
      x   = a • x + b • x : (convex.combo_self hab _).symm
      ... ≤ a • x + b • y : add_le_add_left (smul_le_smul_of_nonneg hxy hb) _,
    calc
      a • x + b • y
          ≤ a • y + b • y : add_le_add_right (smul_le_smul_of_nonneg hxy ha) _
      ... = y : strict_convex.combo_self hab _ },
  { refine hs.out hy hx (mem_Icc.2 ⟨_, _⟩),
    calc
      y   = a • y + b • y : (convex.combo_self hab _).symm
      ... ≤ a • x + b • y : add_le_add_right (smul_le_smul_of_nonneg hyx ha) _,
    calc
      a • x + b • y
          ≤ a • x + b • x : add_le_add_left (smul_le_smul_of_nonneg hyx hb) _
      ... = x : strict_convex.combo_self hab _ }
end

lemma set.ord_connected.strict_convex [ordered_semiring 𝕜] [linear_ordered_add_comm_monoid E] [module 𝕜 E]
  [ordered_smul 𝕜 E] {s : set E} (hs : s.ord_connected) :
  strict_convex 𝕜 s :=
hs.strict_convex_of_chain (zorn.chain_of_trichotomous s)

lemma strict_convex_iff_ord_connected [linear_ordered_field 𝕜] {s : set 𝕜} :
  strict_convex 𝕜 s ↔ s.ord_connected :=
begin
  simp_rw [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset],
  exact forall_congr (λ x, forall_swap)
end

alias strict_convex_iff_ord_connected ↔ strict_convex.ord_connected _

end

/-! #### Convexity of submodules/subspaces -/

section submodule
open submodule

lemma submodule.strict_convex [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] (K : submodule 𝕜 E) :
  strict_convex 𝕜 (↑K : set E) :=
by { repeat {intro}, refine add_mem _ (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma subspace.strict_convex [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] (K : subspace 𝕜 E) :
  strict_convex 𝕜 (↑K : set E) :=
K.strict_convex

end submodule

/-! ### Simplex -/

section simplex

variables (𝕜) (ι : Type*) [ordered_semiring 𝕜] [fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of strict_convex spaces. -/
def std_simplex : set (ι → 𝕜) :=
{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

lemma std_simplex_eq_inter :
  std_simplex 𝕜 ι = (⋂ x, {f | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} :=
by { ext f, simp only [std_simplex, set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] }

lemma strict_convex_std_simplex : strict_convex 𝕜 (std_simplex 𝕜 ι) :=
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
