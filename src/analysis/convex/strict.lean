/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.basic
import topology.algebra.order.basic

/-!
# Strictly convex sets

This file defines strictly convex sets.

A set is strictly convex if the open segment between any two distinct points lies in its interior.
-/

open set
open_locale convex pointwise

variables {𝕜 𝕝 E F β : Type*}

open function set
open_locale convex

section ordered_semiring
variables [ordered_semiring 𝕜] [topological_space E] [topological_space F]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E] [has_scalar 𝕜 F] (s : set E)

/-- A set is strictly convex if the open segment between any two distinct points lies is in its
interior. This basically means "convex and not flat on the boundary". -/
def strict_convex : Prop :=
s.pairwise $ λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ interior s

variables {𝕜 s} {x y : E} {a b : 𝕜}

lemma strict_convex_iff_open_segment_subset :
  strict_convex 𝕜 s ↔ s.pairwise (λ x y, open_segment 𝕜 x y ⊆ interior s) :=
forall₅_congr $ λ x hx y hy hxy, (open_segment_subset_iff 𝕜).symm

lemma strict_convex.open_segment_subset (hs : strict_convex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s)
  (h : x ≠ y) :
  open_segment 𝕜 x y ⊆ interior s :=
strict_convex_iff_open_segment_subset.1 hs hx hy h

lemma strict_convex_empty : strict_convex 𝕜 (∅ : set E) := pairwise_empty _

lemma strict_convex_univ : strict_convex 𝕜 (univ : set E) :=
begin
  intros x hx y hy hxy a b ha hb hab,
  rw interior_univ,
  exact mem_univ _,
end

protected lemma strict_convex.eq (hs : strict_convex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a)
  (hb : 0 < b) (hab : a + b = 1) (h : a • x + b • y ∉ interior s) : x = y :=
hs.eq hx hy $ λ H, h $ H ha hb hab

protected lemma strict_convex.inter {t : set E} (hs : strict_convex 𝕜 s) (ht : strict_convex 𝕜 t) :
  strict_convex 𝕜 (s ∩ t) :=
begin
  intros x hx y hy hxy a b ha hb hab,
  rw interior_inter,
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩,
end

lemma directed.strict_convex_Union {ι : Sort*} {s : ι → set E} (hdir : directed (⊆) s)
  (hs : ∀ ⦃i : ι⦄, strict_convex 𝕜 (s i)) :
  strict_convex 𝕜 (⋃ i, s i) :=
begin
  rintro x hx y hy hxy a b ha hb hab,
  rw mem_Union at hx hy,
  obtain ⟨i, hx⟩ := hx,
  obtain ⟨j, hy⟩ := hy,
  obtain ⟨k, hik, hjk⟩ := hdir i j,
  exact interior_mono (subset_Union s k) (hs (hik hx) (hjk hy) hxy ha hb hab),
end

lemma directed_on.strict_convex_sUnion {S : set (set E)} (hdir : directed_on (⊆) S)
  (hS : ∀ s ∈ S, strict_convex 𝕜 s) :
  strict_convex 𝕜 (⋃₀ S) :=
begin
  rw sUnion_eq_Union,
  exact (directed_on_iff_directed.1 hdir).strict_convex_Union (λ s, hS _ s.2),
end

end has_scalar

section module
variables [module 𝕜 E] [module 𝕜 F] {s : set E}

protected lemma strict_convex.convex (hs : strict_convex 𝕜 s) : convex 𝕜 s :=
convex_iff_pairwise_pos.2 $ λ x hx y hy hxy a b ha hb hab, interior_subset $ hs hx hy hxy ha hb hab

/-- An open convex set is strictly convex. -/
protected lemma convex.strict_convex (h : is_open s) (hs : convex 𝕜 s) : strict_convex 𝕜 s :=
λ x hx y hy _ a b ha hb hab, h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab

lemma is_open.strict_convex_iff (h : is_open s) : strict_convex 𝕜 s ↔ convex 𝕜 s :=
⟨strict_convex.convex, convex.strict_convex h⟩

lemma strict_convex_singleton (c : E) : strict_convex 𝕜 ({c} : set E) := pairwise_singleton _ _

lemma set.subsingleton.strict_convex (hs : s.subsingleton) : strict_convex 𝕜 s := hs.pairwise _

lemma strict_convex.linear_image [semiring 𝕝] [module 𝕝 E] [module 𝕝 F]
  [linear_map.compatible_smul E F 𝕜 𝕝] (hs : strict_convex 𝕜 s) (f : E →ₗ[𝕝] F)
  (hf : is_open_map f) :
  strict_convex 𝕜 (f '' s) :=
begin
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab,
  refine hf.image_interior_subset _ ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, _⟩,
  rw [map_add, f.map_smul_of_tower a, f.map_smul_of_tower b]
end

lemma strict_convex.is_linear_image (hs : strict_convex 𝕜 s) {f : E → F} (h : is_linear_map 𝕜 f)
  (hf : is_open_map f) :
  strict_convex 𝕜 (f '' s) :=
hs.linear_image (h.mk' f) hf

lemma strict_convex.linear_preimage {s : set F} (hs : strict_convex 𝕜 s) (f : E →ₗ[𝕜] F)
  (hf : continuous f) (hfinj : injective f) :
  strict_convex 𝕜 (s.preimage f) :=
begin
  intros x hx y hy hxy a b ha hb hab,
  refine preimage_interior_subset_interior_preimage hf _,
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul],
  exact hs hx hy (hfinj.ne hxy) ha hb hab,
end

lemma strict_convex.is_linear_preimage {s : set F} (hs : strict_convex 𝕜 s) {f : E → F}
  (h : is_linear_map 𝕜 f) (hf : continuous f) (hfinj : injective f) :
  strict_convex 𝕜 (s.preimage f) :=
hs.linear_preimage (h.mk' f) hf hfinj

section linear_ordered_cancel_add_comm_monoid
variables [topological_space β] [linear_ordered_cancel_add_comm_monoid β] [order_topology β]
  [module 𝕜 β] [ordered_smul 𝕜 β]

lemma strict_convex_Iic (r : β) : strict_convex 𝕜 (Iic r) :=
begin
  rintro x (hx : x ≤ r) y (hy : y ≤ r) hxy a b ha hb hab,
  refine (subset_interior_iff_subset_of_open is_open_Iio).2 Iio_subset_Iic_self _,
  rw ←convex.combo_self hab r,
  obtain rfl | hx := hx.eq_or_lt,
  { exact add_lt_add_left (smul_lt_smul_of_pos (hy.lt_of_ne hxy.symm) hb) _ },
  obtain rfl | hy := hy.eq_or_lt,
  { exact add_lt_add_right (smul_lt_smul_of_pos hx ha) _ },
  { exact add_lt_add (smul_lt_smul_of_pos hx ha) (smul_lt_smul_of_pos hy hb) }
end

lemma strict_convex_Ici (r : β) : strict_convex 𝕜 (Ici r) := @strict_convex_Iic 𝕜 βᵒᵈ _ _ _ _ _ _ r

lemma strict_convex_Icc (r s : β) : strict_convex 𝕜 (Icc r s) :=
(strict_convex_Ici r).inter $ strict_convex_Iic s

lemma strict_convex_Iio (r : β) : strict_convex 𝕜 (Iio r) :=
(convex_Iio r).strict_convex is_open_Iio

lemma strict_convex_Ioi (r : β) : strict_convex 𝕜 (Ioi r) :=
(convex_Ioi r).strict_convex is_open_Ioi

lemma strict_convex_Ioo (r s : β) : strict_convex 𝕜 (Ioo r s) :=
(strict_convex_Ioi r).inter $ strict_convex_Iio s

lemma strict_convex_Ico (r s : β) : strict_convex 𝕜 (Ico r s) :=
(strict_convex_Ici r).inter $ strict_convex_Iio s

lemma strict_convex_Ioc (r s : β) : strict_convex 𝕜 (Ioc r s) :=
(strict_convex_Ioi r).inter $ strict_convex_Iic s

lemma strict_convex_interval (r s : β) : strict_convex 𝕜 (interval r s) :=
strict_convex_Icc _ _

end linear_ordered_cancel_add_comm_monoid
end module
end add_comm_monoid

section add_cancel_comm_monoid
variables [add_cancel_comm_monoid E] [has_continuous_add E] [module 𝕜 E] {s : set E}

/-- The translation of a strictly convex set is also strictly convex. -/
lemma strict_convex.preimage_add_right (hs : strict_convex 𝕜 s) (z : E) :
  strict_convex 𝕜 ((λ x, z + x) ⁻¹' s) :=
begin
  intros x hx y hy hxy a b ha hb hab,
  refine preimage_interior_subset_interior_preimage (continuous_add_left _) _,
  have h := hs hx hy ((add_right_injective _).ne hxy) ha hb hab,
  rwa [smul_add, smul_add, add_add_add_comm, ←add_smul, hab, one_smul] at h,
end

/-- The translation of a strictly convex set is also strictly convex. -/
lemma strict_convex.preimage_add_left (hs : strict_convex 𝕜 s) (z : E) :
  strict_convex 𝕜 ((λ x, x + z) ⁻¹' s) :=
by simpa only [add_comm] using hs.preimage_add_right z

end add_cancel_comm_monoid

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F]

section continuous_add
variables [has_continuous_add E] {s t : set E}

lemma strict_convex.add (hs : strict_convex 𝕜 s) (ht : strict_convex 𝕜 t) :
  strict_convex 𝕜 (s + t) :=
begin
  rintro _ ⟨v, w, hv, hw, rfl⟩ _ ⟨x, y, hx, hy, rfl⟩ h a b ha hb hab,
  rw [smul_add, smul_add, add_add_add_comm],
  obtain rfl | hvx := eq_or_ne v x,
  { refine interior_mono (add_subset_add (singleton_subset_iff.2 hv) subset.rfl) _,
    rw [convex.combo_self hab, singleton_add],
    exact (is_open_map_add_left _).image_interior_subset _
      (mem_image_of_mem _ $ ht hw hy (ne_of_apply_ne _ h) ha hb hab) },
  exact subset_interior_add_left (add_mem_add (hs hv hx hvx ha hb hab) $
    ht.convex hw hy ha.le hb.le hab)
end

lemma strict_convex.add_left (hs : strict_convex 𝕜 s) (z : E) :
  strict_convex 𝕜 ((λ x, z + x) '' s) :=
by simpa only [singleton_add] using (strict_convex_singleton z).add hs

lemma strict_convex.add_right (hs : strict_convex 𝕜 s) (z : E) :
  strict_convex 𝕜 ((λ x, x + z) '' s) :=
by simpa only [add_comm] using hs.add_left z

/-- The translation of a strictly convex set is also strictly convex. -/
lemma strict_convex.vadd (hs : strict_convex 𝕜 s) (x : E) : strict_convex 𝕜 (x +ᵥ s) :=
hs.add_left x

end continuous_add

section continuous_smul
variables [linear_ordered_field 𝕝] [module 𝕝 E] [has_continuous_const_smul 𝕝 E]
  [linear_map.compatible_smul E E 𝕜 𝕝] {s : set E} {x : E}

lemma strict_convex.smul (hs : strict_convex 𝕜 s) (c : 𝕝) : strict_convex 𝕜 (c • s) :=
begin
  obtain rfl | hc := eq_or_ne c 0,
  { exact (subsingleton_zero_smul_set _).strict_convex },
  { exact hs.linear_image (linear_map.lsmul _ _ c) (is_open_map_smul₀ hc) }
end

lemma strict_convex.affinity [has_continuous_add E] (hs : strict_convex 𝕜 s) (z : E) (c : 𝕝) :
  strict_convex 𝕜 (z +ᵥ c • s) :=
(hs.smul c).vadd z

end continuous_smul
end add_comm_group
end ordered_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring 𝕜] [topological_space E]

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] [no_zero_smul_divisors 𝕜 E]
  [has_continuous_const_smul 𝕜 E] {s : set E}

lemma strict_convex.preimage_smul (hs : strict_convex 𝕜 s) (c : 𝕜) :
  strict_convex 𝕜 ((λ z, c • z) ⁻¹' s) :=
begin
  classical,
  obtain rfl | hc := eq_or_ne c 0,
  { simp_rw [zero_smul, preimage_const],
    split_ifs,
    { exact strict_convex_univ },
    { exact strict_convex_empty } },
  refine hs.linear_preimage (linear_map.lsmul _ _ c) _ (smul_right_injective E hc),
  unfold linear_map.lsmul linear_map.mk₂ linear_map.mk₂' linear_map.mk₂'ₛₗ,
  exact continuous_const_smul _,
end

end add_comm_group
end ordered_comm_semiring

section ordered_ring
variables [ordered_ring 𝕜] [topological_space E] [topological_space F]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {s t : set E} {x y : E}

lemma strict_convex.eq_of_open_segment_subset_frontier [nontrivial 𝕜] [densely_ordered 𝕜]
  (hs : strict_convex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (h : open_segment 𝕜 x y ⊆ frontier s) :
  x = y :=
begin
  obtain ⟨a, ha₀, ha₁⟩ := densely_ordered.dense (0 : 𝕜) 1 zero_lt_one,
  classical,
  by_contra hxy,
  exact (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel'_right _ _, rfl⟩).2
    (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) $ add_sub_cancel'_right _ _),
end

lemma strict_convex.add_smul_mem (hs : strict_convex 𝕜 s) (hx : x ∈ s) (hxy : x + y ∈ s)
  (hy : y ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) :
  x + t • y ∈ interior s :=
begin
  have h : x + t • y = (1 - t) • x + t • (x + y),
  { rw [smul_add, ←add_assoc, ←add_smul, sub_add_cancel, one_smul] },
  rw h,
  refine hs hx hxy (λ h, hy $ add_left_cancel _) (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel _ _),
  exact x,
  rw [←h, add_zero],
end

lemma strict_convex.smul_mem_of_zero_mem (hs : strict_convex 𝕜 s) (zero_mem : (0 : E) ∈ s)
  (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) :
  t • x ∈ interior s :=
by simpa using hs.add_smul_mem zero_mem (by simpa using hx) hx₀ ht₀ ht₁

lemma strict_convex.add_smul_sub_mem (h : strict_convex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
  {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • (y - x) ∈ interior s :=
begin
  apply h.open_segment_subset hx hy hxy,
  rw open_segment_eq_image',
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩,
end

/-- The preimage of a strictly convex set under an affine map is strictly convex. -/
lemma strict_convex.affine_preimage {s : set F} (hs : strict_convex 𝕜 s) {f : E →ᵃ[𝕜] F}
  (hf : continuous f) (hfinj : injective f) :
  strict_convex 𝕜 (f ⁻¹' s) :=
begin
  intros x hx y hy hxy a b ha hb hab,
  refine preimage_interior_subset_interior_preimage hf _,
  rw [mem_preimage, convex.combo_affine_apply hab],
  exact hs hx hy (hfinj.ne hxy) ha hb hab,
end

/-- The image of a strictly convex set under an affine map is strictly convex. -/
lemma strict_convex.affine_image (hs : strict_convex 𝕜 s) {f : E →ᵃ[𝕜] F} (hf : is_open_map f) :
  strict_convex 𝕜 (f '' s) :=
begin
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab,
  exact hf.image_interior_subset _ ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab,
    convex.combo_affine_apply hab⟩⟩,
end

variables [topological_add_group E]

lemma strict_convex.neg (hs : strict_convex 𝕜 s) : strict_convex 𝕜 (-s) :=
hs.is_linear_preimage is_linear_map.is_linear_map_neg continuous_id.neg neg_injective

lemma strict_convex.sub (hs : strict_convex 𝕜 s) (ht : strict_convex 𝕜 t) :
  strict_convex 𝕜 (s - t) :=
(sub_eq_add_neg s t).symm ▸ hs.add ht.neg

end add_comm_group
end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [topological_space E]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F] {s : set E} {x : E}

/-- Alternative definition of set strict convexity, using division. -/
lemma strict_convex_iff_div :
  strict_convex 𝕜 s ↔ s.pairwise
    (λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → (a / (a + b)) • x + (b / (a + b)) • y ∈ interior s) :=
⟨λ h x hx y hy hxy a b ha hb, begin
  apply h hx hy hxy (div_pos ha $ add_pos ha hb) (div_pos hb $ add_pos ha hb),
  rw ←add_div,
  exact div_self (add_pos ha hb).ne',
end, λ h x hx y hy hxy a b ha hb hab, by convert h hx hy hxy ha hb; rw [hab, div_one] ⟩

lemma strict_convex.mem_smul_of_zero_mem (hs : strict_convex 𝕜 s) (zero_mem : (0 : E) ∈ s)
  (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht : 1 < t) :
  x ∈ t • interior s :=
begin
  rw mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans ht).ne',
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (inv_pos.2 $ zero_lt_one.trans ht)  (inv_lt_one ht),
end

end add_comm_group
end linear_ordered_field

/-!
#### Convex sets in an ordered space

Relates `convex` and `set.ord_connected`.
-/

section
variables [topological_space E]

/-- A set in a linear ordered field is strictly convex if and only if it is convex. -/
@[simp] lemma strict_convex_iff_convex [linear_ordered_field 𝕜] [topological_space 𝕜]
  [order_topology 𝕜] {s : set 𝕜} :
  strict_convex 𝕜 s ↔ convex 𝕜 s :=
begin
  refine ⟨strict_convex.convex, λ hs, strict_convex_iff_open_segment_subset.2 (λ x hx y hy hxy, _)⟩,
  obtain h | h := hxy.lt_or_lt,
  { refine (open_segment_subset_Ioo h).trans _,
    rw ←interior_Icc,
    exact interior_mono (Icc_subset_segment.trans $ hs.segment_subset hx hy) },
  { rw open_segment_symm,
    refine (open_segment_subset_Ioo h).trans _,
    rw ←interior_Icc,
    exact interior_mono (Icc_subset_segment.trans $ hs.segment_subset hy hx) }
end

lemma strict_convex_iff_ord_connected [linear_ordered_field 𝕜] [topological_space 𝕜]
  [order_topology 𝕜] {s : set 𝕜} :
  strict_convex 𝕜 s ↔ s.ord_connected :=
strict_convex_iff_convex.trans convex_iff_ord_connected

alias strict_convex_iff_ord_connected ↔ strict_convex.ord_connected _

end
