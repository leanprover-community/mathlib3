/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Yaël Dillies
-/
import algebra.module.ordered
import algebra.pointwise
import order.conditionally_complete_lattice

/-!
# Upper/lower bounds in ordered monoids and groups

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bdd_above_neg`).
-/

open function set
open_locale pointwise

section inv_neg

variables {G : Type*} [group G] [preorder G] [covariant_class G G (*) (≤)]
  [covariant_class G G (swap (*)) (≤)] {s : set G} {a : G}

@[simp, to_additive]
lemma bdd_above_inv : bdd_above s⁻¹ ↔ bdd_below s := (order_iso.inv G).bdd_above_preimage

@[simp, to_additive]
lemma bdd_below_inv : bdd_below s⁻¹ ↔ bdd_above s := (order_iso.inv G).bdd_below_preimage

@[to_additive]
lemma bdd_above.inv (h : bdd_above s) : bdd_below s⁻¹ := bdd_below_inv.2 h

@[to_additive]
lemma bdd_below.inv (h : bdd_below s) : bdd_above s⁻¹ := bdd_above_inv.2 h

@[simp, to_additive]
lemma is_lub_inv : is_lub s⁻¹ a ↔ is_glb s a⁻¹ := (order_iso.inv G).is_lub_preimage

@[to_additive]
lemma is_lub_inv' : is_lub s⁻¹ a⁻¹ ↔ is_glb s a := (order_iso.inv G).is_lub_preimage'

@[to_additive]
lemma is_glb.inv (h : is_glb s a) : is_lub s⁻¹ a⁻¹ := is_lub_inv'.2 h

@[simp, to_additive]
lemma is_glb_inv : is_glb s⁻¹ a ↔ is_lub s a⁻¹ := (order_iso.inv G).is_glb_preimage

@[to_additive]
lemma is_glb_inv' : is_glb s⁻¹ a⁻¹ ↔ is_lub s a := (order_iso.inv G).is_glb_preimage'

@[to_additive]
lemma is_lub.inv (h : is_lub s a) : is_glb s⁻¹ a⁻¹ := is_glb_inv'.2 h

end inv_neg

section mul_add

variables {M : Type*} [has_mul M] [preorder M] [covariant_class M M (*) (≤)]
  [covariant_class M M (swap (*)) (≤)]

@[to_additive] lemma mul_mem_upper_bounds_mul {s t : set M} {a b : M} (ha : a ∈ upper_bounds s)
  (hb : b ∈ upper_bounds t) :
  a * b ∈ upper_bounds (s * t) :=
forall_image2_iff.2 $ λ x hx y hy, mul_le_mul' (ha hx) (hb hy)

@[to_additive] lemma subset_upper_bounds_mul (s t : set M) :
  upper_bounds s * upper_bounds t ⊆ upper_bounds (s * t) :=
image2_subset_iff.2 $ λ x hx y hy, mul_mem_upper_bounds_mul hx hy

@[to_additive] lemma mul_mem_lower_bounds_mul {s t : set M} {a b : M} (ha : a ∈ lower_bounds s)
  (hb : b ∈ lower_bounds t) : a * b ∈ lower_bounds (s * t) :=
@mul_mem_upper_bounds_mul (order_dual M) _ _ _ _ _ _ _ _ ha hb

@[to_additive] lemma subset_lower_bounds_mul (s t : set M) :
  lower_bounds s * lower_bounds t ⊆ lower_bounds (s * t) :=
@subset_upper_bounds_mul (order_dual M) _ _ _ _ _ _

@[to_additive] lemma bdd_above.mul {s t : set M} (hs : bdd_above s) (ht : bdd_above t) :
  bdd_above (s * t) :=
(hs.mul ht).mono (subset_upper_bounds_mul s t)

@[to_additive] lemma bdd_below.mul {s t : set M} (hs : bdd_below s) (ht : bdd_below t) :
  bdd_below (s * t) :=
(hs.mul ht).mono (subset_lower_bounds_mul s t)

end mul_add

section conditionally_complete_lattice

section right

variables {ι G : Type*} [group G] [conditionally_complete_lattice G]
  [covariant_class G G (function.swap (*)) (≤)] [nonempty ι] {f : ι → G}

@[to_additive] lemma csupr_mul (hf : bdd_above (set.range f)) (a : G) :
  (⨆ i, f i) * a = ⨆ i, f i * a :=
(order_iso.mul_right a).map_csupr hf

@[to_additive] lemma csupr_div (hf : bdd_above (set.range f)) (a : G) :
  (⨆ i, f i) / a = ⨆ i, f i / a :=
by simp only [div_eq_mul_inv, csupr_mul hf]

end right

section left

variables {ι G : Type*} [group G] [conditionally_complete_lattice G]
  [covariant_class G G (*) (≤)] [nonempty ι] {f : ι → G}

@[to_additive] lemma mul_csupr (hf : bdd_above (set.range f)) (a : G) :
  a * (⨆ i, f i) = ⨆ i, a * f i :=
(order_iso.mul_left a).map_csupr hf

end left

end conditionally_complete_lattice

/-! ### Scalar multiplication -/

section ordered_semiring
variables {α β : Type*} [ordered_semiring α] [ordered_add_comm_monoid β] [smul_with_zero α β]
  [ordered_smul α β] {s : set β} {a : α}

lemma smul_lower_bounds_subset_lower_bounds_smul (ha : 0 ≤ a) :
  a • lower_bounds s ⊆ lower_bounds (a • s) :=
begin
  rintro _ ⟨b, hb, rfl⟩ _ ⟨x, hx, rfl⟩,
  exact smul_le_smul_of_nonneg (hb hx) ha,
end

lemma smul_upper_bounds_subset_upper_bounds_smul (ha : 0 ≤ a) :
  a • upper_bounds s ⊆ upper_bounds (a • s) :=
begin
  rintro _ ⟨b, hb, rfl⟩ _ ⟨x, hx, rfl⟩,
  exact smul_le_smul_of_nonneg (hb hx) ha,
end

lemma bdd_below.smul_of_nonneg (ha : 0 ≤ a) (hs : bdd_below s) :
  bdd_below (a • s) :=
begin
  obtain ⟨b, hb⟩ := hs,
  exact ⟨a • b, smul_lower_bounds_subset_lower_bounds_smul ha (smul_mem_smul_set hb)⟩,
end

lemma bdd_above.smul_of_nonneg (ha : 0 ≤ a) (hs : bdd_above s) :
  bdd_above (a • s) :=
begin
  obtain ⟨b, hb⟩ := hs,
  exact ⟨a • b, smul_upper_bounds_subset_upper_bounds_smul ha (smul_mem_smul_set hb)⟩,
end

end ordered_semiring

section ordered_ring
variables {α β : Type*} [ordered_ring α] [ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {s : set β} {a : α}

lemma smul_lower_bounds_subset_upper_bounds_smul (ha : a ≤ 0) :
  a • lower_bounds s ⊆ upper_bounds (a • s) :=
begin
  rintro _ ⟨b, hb, rfl⟩ _ ⟨x, hx, rfl⟩,
  exact smul_le_smul_of_nonpos (hb hx) ha,
end

lemma smul_upper_bounds_subset_lower_bounds_smul (ha : a ≤ 0) :
  a • upper_bounds s ⊆ lower_bounds (a • s) :=
begin
  rintro _ ⟨b, hb, rfl⟩ _ ⟨x, hx, rfl⟩,
  exact smul_le_smul_of_nonpos (hb hx) ha,
end

lemma bdd_below.smul_of_nonpos (ha : a ≤ 0) (hs : bdd_below s) :
  bdd_above (a • s) :=
begin
  obtain ⟨b, hb⟩ := hs,
  exact ⟨a • b, smul_lower_bounds_subset_upper_bounds_smul ha (smul_mem_smul_set hb)⟩,
end

lemma bdd_above.smul_of_nonpos (ha : a ≤ 0) (hs : bdd_above s) :
  bdd_below (a • s) :=
begin
  obtain ⟨b, hb⟩ := hs,
  exact ⟨a • b, smul_upper_bounds_subset_lower_bounds_smul ha (smul_mem_smul_set hb)⟩,
end

end ordered_ring

section linear_ordered_field
variables {α β : Type*} [linear_ordered_field α] [ordered_add_comm_group β]

section mul_action_with_zero
variables [mul_action_with_zero α β] [ordered_smul α β] {s t : set β} {a : α}

@[simp] lemma lower_bounds_smul_of_pos (ha : 0 < a) :
  lower_bounds (a • s) = a • lower_bounds s :=
begin
  refine subset.antisymm _ (smul_lower_bounds_subset_lower_bounds_smul ha.le),
  have h : a⁻¹ • lower_bounds (a • s) ⊆ lower_bounds (a⁻¹ • a • s) :=
    smul_lower_bounds_subset_lower_bounds_smul (inv_nonneg.2 ha.le),
  rwa [←subset_smul_iff' ha.ne', inv_smul_smul' ha.ne'] at h,
end

@[simp] lemma upper_bounds_smul_of_pos (ha : 0 < a) :
  upper_bounds (a • s) = a • upper_bounds s :=
begin
  refine subset.antisymm _ (smul_upper_bounds_subset_upper_bounds_smul ha.le),
  have h : a⁻¹ • upper_bounds (a • s) ⊆ upper_bounds (a⁻¹ • a • s) :=
    smul_upper_bounds_subset_upper_bounds_smul (inv_nonneg.2 ha.le),
  rwa [←subset_smul_iff' ha.ne', inv_smul_smul' ha.ne'] at h,
end

@[simp] lemma bdd_below_smul_iff_of_pos (ha : 0 < a) :
  bdd_below (a • s) ↔ bdd_below s :=
begin
  refine ⟨λ h, _, bdd_below.smul_of_nonneg ha.le⟩,
  rw ←inv_smul_smul' ha.ne' s,
  exact h.smul_of_nonneg (inv_nonneg.2 ha.le),
end

@[simp] lemma bdd_above_smul_iff_of_pos (ha : 0 < a) :
  bdd_above (a • s) ↔ bdd_above s :=
begin
  refine ⟨λ h, _, bdd_above.smul_of_nonneg ha.le⟩,
  rw ←inv_smul_smul' ha.ne' s,
  exact h.smul_of_nonneg (inv_nonneg.2 ha.le),
end

end mul_action_with_zero

section module
variables [module α β] [ordered_smul α β] {s t : set β} {a : α}

@[simp] lemma lower_bounds_smul_of_neg (ha : a < 0) :
  lower_bounds (a • s) = a • upper_bounds s :=
begin
  refine subset.antisymm _ (smul_upper_bounds_subset_lower_bounds_smul ha.le),
  have h : a⁻¹ • lower_bounds (a • s) ⊆ upper_bounds (a⁻¹ • a • s) :=
    smul_lower_bounds_subset_upper_bounds_smul (inv_nonpos.2 ha.le),
  rwa [←subset_smul_iff' ha.ne, inv_smul_smul' ha.ne] at h,
end

@[simp] lemma upper_bounds_smul_of_neg (ha : a < 0) :
  upper_bounds (a • s) = a • lower_bounds s :=
begin
  refine subset.antisymm _ (smul_lower_bounds_subset_upper_bounds_smul ha.le),
  have h : a⁻¹ • upper_bounds (a • s) ⊆ lower_bounds (a⁻¹ • a • s) :=
    smul_upper_bounds_subset_lower_bounds_smul (inv_nonpos.2 ha.le),
  rwa [←subset_smul_iff' ha.ne, inv_smul_smul' ha.ne] at h,
end

@[simp] lemma bdd_below_smul_iff_of_neg (ha : a < 0) :
  bdd_below (a • s) ↔ bdd_above s :=
begin
  refine ⟨λ h, _, bdd_above.smul_of_nonpos ha.le⟩,
  rw ←inv_smul_smul' ha.ne s,
  exact h.smul_of_nonpos (inv_nonpos.2 ha.le),
end

@[simp] lemma bdd_above_smul_iff_of_neg (ha : a < 0) :
  bdd_above (a • s) ↔ bdd_below s :=
begin
  refine ⟨λ h, _, bdd_below.smul_of_nonpos ha.le⟩,
  rw ←inv_smul_smul' ha.ne s,
  exact h.smul_of_nonpos (inv_nonpos.2 ha.le),
end

end module
end linear_ordered_field
