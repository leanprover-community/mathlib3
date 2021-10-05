/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Yaël Dillies
-/

import algebra.module.pi
import algebra.module.prod
import algebra.order.field
import algebra.order.pi
import algebra.order.smul

/-!
# Ordered module

In this file we provide lemmas about `ordered_smul` that hold once a module structure is present.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/

variables {k M N : Type*}

section semiring
variables [ordered_semiring k] [ordered_add_comm_group M] [module k M] [ordered_smul k M]
  {a b : M} {c : k}

/- can be generalized from `module k M` to `distrib_mul_action_with_zero k M` once it exists.
where `distrib_mul_action_with_zero k M`is the conjunction of `distrib_mul_action k M` and
`smul_with_zero k M`.-/
lemma smul_neg_iff_of_pos (hc : 0 < c) :
  c • a < 0 ↔ a < 0 :=
begin
  rw [←neg_neg a, smul_neg, neg_neg_iff_pos, neg_neg_iff_pos],
  exact smul_pos_iff_of_pos hc,
end

end semiring

section ring
variables [ordered_ring k] [ordered_add_comm_group M] [module k M] [ordered_smul k M]
  {a b : M} {c : k}

lemma smul_lt_smul_of_neg (h : a < b) (hc : c < 0) :
  c • b < c • a :=
begin
  rw [←neg_neg c, neg_smul, neg_smul (-c), neg_lt_neg_iff],
  exact smul_lt_smul_of_pos h (neg_pos_of_neg hc),
end

lemma smul_le_smul_of_nonpos (h : a ≤ b) (hc : c ≤ 0) :
  c • b ≤ c • a :=
begin
  rw [←neg_neg c, neg_smul, neg_smul (-c), neg_le_neg_iff],
  exact smul_le_smul_of_nonneg h (neg_nonneg_of_nonpos hc),
end

lemma eq_of_smul_eq_smul_of_neg_of_le (hab : c • a = c • b) (hc : c < 0) (h : a ≤ b) :
  a = b :=
begin
  rw [←neg_neg c, neg_smul, neg_smul (-c), neg_inj] at hab,
  exact eq_of_smul_eq_smul_of_pos_of_le hab (neg_pos_of_neg hc) h,
end

lemma lt_of_smul_lt_smul_of_nonpos (h : c • a < c • b) (hc : c ≤ 0) :
  b < a :=
begin
  rw [←neg_neg c, neg_smul, neg_smul (-c), neg_lt_neg_iff] at h,
  exact lt_of_smul_lt_smul_of_nonneg h (neg_nonneg_of_nonpos hc),
end

lemma smul_lt_smul_iff_of_neg (hc : c < 0) :
  c • a < c • b ↔ b < a :=
begin
  rw [←neg_neg c, neg_smul, neg_smul (-c), neg_lt_neg_iff],
  exact smul_lt_smul_iff_of_pos (neg_pos_of_neg hc),
end

lemma smul_neg_iff_of_neg (hc : c < 0) :
  c • a < 0 ↔ 0 < a :=
begin
  rw [←neg_neg c, neg_smul, neg_neg_iff_pos],
  exact smul_pos_iff_of_pos (neg_pos_of_neg hc),
end

lemma smul_pos_iff_of_neg (hc : c < 0) :
  0 < c • a ↔ a < 0 :=
begin
  rw [←neg_neg c, neg_smul, neg_pos],
  exact smul_neg_iff_of_pos (neg_pos_of_neg hc),
end

end ring

section field
variables [linear_ordered_field k] [ordered_add_comm_group M] [module k M] [ordered_smul k M]
  {a b : M} {c : k}

lemma smul_le_smul_iff_of_neg (hc : c < 0) : c • a ≤ c • b ↔ b ≤ a :=
begin
  rw [←neg_neg c, neg_smul, neg_smul (-c), neg_le_neg_iff],
  exact smul_le_smul_iff_of_pos (neg_pos_of_neg hc),
end

lemma smul_lt_iff_of_neg (hc : c < 0) : c • a < b ↔ c⁻¹ • b < a :=
begin
  rw [←neg_neg c, ←neg_neg a, neg_smul_neg, inv_neg, neg_smul _ b, neg_lt_neg_iff],
  exact smul_lt_iff_of_pos (neg_pos_of_neg hc),
end

lemma lt_smul_iff_of_neg (hc : c < 0) : a < c • b ↔ b < c⁻¹ • a :=
begin
  rw [←neg_neg c, ←neg_neg b, neg_smul_neg, inv_neg, neg_smul _ a, neg_lt_neg_iff],
  exact lt_smul_iff_of_pos (neg_pos_of_neg hc),
end

variables [ordered_add_comm_group N] [module k N] [ordered_smul k N]

-- TODO: solve `prod.has_lt` and `prod.has_le` misalignment issue
instance prod.ordered_smul : ordered_smul k (M × N) :=
ordered_smul.mk' $ λ (v u : M × N) (c : k) h hc,
  ⟨smul_le_smul_of_nonneg h.1.1 hc.le, smul_le_smul_of_nonneg h.1.2 hc.le⟩

instance pi.ordered_smul {ι : Type*} {M : ι → Type*} [Π i, ordered_add_comm_group (M i)]
  [Π i, mul_action_with_zero k (M i)] [∀ i, ordered_smul k (M i)] :
  ordered_smul k (Π i : ι, M i) :=
begin
  refine (ordered_smul.mk' $ λ v u c h hc i, _),
  change c • v i ≤ c • u i,
  exact smul_le_smul_of_nonneg (h.le i) hc.le,
end

-- Sometimes Lean fails to apply the dependent version to non-dependent functions,
-- so we define another instance
instance pi.ordered_smul' {ι : Type*} {M : Type*} [ordered_add_comm_group M]
  [mul_action_with_zero k M] [ordered_smul k M] :
  ordered_smul k (ι → M) :=
pi.ordered_smul

end field

namespace order_dual

instance [semiring k] [ordered_add_comm_monoid M] [module k M] : module k (order_dual M) :=
{ add_smul := λ r s x, order_dual.rec (add_smul _ _) x,
  zero_smul := λ m, order_dual.rec (zero_smul _) m }

end

/-! ### Upper/lower bounds -/

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

/-- Left scalar multiplication as an order isomorphism. -/
@[simps] def order_iso.smul_left {c : k} (hc : 0 < c) : M ≃o M :=
{ to_fun := λ b, c • b,
  inv_fun := λ b, c⁻¹ • b,
  left_inv := inv_smul_smul₀ hc.ne',
  right_inv := smul_inv_smul₀ hc.ne',
  map_rel_iff' := λ b₁ b₂, smul_le_smul_iff_of_pos hc }

@[simp] lemma lower_bounds_smul_of_pos (ha : 0 < a) :
  lower_bounds (a • s) = a • lower_bounds s :=
(order_iso.smul_left ha).lower_bounds_image

@[simp] lemma upper_bounds_smul_of_pos (ha : 0 < a) :
  upper_bounds (a • s) = a • upper_bounds s :=
(order_iso.smul_left ha).upper_bounds_image

@[simp] lemma bdd_below_smul_iff_of_pos (ha : 0 < a) :
  bdd_below (a • s) ↔ bdd_below s :=
(order_iso.smul_left ha).bdd_below_image

@[simp] lemma bdd_above_smul_iff_of_pos (ha : 0 < a) :
  bdd_above (a • s) ↔ bdd_above s :=
(order_iso.smul_left ha).bdd_above_image

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
