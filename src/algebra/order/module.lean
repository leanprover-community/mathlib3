/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Yaël Dillies
-/
import algebra.order.smul

/-!
# Ordered module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide lemmas about `ordered_smul` that hold once a module structure is present.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/

open_locale pointwise

variables {k M N : Type*}

instance [semiring k] [ordered_add_comm_monoid M] [module k M] : module k Mᵒᵈ :=
{ add_smul := λ r s x, order_dual.rec (add_smul _ _) x,
  zero_smul := λ m, order_dual.rec (zero_smul _) m }

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

lemma smul_nonpos_of_nonpos_of_nonneg (hc : c ≤ 0) (ha : 0 ≤ a) : c • a ≤ 0 :=
calc
  c • a ≤ c • 0 : smul_le_smul_of_nonpos ha hc
  ... = 0 : smul_zero c

lemma smul_nonneg_of_nonpos_of_nonpos (hc : c ≤ 0) (ha : a ≤ 0) : 0 ≤ c • a :=
@smul_nonpos_of_nonpos_of_nonneg k Mᵒᵈ _ _ _ _ _ _ hc ha

alias smul_pos_iff_of_neg ↔ _ smul_pos_of_neg_of_neg
alias smul_neg_iff_of_pos ↔ _ smul_neg_of_pos_of_neg
alias smul_neg_iff_of_neg ↔ _ smul_neg_of_neg_of_pos

lemma antitone_smul_left (hc : c ≤ 0) : antitone (has_smul.smul c : M → M) :=
λ a b h, smul_le_smul_of_nonpos h hc

lemma strict_anti_smul_left (hc : c < 0) : strict_anti (has_smul.smul c : M → M) :=
λ a b h, smul_lt_smul_of_neg h hc

/-- Binary **rearrangement inequality**. -/
lemma smul_add_smul_le_smul_add_smul [contravariant_class M M (+) (≤)] {a b : k} {c d : M}
  (hab : a ≤ b) (hcd : c ≤ d) :
  a • d + b • c ≤ a • c + b • d :=
begin
  obtain ⟨b, rfl⟩ := exists_add_of_le hab,
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd,
  rw [smul_add, add_right_comm, smul_add, ←add_assoc, add_smul _ _ d],
  rw le_add_iff_nonneg_right at hab hcd,
  exact add_le_add_left (le_add_of_nonneg_right $ smul_nonneg hab hcd) _,
end

/-- Binary **rearrangement inequality**. -/
lemma smul_add_smul_le_smul_add_smul' [contravariant_class M M (+) (≤)] {a b : k} {c d : M}
  (hba : b ≤ a) (hdc : d ≤ c) : a • d + b • c ≤ a • c + b • d :=
by { rw [add_comm (a • d), add_comm (a • c)], exact smul_add_smul_le_smul_add_smul hba hdc }

/-- Binary strict **rearrangement inequality**. -/
lemma smul_add_smul_lt_smul_add_smul [covariant_class M M (+) (<)] [contravariant_class M M (+) (<)]
  {a b : k} {c d : M} (hab : a < b) (hcd : c < d) : a • d + b • c < a • c + b • d :=
begin
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le,
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le,
  rw [smul_add, add_right_comm, smul_add, ←add_assoc, add_smul _ _ d],
  rw lt_add_iff_pos_right at hab hcd,
  exact add_lt_add_left (lt_add_of_pos_right _ $ smul_pos hab hcd) _,
end

/-- Binary strict **rearrangement inequality**. -/
lemma smul_add_smul_lt_smul_add_smul' [covariant_class M M (+) (<)]
  [contravariant_class M M (+) (<)] {a b : k} {c d : M} (hba : b < a) (hdc : d < c) :
  a • d + b • c < a • c + b • d :=
by { rw [add_comm (a • d), add_comm (a • c)], exact smul_add_smul_lt_smul_add_smul hba hdc }

end ring

section field
variables [linear_ordered_field k] [ordered_add_comm_group M] [module k M] [ordered_smul k M]
  {a b : M} {c : k}

lemma smul_le_smul_iff_of_neg (hc : c < 0) : c • a ≤ c • b ↔ b ≤ a :=
begin
  rw [←neg_neg c, neg_smul, neg_smul (-c), neg_le_neg_iff],
  exact smul_le_smul_iff_of_pos (neg_pos_of_neg hc),
end

lemma inv_smul_le_iff_of_neg (h : c < 0) : c⁻¹ • a ≤ b ↔ c • b ≤ a :=
by { rw [←smul_le_smul_iff_of_neg h, smul_inv_smul₀ h.ne], apply_instance }

lemma inv_smul_lt_iff_of_neg (h : c < 0) : c⁻¹ • a < b ↔ c • b < a :=
by { rw [←smul_lt_smul_iff_of_neg h, smul_inv_smul₀ h.ne], apply_instance }

lemma smul_inv_le_iff_of_neg (h : c < 0) : a ≤ c⁻¹ • b ↔ b ≤ c • a :=
by { rw [←smul_le_smul_iff_of_neg h, smul_inv_smul₀ h.ne], apply_instance }

lemma smul_inv_lt_iff_of_neg (h : c < 0) : a < c⁻¹ • b ↔ b < c • a :=
by { rw [←smul_lt_smul_iff_of_neg h, smul_inv_smul₀ h.ne], apply_instance }

variables (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps] def order_iso.smul_left_dual {c : k} (hc : c < 0) : M ≃o Mᵒᵈ :=
{ to_fun := λ b, order_dual.to_dual (c • b),
  inv_fun := λ b, c⁻¹ • (order_dual.of_dual b),
  left_inv := inv_smul_smul₀ hc.ne,
  right_inv := smul_inv_smul₀ hc.ne,
  map_rel_iff' := λ b₁ b₂, smul_le_smul_iff_of_neg hc }

end field

/-! ### Upper/lower bounds -/

section ordered_ring
variables [ordered_ring k] [ordered_add_comm_group M] [module k M] [ordered_smul k M]
  {s : set M} {c : k}

lemma smul_lower_bounds_subset_upper_bounds_smul (hc : c ≤ 0) :
  c • lower_bounds s ⊆ upper_bounds (c • s) :=
(antitone_smul_left hc).image_lower_bounds_subset_upper_bounds_image

lemma smul_upper_bounds_subset_lower_bounds_smul (hc : c ≤ 0) :
  c • upper_bounds s ⊆ lower_bounds (c • s) :=
(antitone_smul_left hc).image_upper_bounds_subset_lower_bounds_image

lemma bdd_below.smul_of_nonpos (hc : c ≤ 0) (hs : bdd_below s) : bdd_above (c • s) :=
(antitone_smul_left hc).map_bdd_below hs

lemma bdd_above.smul_of_nonpos (hc : c ≤ 0) (hs : bdd_above s) : bdd_below (c • s) :=
(antitone_smul_left hc).map_bdd_above hs

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field k] [ordered_add_comm_group M] [module k M] [ordered_smul k M]
  {s : set M} {c : k}

@[simp] lemma lower_bounds_smul_of_neg (hc : c < 0) : lower_bounds (c • s) = c • upper_bounds s :=
(order_iso.smul_left_dual M hc).upper_bounds_image

@[simp] lemma upper_bounds_smul_of_neg (hc : c < 0) : upper_bounds (c • s) = c • lower_bounds s :=
(order_iso.smul_left_dual M hc).lower_bounds_image

@[simp] lemma bdd_below_smul_iff_of_neg (hc : c < 0) : bdd_below (c • s) ↔ bdd_above s :=
(order_iso.smul_left_dual M hc).bdd_above_image

@[simp] lemma bdd_above_smul_iff_of_neg (hc : c < 0) : bdd_above (c • s) ↔ bdd_below s :=
(order_iso.smul_left_dual M hc).bdd_below_image

end linear_ordered_field
