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
import algebra.pointwise

/-!
# Ordered module

In this file we provide lemmas about `ordered_smul` that hold once a module structure is present.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/

open_locale pointwise

variables {k M N : Type*}

namespace order_dual

instance [semiring k] [ordered_add_comm_monoid M] [module k M] : module k (order_dual M) :=
{ add_smul := λ r s x, order_dual.rec (add_smul _ _) x,
  zero_smul := λ m, order_dual.rec (zero_smul _) m }

end order_dual

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
  ... = 0 : smul_zero' M c

lemma smul_nonneg_of_nonpos_of_nonpos (hc : c ≤ 0) (ha : a ≤ 0) : 0 ≤ c • a :=
@smul_nonpos_of_nonpos_of_nonneg k (order_dual M) _ _ _ _ _ _ hc ha

alias smul_pos_iff_of_neg ↔ _ smul_pos_of_neg_of_neg
alias smul_neg_iff_of_pos ↔ _ smul_neg_of_pos_of_neg
alias smul_neg_iff_of_neg ↔ _ smul_neg_of_neg_of_pos

lemma antitone_smul_left (hc : c ≤ 0) : antitone (has_scalar.smul c : M → M) :=
λ a b h, smul_le_smul_of_nonpos h hc

lemma strict_anti_smul_left (hc : c < 0) : strict_anti (has_scalar.smul c : M → M) :=
λ a b h, smul_lt_smul_of_neg h hc

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

variables (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps] def order_iso.smul_left_dual {c : k} (hc : c < 0) : M ≃o order_dual M :=
{ to_fun := λ b, order_dual.to_dual (c • b),
  inv_fun := λ b, c⁻¹ • (order_dual.of_dual b),
  left_inv := inv_smul_smul₀ hc.ne,
  right_inv := smul_inv_smul₀ hc.ne,
  map_rel_iff' := λ b₁ b₂, smul_le_smul_iff_of_neg hc }

variables {M} [ordered_add_comm_group N] [module k N] [ordered_smul k N]

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

/-! ### Upper/lower bounds -/

section ordered_semiring
variables [ordered_semiring k] [ordered_add_comm_monoid M] [smul_with_zero k M] [ordered_smul k M]
  {s : set M} {c : k}

lemma smul_lower_bounds_subset_lower_bounds_smul (hc : 0 ≤ c) :
  c • lower_bounds s ⊆ lower_bounds (c • s) :=
(monotone_smul_left hc).image_lower_bounds_subset_lower_bounds_image

lemma smul_upper_bounds_subset_upper_bounds_smul (hc : 0 ≤ c) :
  c • upper_bounds s ⊆ upper_bounds (c • s) :=
(monotone_smul_left hc).image_upper_bounds_subset_upper_bounds_image

lemma bdd_below.smul_of_nonneg (hs : bdd_below s) (hc : 0 ≤ c) : bdd_below (c • s) :=
(monotone_smul_left hc).map_bdd_below hs

lemma bdd_above.smul_of_nonneg (hs : bdd_above s) (hc : 0 ≤ c) : bdd_above (c • s) :=
(monotone_smul_left hc).map_bdd_above hs

end ordered_semiring

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
variables [linear_ordered_field k] [ordered_add_comm_group M]

section mul_action_with_zero
variables [mul_action_with_zero k M] [ordered_smul k M] {s t : set M} {c : k}

@[simp] lemma lower_bounds_smul_of_pos (hc : 0 < c) : lower_bounds (c • s) = c • lower_bounds s :=
(order_iso.smul_left _ hc).lower_bounds_image

@[simp] lemma upper_bounds_smul_of_pos (hc : 0 < c) : upper_bounds (c • s) = c • upper_bounds s :=
(order_iso.smul_left _ hc).upper_bounds_image

@[simp] lemma bdd_below_smul_iff_of_pos (hc : 0 < c) : bdd_below (c • s) ↔ bdd_below s :=
(order_iso.smul_left _ hc).bdd_below_image

@[simp] lemma bdd_above_smul_iff_of_pos (hc : 0 < c) : bdd_above (c • s) ↔ bdd_above s :=
(order_iso.smul_left _ hc).bdd_above_image

end mul_action_with_zero

section module
variables [module k M] [ordered_smul k M] {s t : set M} {c : k}

@[simp] lemma lower_bounds_smul_of_neg (hc : c < 0) : lower_bounds (c • s) = c • upper_bounds s :=
(order_iso.smul_left_dual M hc).upper_bounds_image

@[simp] lemma upper_bounds_smul_of_neg (hc : c < 0) : upper_bounds (c • s) = c • lower_bounds s :=
(order_iso.smul_left_dual M hc).lower_bounds_image

@[simp] lemma bdd_below_smul_iff_of_neg (hc : c < 0) : bdd_below (c • s) ↔ bdd_above s :=
(order_iso.smul_left_dual M hc).bdd_above_image

@[simp] lemma bdd_above_smul_iff_of_neg (hc : c < 0) : bdd_above (c • s) ↔ bdd_below s :=
(order_iso.smul_left_dual M hc).bdd_below_image

end module
end linear_ordered_field
