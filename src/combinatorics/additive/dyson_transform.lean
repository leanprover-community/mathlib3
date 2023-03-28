/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pointwise

/-!
# Dyson transforms

Dyson transforms are a family of transformations of pairs of finite sets that aim to reduce the size
of the sumset while keeping some invariant the same. This file defines a few of them.

## Main declarations

* `finset.mul_e_transform`: The Dyson e-transform. Replaces `(s, t)` by `(s ∪ e • t, t ∩ e⁻¹ • s)`.
  The additive version preserves `(s ∩ Icc 1 m).card + (t ∩ finset.range Icc 1 (m - e)).card`.
* `finset.mul_transform₁`/`finset.mul_transform₂`: Replaces `(s, t)` by
  `(s ∩ op e • s, t ∪ e⁻¹ • t)` and `(s ∪ op e • s, t ∩ e⁻¹ • t)`. Preserve (together) the sum of
  the cardinalities (see `finset.mul_transform.card`). In particular, one of the two transforms does
  not increase the sum of the cardinalities.

## TODO

Prove the invariance property of the e-transform.
-/

open mul_opposite
open_locale pointwise

variables {α  : Type*} [decidable_eq α]

namespace finset

/-! ### Dyson e-transform -/

section comm_group
variables [comm_group α] (e : α) (x : finset α × finset α)

/-- The **Dyson e-transform**. Turns `(s, t)` into `(s ∪ e • t, t ∩ e⁻¹ • s)`. This reduces the
product of the two sets. -/
@[to_additive "The **Dyson e-transform**. Turns `(s, t)` into `(s ∪ e +ᵥ t, t ∩ -e +ᵥ s)`. This
reduces the sum of the two sets.", simps]
def mul_e_transform : finset α × finset α := (x.1 ∪ e • x.2, x.2 ∩ e⁻¹ • x.1)

@[simp, to_additive] lemma mul_e_transform.fst_mul_snd_subset :
  (mul_e_transform e x).1 * (mul_e_transform e x).2 ⊆ x.1 * x.2 :=
begin
  refine union_mul_inter_subset_union.trans (union_subset subset.rfl _),
  rw [mul_smul_comm,  smul_mul_assoc, inv_smul_smul, mul_comm],
  refl,
end

variables {e x}

@[to_additive] lemma mul_e_transform.smul_finset_snd_subset_fst :
  e • (mul_e_transform e x).2 ⊆ (mul_e_transform e x).1 :=
by { dsimp, rw [smul_finset_inter, smul_inv_smul, inter_comm], exact inter_subset_union }

end comm_group

/-!
### Some unnamed transform

The following two transforms both reduce the product/sum of the two sets. Further, one of them must
decrease the sum of the size of the sets (and then the other increases it).
-/

section group
variables [group α] (e : α) (x : finset α × finset α)

/-- A **Dyson transform**. Turns `(s, t)` into `(s ∩ op e • s, t ∪ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive "A **Dyson transform**. Turns `(s, t)` into `(s ∩ op e +ᵥ s, t ⊆ -e +ᵥ t)`. This
reduces the sum of the two sets.", simps]
def mul_transform₁ : finset α × finset α := (x.1 ∩ op e • x.1, x.2 ∪ e⁻¹ • x.2)

/-- A **Dyson transform**. Turns `(s, t)` into `(s ∪ op e • s, t ∩ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive "A **Dyson transform**. Turns `(s, t)` into `(s ∪ op e +ᵥ s, t ∩ -e +ᵥ t)`. This
reduces the sum of the two sets.", simps]
@[to_additive, simps] def mul_transform₂ : finset α × finset α :=
(x.1 ∪ op e • x.1, x.2 ∩ e⁻¹ • x.2)

@[simp, to_additive] lemma mul_transform₁_one : mul_transform₁ 1 x = x := by simp [mul_transform₁]
@[simp, to_additive] lemma mul_transform₂_one : mul_transform₂ 1 x = x := by simp [mul_transform₂]

@[simp, to_additive] lemma mul_transform₁.fst_mul_snd_subset :
  (mul_transform₁ e x).1 * (mul_transform₁ e x).2 ⊆ x.1 * x.2 :=
begin
  refine inter_mul_union_subset_union.trans (union_subset subset.rfl _),
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul],
  refl,
end

@[simp, to_additive] lemma mul_transform₂.fst_mul_snd_subset :
  (mul_transform₂ e x).1 * (mul_transform₂ e x).2 ⊆ x.1 * x.2 :=
begin
  refine union_mul_inter_subset_union.trans (union_subset subset.rfl _),
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul],
  refl,
end

@[simp, to_additive add_transform.card_fst] lemma mul_transform.card_fst :
  (mul_transform₁ e x).1.card + (mul_transform₂ e x).1.card = 2 * x.1.card :=
(card_inter_add_card_union _ _).trans $ by rw [card_smul_finset, two_mul]

@[simp, to_additive add_transform.card_snd] lemma mul_transform.card_snd :
  (mul_transform₁ e x).2.card + (mul_transform₂ e x).2.card = 2 * x.2.card :=
(card_union_add_card_inter _ _).trans $ by rw [card_smul_finset, two_mul]

@[simp, to_additive add_transform.card] protected lemma mul_transform.card :
  (mul_transform₁ e x).1.card + (mul_transform₁ e x).2.card
    + ((mul_transform₂ e x).1.card + (mul_transform₂ e x).2.card)
    = x.1.card + x.2.card + (x.1.card + x.2.card) :=
by rw [add_add_add_comm, mul_transform.card_fst, mul_transform.card_snd, ←mul_add, two_mul]

@[simp, to_additive add_transform.card_le] protected lemma mul_transform.card_le :
  (mul_transform₁ e x).1.card + (mul_transform₁ e x).2.card ≤ x.1.card + x.2.card
    ∨ ((mul_transform₂ e x).1.card + (mul_transform₂ e x).2.card) ≤ x.1.card + x.2.card :=
le_or_le_of_add_le_add (mul_transform.card _ _).le

@[simp, to_additive add_transform.card_ge] protected lemma mul_transform.card_ge :
  x.1.card + x.2.card ≤ (mul_transform₁ e x).1.card + (mul_transform₁ e x).2.card
    ∨ x.1.card + x.2.card ≤ ((mul_transform₂ e x).1.card + (mul_transform₂ e x).2.card) :=
le_or_le_of_add_le_add (mul_transform.card _ _).ge

end group

section comm_group
variables [comm_group α] (e : α) (x : finset α × finset α)

@[simp, to_additive]
lemma mul_transform₁_inv : mul_transform₁ e⁻¹ x = (mul_transform₂ e x.swap).swap :=
by simp [-op_inv, op_smul_eq_smul, mul_transform₁, mul_transform₂]

@[simp, to_additive]
lemma mul_transform₂_inv : mul_transform₂ e⁻¹ x = (mul_transform₁ e x.swap).swap :=
by simp [-op_inv, op_smul_eq_smul, mul_transform₁, mul_transform₂]

end comm_group
end finset
