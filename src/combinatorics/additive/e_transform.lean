/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pointwise

/-!
# e-transforms

e-transforms are a family of transformations of pairs of finite sets that aim to reduce the size
of the sumset while keeping some invariant the same. This file defines a few of them, to be used
as internals of other proofs.

## Main declarations

* `finset.mul_dyson_e_transform`: The Dyson e-transform. Replaces `(s, t)` by
  `(s ∪ e • t, t ∩ e⁻¹ • s)`. The additive version preserves `|s ∩ [1, m]| + |t ∩ [1, m - e]|`.
* `finset.mul_e_transform_left`/`finset.mul_e_transform_right`: Replace `(s, t)` by
  `(s ∩ s • e, t ∪ e⁻¹ • t)` and `(s ∪ s • e, t ∩ e⁻¹ • t)`. Preserve (together) the sum of
  the cardinalities (see `finset.mul_e_transform.card`). In particular, one of the two transforms
  increases the sum of the cardinalities and the other one decreases it. See
  `le_or_lt_of_add_le_add` and around.

## TODO

Prove the invariance property of the Dyson e-transform.
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
def mul_dyson_e_transform : finset α × finset α := (x.1 ∪ e • x.2, x.2 ∩ e⁻¹ • x.1)

@[to_additive] lemma mul_dyson_e_transform.subset :
  (mul_dyson_e_transform e x).1 * (mul_dyson_e_transform e x).2 ⊆ x.1 * x.2 :=
begin
  refine union_mul_inter_subset_union.trans (union_subset subset.rfl _),
  rw [mul_smul_comm,  smul_mul_assoc, inv_smul_smul, mul_comm],
  refl,
end

@[to_additive] lemma mul_dyson_e_transform.card :
  (mul_dyson_e_transform e x).1.card + (mul_dyson_e_transform e x).2.card = x.1.card + x.2.card :=
begin
  dsimp,
  rw [←card_smul_finset e (_ ∩ _), smul_finset_inter, smul_inv_smul, inter_comm,
    card_union_add_card_inter, card_smul_finset],
end

@[simp, to_additive] lemma mul_dyson_e_transform_idem :
  mul_dyson_e_transform e (mul_dyson_e_transform e x) = mul_dyson_e_transform e x :=
begin
  ext : 1; dsimp,
  { rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left_iff_subset],
    exact inter_subset_union },
  { rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left_iff_subset],
    exact inter_subset_union }
end

variables {e x}

@[to_additive] lemma mul_dyson_e_transform.smul_finset_snd_subset_fst :
  e • (mul_dyson_e_transform e x).2 ⊆ (mul_dyson_e_transform e x).1 :=
by { dsimp, rw [smul_finset_inter, smul_inv_smul, inter_comm], exact inter_subset_union }

end comm_group

/-!
### Two unnamed e-transforms

The following two transforms both reduce the product/sum of the two sets. Further, one of them must
decrease the sum of the size of the sets (and then the other increases it).

This pair of transforms doesn't seem to be named in the literature. It is used by Sanders in his
bound on Roth numbers, and by DeVos in his proof of Cauchy-Davenport.
-/

section group
variables [group α] (e : α) (x : finset α × finset α)

/-- An **e-transform**. Turns `(s, t)` into `(s ∩ s • e, t ∪ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive "An **e-transform**. Turns `(s, t)` into `(s ∩ s +ᵥ e, t ∪ -e +ᵥ t)`. This
reduces the sum of the two sets.", simps]
def mul_e_transform_left : finset α × finset α := (x.1 ∩ op e • x.1, x.2 ∪ e⁻¹ • x.2)

/-- An **e-transform**. Turns `(s, t)` into `(s ∪ s • e, t ∩ e⁻¹ • t)`. This reduces the product of
the two sets. -/
@[to_additive "An **e-transform**. Turns `(s, t)` into `(s ∪ s +ᵥ e, t ∩ -e +ᵥ t)`. This reduces the
sum of the two sets.", simps]
def mul_e_transform_right : finset α × finset α := (x.1 ∪ op e • x.1, x.2 ∩ e⁻¹ • x.2)

@[simp, to_additive] lemma mul_e_transform_left_one : mul_e_transform_left 1 x = x :=
by simp [mul_e_transform_left]
@[simp, to_additive] lemma mul_e_transform_right_one : mul_e_transform_right 1 x = x :=
by simp [mul_e_transform_right]

@[to_additive] lemma mul_e_transform_left.fst_mul_snd_subset :
  (mul_e_transform_left e x).1 * (mul_e_transform_left e x).2 ⊆ x.1 * x.2 :=
begin
  refine inter_mul_union_subset_union.trans (union_subset subset.rfl _),
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul],
  refl,
end

@[to_additive] lemma mul_e_transform_right.fst_mul_snd_subset :
  (mul_e_transform_right e x).1 * (mul_e_transform_right e x).2 ⊆ x.1 * x.2 :=
begin
  refine union_mul_inter_subset_union.trans (union_subset subset.rfl _),
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul],
  refl,
end

@[to_additive] lemma mul_e_transform_left.card :
  (mul_e_transform_left e x).1.card + (mul_e_transform_right e x).1.card = 2 * x.1.card :=
(card_inter_add_card_union _ _).trans $ by rw [card_smul_finset, two_mul]

@[to_additive] lemma mul_e_transform_right.card :
  (mul_e_transform_left e x).2.card + (mul_e_transform_right e x).2.card = 2 * x.2.card :=
(card_union_add_card_inter _ _).trans $ by rw [card_smul_finset, two_mul]

/-- This statement is meant to be combined with `le_or_lt_of_add_le_add` and similar lemmas. -/
@[to_additive add_e_transform.card "This statement is meant to be combined with
`le_or_lt_of_add_le_add` and similar lemmas."]
protected lemma mul_e_transform.card :
  (mul_e_transform_left e x).1.card + (mul_e_transform_left e x).2.card
    + ((mul_e_transform_right e x).1.card + (mul_e_transform_right e x).2.card)
    = x.1.card + x.2.card + (x.1.card + x.2.card) :=
by rw [add_add_add_comm, mul_e_transform_left.card, mul_e_transform_right.card, ←mul_add, two_mul]

end group

section comm_group
variables [comm_group α] (e : α) (x : finset α × finset α)

@[simp, to_additive] lemma mul_e_transform_left_inv :
  mul_e_transform_left e⁻¹ x = (mul_e_transform_right e x.swap).swap :=
by simp [-op_inv, op_smul_eq_smul, mul_e_transform_left, mul_e_transform_right]

@[simp, to_additive] lemma mul_e_transform_right_inv :
  mul_e_transform_right e⁻¹ x = (mul_e_transform_left e x.swap).swap :=
by simp [-op_inv, op_smul_eq_smul, mul_e_transform_left, mul_e_transform_right]

end comm_group
end finset
