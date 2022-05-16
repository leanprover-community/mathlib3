/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.set.pointwise

/-!
# Sets as a semiring under union

This file defines `set_semiring α`, an alias of `set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `set_semiring α` is a
(commutative) semiring.
-/

open function set
open_locale pointwise

variables {α β : Type*}

/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
@[derive [inhabited, partial_order, order_bot]] def set_semiring (α : Type*) : Type* := set α

/-- The identity function `set α → set_semiring α`. -/
protected def set.up : set α ≃ set_semiring α := equiv.refl _

namespace set_semiring

/-- The identity function `set_semiring α → set α`. -/
protected def down : set_semiring α ≃ set α := equiv.refl _

@[simp] protected lemma down_up (s : set α) : s.up.down = s := rfl
@[simp] protected lemma up_down (s : set_semiring α) : s.down.up = s := rfl

-- TODO: These lemmas are not tagged `simp` because `set.le_eq_subset` simplifies the LHS
lemma up_le_up {s t : set α} : s.up ≤ t.up ↔ s ⊆ t := iff.rfl
lemma up_lt_up {s t : set α} : s.up < t.up ↔ s ⊂ t := iff.rfl

@[simp] lemma down_subset_down {s t : set_semiring α} : s.down ⊆ t.down ↔ s ≤ t := iff.rfl
@[simp] lemma down_ssubset_down {s t : set_semiring α} : s.down ⊂ t.down ↔ s < t := iff.rfl

instance : add_comm_monoid (set_semiring α) :=
{ add := λ s t, (s.down ∪ t.down).up,
  zero := (∅ : set α).up,
  add_assoc := union_assoc,
  zero_add := empty_union,
  add_zero := union_empty,
  add_comm := union_comm }

/- Since addition on `set_semiring` is commutative (it is set union), there is no need
to also have the instance `covariant_class (set_semiring α) (set_semiring α) (swap (+)) (≤)`. -/
instance covariant_class_add : covariant_class (set_semiring α) (set_semiring α) (+) (≤) :=
⟨λ a b c, union_subset_union_right _⟩

section has_mul
variables [has_mul α]

instance : non_unital_non_assoc_semiring (set_semiring α) :=
{ mul := λ s t, (image2 (*) s.down t.down).up,
  zero_mul := λ s, empty_mul,
  mul_zero := λ s, mul_empty,
  left_distrib := λ _ _ _, mul_union,
  right_distrib := λ _ _ _, union_mul,
  ..set_semiring.add_comm_monoid }

instance : no_zero_divisors (set_semiring α) :=
⟨λ a b ab, a.eq_empty_or_nonempty.imp_right $ λ ha, b.eq_empty_or_nonempty.resolve_right $
  λ hb, nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

instance covariant_class_mul_left : covariant_class (set_semiring α) (set_semiring α) (*) (≤) :=
⟨λ a b c, mul_subset_mul_left⟩

instance covariant_class_mul_right :
  covariant_class (set_semiring α) (set_semiring α) (swap (*)) (≤) :=
⟨λ a b c, mul_subset_mul_right⟩

end has_mul

instance [mul_one_class α] : non_assoc_semiring (set_semiring α) :=
{ one := 1,
  mul := (*),
  ..set_semiring.non_unital_non_assoc_semiring, ..set.mul_one_class }

instance [semigroup α] : non_unital_semiring (set_semiring α) :=
{ ..set_semiring.non_unital_non_assoc_semiring, ..set.semigroup }

instance [monoid α] : semiring (set_semiring α) :=
{ ..set_semiring.non_assoc_semiring, ..set_semiring.non_unital_semiring }

instance [comm_semigroup α] : non_unital_comm_semiring (set_semiring α) :=
{ ..set_semiring.non_unital_semiring, ..set.comm_semigroup }

instance [comm_monoid α] : canonically_ordered_comm_semiring (set_semiring α) :=
{ add_le_add_left := λ a b, add_le_add_left,
  le_iff_exists_add := λ a b, ⟨λ ab, ⟨b, (union_eq_right_iff_subset.2 ab).symm⟩,
    by { rintro ⟨c, rfl⟩, exact subset_union_left _ _ }⟩,
  ..set_semiring.semiring, ..set.comm_monoid, ..set_semiring.partial_order _,
  ..set_semiring.order_bot _, ..set_semiring.no_zero_divisors }

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def image_hom [mul_one_class α] [mul_one_class β] (f : α →* β) :
  set_semiring α →+* set_semiring β :=
{ to_fun := image f,
  map_zero' := image_empty _,
  map_one' := by rw [image_one, map_one, singleton_one],
  map_add' := image_union _,
  map_mul' := λ _ _, image_mul f }

end set_semiring
