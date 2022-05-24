/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import group_theory.submonoid.pointwise

/-!

# Submonoid of inverses

Given a submonoid `N` of a monoid `M`, we define the submonoid `N.left_inv` as the submonoid of
left inverses of `N`. When `M` is commutative, we may define `from_comm_left_inv : N.left_inv →* N`
since the inverses are unique. When `N ≤ is_unit.submonoid M`, this is precisely
the pointwise inverse of `N`, and we may define `left_inv_equiv : S.left_inv ≃* S`.

For the pointwise inverse of submonoids of groups, please refer to
`group_theory.submonoid.pointwise`.

## TODO

Define the submonoid of right inverses and two-sided inverses.
See the comments of #10679 for a possible implementation.

-/
variables {M : Type*}

namespace submonoid

@[to_additive]
noncomputable instance [monoid M] : group (is_unit.submonoid M) :=
{ inv := λ x, ⟨_, (x.prop.unit⁻¹).is_unit⟩,
  mul_left_inv := λ x, subtype.eq x.prop.unit.inv_val,
 ..(show monoid (is_unit.submonoid M), by apply_instance) }

@[to_additive]
noncomputable instance [comm_monoid M] : comm_group (is_unit.submonoid M) :=
{ mul_comm := λ a b, mul_comm a b,
 ..(show group (is_unit.submonoid M), by apply_instance) }

@[to_additive] lemma is_unit.submonoid.coe_inv [monoid M] (x : is_unit.submonoid M) :
  ↑(x⁻¹) = (↑x.prop.unit⁻¹ : M) := rfl

section monoid

variables [monoid M] (S : submonoid M)

/-- `S.left_inv` is the submonoid containing all the left inverses of `S`. -/
@[to_additive "`S.left_neg` is the additive submonoid containing all the left additive inverses
of `S`."]
def left_inv : submonoid M :=
{ carrier := { x : M | ∃ y : S, x * y = 1 },
  one_mem' := ⟨1, mul_one 1⟩,
  mul_mem' := λ a b ⟨a', ha⟩ ⟨b', hb⟩,
    ⟨b' * a', by rw [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩ }

@[to_additive]
lemma left_inv_left_inv_le : S.left_inv.left_inv ≤ S :=
begin
  rintros x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩,
  convert z.prop,
  rw [← mul_one x, ← h₁, ← mul_assoc, h₂, one_mul],
end

@[to_additive]
lemma unit_mem_left_inv (x : Mˣ) (hx : (x : M) ∈ S) : ((x⁻¹ : _) : M) ∈ S.left_inv :=
⟨⟨x, hx⟩, x.inv_val⟩

@[to_additive]
lemma left_inv_left_inv_eq (hS : S ≤ is_unit.submonoid M) : S.left_inv.left_inv = S :=
begin
  refine le_antisymm S.left_inv_left_inv_le _,
  intros x hx,
  have : x = ((hS hx).unit⁻¹⁻¹ : Mˣ) := by { rw [inv_inv (hS hx).unit], refl },
  rw this,
  exact S.left_inv.unit_mem_left_inv _ (S.unit_mem_left_inv _ hx)
end

/-- The function from `S.left_inv` to `S` sending an element to its right inverse in `S`.
This is a `monoid_hom` when `M` is commutative. -/
@[to_additive "The function from `S.left_add` to `S` sending an element to its right additive
inverse in `S`. This is an `add_monoid_hom` when `M` is commutative."]
noncomputable
def from_left_inv : S.left_inv → S := λ x, x.prop.some

@[simp, to_additive]
lemma mul_from_left_inv (x : S.left_inv) : (x : M) * S.from_left_inv x = 1 :=
x.prop.some_spec

@[simp, to_additive] lemma from_left_inv_one : S.from_left_inv 1 = 1 :=
(one_mul _).symm.trans (subtype.eq $ S.mul_from_left_inv 1)

end monoid

section comm_monoid

variables [comm_monoid M] (S : submonoid M)

@[simp, to_additive]
lemma from_left_inv_mul (x : S.left_inv) : (S.from_left_inv x : M) * x = 1 :=
by rw [mul_comm, mul_from_left_inv]

@[to_additive]
lemma left_inv_le_is_unit : S.left_inv ≤ is_unit.submonoid M :=
λ x ⟨y, hx⟩, ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩

@[to_additive]
lemma from_left_inv_eq_iff (a : S.left_inv) (b : M) :
  (S.from_left_inv a : M) = b ↔ (a : M) * b = 1 :=
by rw [← is_unit.mul_right_inj (left_inv_le_is_unit _ a.prop), S.mul_from_left_inv, eq_comm]

/-- The `monoid_hom` from `S.left_inv` to `S` sending an element to its right inverse in `S`. -/
@[to_additive "The `add_monoid_hom` from `S.left_neg` to `S` sending an element to its
right additive inverse in `S`.", simps]
noncomputable
def from_comm_left_inv : S.left_inv →* S :=
{ to_fun := S.from_left_inv,
  map_one' := S.from_left_inv_one,
  map_mul' := λ x y, subtype.ext $
    by rw [from_left_inv_eq_iff, mul_comm x, submonoid.coe_mul, submonoid.coe_mul, mul_assoc,
      ← mul_assoc (x : M), mul_from_left_inv, one_mul, mul_from_left_inv] }

variable (hS : S ≤ is_unit.submonoid M)

include hS

/-- The submonoid of pointwise inverse of `S` is `mul_equiv` to `S`. -/
@[to_additive "The additive submonoid of pointwise additive inverse of `S` is
`add_equiv` to `S`.", simps apply]
noncomputable
def left_inv_equiv : S.left_inv ≃* S :=
{ inv_fun := λ x, by { choose x' hx using (hS x.prop), exact ⟨x'.inv, x, hx ▸ x'.inv_val⟩ },
  left_inv := λ x, subtype.eq $ begin
      dsimp, generalize_proofs h, rw ← h.some.mul_left_inj,
      exact h.some.inv_val.trans ((S.mul_from_left_inv x).symm.trans (by rw h.some_spec)),
  end,
  right_inv := λ x, by { dsimp, ext, rw [from_left_inv_eq_iff], convert (hS x.prop).some.inv_val,
    exact (hS x.prop).some_spec.symm },
  ..S.from_comm_left_inv }

@[simp, to_additive] lemma from_left_inv_left_inv_equiv_symm (x : S) :
  S.from_left_inv ((S.left_inv_equiv hS).symm x) = x := (S.left_inv_equiv hS).right_inv x

@[simp, to_additive] lemma left_inv_equiv_symm_from_left_inv (x : S.left_inv) :
  (S.left_inv_equiv hS).symm (S.from_left_inv x) = x := (S.left_inv_equiv hS).left_inv x

@[to_additive]
lemma left_inv_equiv_mul (x : S.left_inv) : (S.left_inv_equiv hS x : M) * x = 1 := by simp

@[to_additive]
lemma mul_left_inv_equiv (x : S.left_inv) : (x : M) * S.left_inv_equiv hS x = 1 := by simp

@[simp, to_additive] lemma left_inv_equiv_symm_mul (x : S) :
  ((S.left_inv_equiv hS).symm x : M) * x = 1 :=
by { convert S.mul_left_inv_equiv hS ((S.left_inv_equiv hS).symm x), simp }

@[simp, to_additive] lemma mul_left_inv_equiv_symm (x : S) :
  (x : M) * (S.left_inv_equiv hS).symm x = 1 :=
by { convert S.left_inv_equiv_mul hS ((S.left_inv_equiv hS).symm x), simp }

end comm_monoid

section group

variables [group M] (S : submonoid M)

open_locale pointwise

@[to_additive] lemma left_inv_eq_inv : S.left_inv = S⁻¹ :=
submonoid.ext $ λ x,
  ⟨λ h, submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.some_spec).symm ▸ h.some.prop),
    λ h, ⟨⟨_, h⟩, mul_right_inv _⟩⟩

@[simp, to_additive] lemma from_left_inv_eq_inv (x : S.left_inv) :
  (S.from_left_inv x : M) = x⁻¹ :=
by rw [← mul_right_inj (x : M), mul_right_inv, mul_from_left_inv]

end group

section comm_group

variables [comm_group M] (S : submonoid M) (hS : S ≤ is_unit.submonoid M)

@[simp, to_additive] lemma left_inv_equiv_symm_eq_inv (x : S) :
  ((S.left_inv_equiv hS).symm x : M) = x⁻¹ :=
by rw [← mul_right_inj (x : M), mul_right_inv, mul_left_inv_equiv_symm]

end comm_group

end submonoid
