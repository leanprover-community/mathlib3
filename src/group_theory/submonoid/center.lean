/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.submonoid.operations
import data.fintype.basic

/-!
# Centers of magmas and monoids

## Main definitions

* `set.center`: the center of a magma
* `submonoid.center`: the center of a monoid
* `set.add_center`: the center of an additive magma
* `add_submonoid.center`: the center of an additive monoid

We provide `subgroup.center`, `add_subgroup.center`, `subsemiring.center`, and `subring.center` in
other files.
-/

variables {M : Type*}

namespace set

variables (M)

/-- The center of a magma. -/
@[to_additive add_center /-" The center of an additive magma. "-/]
def center [has_mul M] : set M := {z | ∀ m, m * z = z * m}

@[to_additive mem_add_center]
lemma mem_center_iff [has_mul M] {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := iff.rfl

instance decidable_mem_center [has_mul M] [decidable_eq M] [fintype M] :
  decidable_pred (∈ center M) :=
λ _, decidable_of_iff' _ (mem_center_iff M)

@[simp, to_additive zero_mem_add_center]
lemma one_mem_center [mul_one_class M] : (1 : M) ∈ set.center M := by simp [mem_center_iff]

@[simp]
lemma zero_mem_center [mul_zero_class M] : (0 : M) ∈ set.center M := by simp [mem_center_iff]

variables {M}

@[simp, to_additive add_mem_add_center]
lemma mul_mem_center [semigroup M] {a b : M}
  (ha : a ∈ set.center M) (hb : b ∈ set.center M) : a * b ∈ set.center M :=
λ g, by rw [mul_assoc, ←hb g, ← mul_assoc, ha g, mul_assoc]

@[simp, to_additive neg_mem_add_center]
lemma inv_mem_center [group M] {a : M} (ha : a ∈ set.center M) : a⁻¹ ∈ set.center M :=
λ g, by rw [← inv_inj, mul_inv_rev, inv_inv, ← ha, mul_inv_rev, inv_inv]

@[simp]
lemma add_mem_center [distrib M] {a b : M}
  (ha : a ∈ set.center M) (hb : b ∈ set.center M) : a + b ∈ set.center M :=
λ c, by rw [add_mul, mul_add, ha c, hb c]

@[simp]
lemma neg_mem_center [ring M] {a : M} (ha : a ∈ set.center M) : -a ∈ set.center M :=
λ c, by rw [←neg_mul_comm, ha (-c), neg_mul_comm]

@[to_additive subset_add_center_add_units]
lemma subset_center_units [monoid M] :
  (coe : units M → M) ⁻¹' center M ⊆ set.center (units M) :=
λ a ha b, units.ext $ ha _

lemma center_units_subset [group_with_zero M] :
  set.center (units M) ⊆ (coe : units M → M) ⁻¹' center M :=
λ a ha b, begin
  obtain rfl | hb := eq_or_ne b 0,
  { rw [zero_mul, mul_zero], },
  { exact units.ext_iff.mp (ha (units.mk0 _ hb)) }
end

/-- In a group with zero, the center of the units is the preimage of the center. -/
lemma center_units_eq [group_with_zero M] :
  set.center (units M) = (coe : units M → M) ⁻¹' center M :=
subset.antisymm center_units_subset subset_center_units

@[simp]
lemma inv_mem_center₀ [group_with_zero M] {a : M} (ha : a ∈ set.center M) : a⁻¹ ∈ set.center M :=
begin
  obtain rfl | ha0 := eq_or_ne a 0,
  { rw inv_zero, exact zero_mem_center M },
  rcases is_unit.mk0 _ ha0 with ⟨a, rfl⟩,
  rw ←units.coe_inv',
  exact center_units_subset (inv_mem_center (subset_center_units ha)),
end

@[simp, to_additive sub_mem_add_center]
lemma div_mem_center [group M] {a b : M} (ha : a ∈ set.center M) (hb : b ∈ set.center M) :
  a / b ∈ set.center M :=
begin
  rw [div_eq_mul_inv],
  exact mul_mem_center ha (inv_mem_center hb),
end

@[simp]
lemma div_mem_center₀ [group_with_zero M] {a b : M} (ha : a ∈ set.center M)
  (hb : b ∈ set.center M) : a / b ∈ set.center M :=
begin
  rw div_eq_mul_inv,
  exact mul_mem_center ha (inv_mem_center₀ hb),
end

variables (M)

@[simp, to_additive add_center_eq_univ]
lemma center_eq_univ [comm_semigroup M] : center M = set.univ :=
subset.antisymm (subset_univ _) $ λ x _ y, mul_comm y x

end set

namespace submonoid
section
variables (M) [monoid M]

/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive "The center of a monoid `M` is the set of elements that commute with everything in
`M`"]
def center : submonoid M :=
{ carrier := set.center M,
  one_mem' := set.one_mem_center M,
  mul_mem' := λ a b, set.mul_mem_center }

@[to_additive] lemma coe_center : ↑(center M) = set.center M := rfl

variables {M}

@[to_additive] lemma mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := iff.rfl

instance decidable_mem_center [decidable_eq M] [fintype M] : decidable_pred (∈ center M) :=
λ _, decidable_of_iff' _ mem_center_iff

/-- The center of a monoid is commutative. -/
instance : comm_monoid (center M) :=
{ mul_comm := λ a b, subtype.ext $ b.prop _,
  .. (center M).to_monoid }

end

section
variables (M) [comm_monoid M]

@[simp] lemma center_eq_top : center M = ⊤ :=
set_like.coe_injective (set.center_eq_univ M)

end

end submonoid
