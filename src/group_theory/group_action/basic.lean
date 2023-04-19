/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.fintype.card
import group_theory.group_action.defs
import group_theory.group_action.group
import data.setoid.basic
import data.set.pointwise.smul
import group_theory.subgroup.basic

/-!
# Basic properties of group actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file primarily concerns itself with orbits, stabilizers, and other objects defined in terms of
actions. Despite this file being called `basic`, low-level helper lemmas for algebraic manipulation
of `•` belong elsewhere.

## Main definitions

* `mul_action.orbit`
* `mul_action.fixed_points`
* `mul_action.fixed_by`
* `mul_action.stabilizer`

-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open_locale pointwise
open function

namespace mul_action

variables (α) [monoid α] [mul_action α β]

/-- The orbit of an element under an action. -/
@[to_additive "The orbit of an element under an action."]
def orbit (b : β) := set.range (λ x : α, x • b)

variable {α}

@[to_additive] lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
iff.rfl

@[simp, to_additive] lemma mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
⟨x, rfl⟩

@[simp, to_additive] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, by simp [mul_action.one_smul]⟩

@[to_additive] lemma orbit_nonempty (b : β) : set.nonempty (orbit α b) := set.range_nonempty _

@[to_additive] lemma maps_to_smul_orbit (a : α) (b : β) :
  set.maps_to ((•) a) (orbit α b) (orbit α b) :=
set.range_subset_iff.2 $ λ a', ⟨a * a', mul_smul _ _ _⟩

@[to_additive] lemma smul_orbit_subset (a : α) (b : β) : a • orbit α b ⊆ orbit α b :=
(maps_to_smul_orbit a b).image_subset

@[to_additive] lemma orbit_smul_subset (a : α) (b : β) : orbit α (a • b) ⊆ orbit α b :=
set.range_subset_iff.2 $ λ a', mul_smul a' a b ▸ mem_orbit _ _

@[to_additive] instance {b : β} : mul_action α (orbit α b) :=
{ smul := λ a, (maps_to_smul_orbit a b).restrict _ _ _,
  one_smul := λ a, subtype.ext (one_smul α a),
  mul_smul := λ a a' b', subtype.ext (mul_smul a a' b') }

@[simp, to_additive] lemma orbit.coe_smul {b : β} {a : α} {b' : orbit α b} :
  ↑(a • b') = a • (b' : β) :=
rfl

variables (α) (β)

/-- The set of elements fixed under the whole action. -/
@[to_additive "The set of elements fixed under the whole action."]
def fixed_points : set β := {b : β | ∀ x : α, x • b = b}

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
@[to_additive "`fixed_by g` is the subfield of elements fixed by `g`."]
def fixed_by (g : α) : set β :=
{ x | g • x = x }

@[to_additive] theorem fixed_eq_Inter_fixed_by : fixed_points α β = ⋂ g : α, fixed_by α β g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g, λ hx g, by exact (set.mem_Inter.1 hx g : _)⟩

variables {α} (β)

@[simp, to_additive] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

@[simp, to_additive] lemma mem_fixed_by {g : α} {b : β} :
  b ∈ fixed_by α β g ↔ g • b = b := iff.rfl

@[to_additive] lemma mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔
  (∀ b', b' ∈ orbit α b → b' = b) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, h _ (mem_orbit _ _)⟩

variables (α) {β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
@[to_additive "The stabilizer of a point `b` as an additive submonoid of `α`."]
def stabilizer.submonoid (b : β) : submonoid α :=
{ carrier := { a | a • b = b },
  one_mem' := one_smul _ b,
  mul_mem' := λ a a' (ha : a • b = b) (hb : a' • b = b),
    show (a * a') • b = b, by rw [←smul_smul, hb, ha] }

@[simp, to_additive] lemma mem_stabilizer_submonoid_iff {b : β} {a : α} :
  a ∈ stabilizer.submonoid α b ↔ a • b = b := iff.rfl

@[to_additive] lemma orbit_eq_univ [is_pretransitive α β] (x : β) :
  orbit α x = set.univ :=
(surjective_smul α x).range_eq

variables {α} {β}

@[to_additive] lemma mem_fixed_points_iff_card_orbit_eq_one {a : β}
  [fintype (orbit α a)] : a ∈ fixed_points α β ↔ fintype.card (orbit α a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    calc x • a = z : subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm }
end

end mul_action

namespace mul_action
variable (α)
variables [group α] [mul_action α β]

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive "The stabilizer of an element under an action, i.e. what sends the element to itself.
An additive subgroup."]
def stabilizer (b : β) : subgroup α :=
{ inv_mem' := λ a (ha : a • b = b), show a⁻¹ • b = b, by rw [inv_smul_eq_iff, ha]
  ..stabilizer.submonoid α b }

variables {α} {β}

@[simp, to_additive] lemma mem_stabilizer_iff {b : β} {a : α} :
  a ∈ stabilizer α b ↔ a • b = b := iff.rfl

@[simp, to_additive] lemma smul_orbit (a : α) (b : β) :
  a • orbit α b = orbit α b :=
(smul_orbit_subset a b).antisymm $
  calc orbit α b = a • a⁻¹ • orbit α b : (smul_inv_smul _ _).symm
             ... ⊆ a • orbit α b       : set.image_subset _ (smul_orbit_subset _ _)

@[simp, to_additive] lemma orbit_smul (a : α) (b : β) : orbit α (a • b) = orbit α b :=
(orbit_smul_subset a b).antisymm $
  calc orbit α b = orbit α (a⁻¹ • a • b) : by rw inv_smul_smul
             ... ⊆ orbit α (a • b)       : orbit_smul_subset _ _

/-- The action of a group on an orbit is transitive. -/
@[to_additive "The action of an additive group on an orbit is transitive."]
instance (x : β) : is_pretransitive α (orbit α x) :=
⟨by { rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩, use b * a⁻¹, ext1, simp [mul_smul] }⟩

@[to_additive] lemma orbit_eq_iff {a b : β} :
   orbit α a = orbit α b ↔ a ∈ orbit α b:=
⟨λ h, h ▸ mem_orbit_self _, λ ⟨c, hc⟩, hc ▸ orbit_smul _ _⟩

variables (α) {β}

@[to_additive] lemma mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) :=
by simp only [orbit_smul, mem_orbit_self]

@[to_additive] lemma smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) :=
by simp only [orbit_smul, mem_orbit]

variables (α) (β)
/-- The relation 'in the same orbit'. -/
@[to_additive "The relation 'in the same orbit'."]
def orbit_rel : setoid β :=
{ r := λ a b, a ∈ orbit α b,
  iseqv := ⟨mem_orbit_self, λ a b, by simp [orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

local attribute [instance] orbit_rel

variables {α} {β}

/-- When you take a set `U` in `β`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `α`. -/
@[to_additive "When you take a set `U` in `β`, push it down to the quotient, and pull back, you get
the union of the orbit of `U` under `α`."] lemma quotient_preimage_image_eq_union_mul (U : set β) :
  quotient.mk ⁻¹' (quotient.mk '' U) = ⋃ a : α, ((•) a) '' U :=
begin
  set f : β → quotient (mul_action.orbit_rel α β) := quotient.mk,
  ext,
  split,
  { rintros ⟨y , hy, hxy⟩,
    obtain ⟨a, rfl⟩ := quotient.exact hxy,
    rw set.mem_Union,
    exact ⟨a⁻¹, a • x, hy, inv_smul_smul a x⟩ },
  { intros hx,
    rw set.mem_Union at hx,
    obtain ⟨a, u, hu₁, hu₂⟩ := hx,
    rw [set.mem_preimage, set.mem_image_iff_bex],
    refine ⟨a⁻¹ • x, _, by simp only [quotient.eq]; use a⁻¹⟩,
    rw ← hu₂,
    convert hu₁,
    simp only [inv_smul_smul], },
end

@[to_additive] lemma disjoint_image_image_iff {U V : set β} :
  disjoint (quotient.mk '' U) (quotient.mk '' V) ↔ ∀ x ∈ U, ∀ a : α, a • x ∉ V :=
begin
  set f : β → quotient (mul_action.orbit_rel α β) := quotient.mk,
  refine ⟨λ h x x_in_U a a_in_V,
    h.le_bot ⟨⟨x, x_in_U, quotient.sound ⟨a⁻¹, _⟩⟩, ⟨a • x, a_in_V, rfl⟩⟩, _⟩,
  { simp },
  { intro h,
    rw set.disjoint_left,
    rintro x ⟨y, hy₁, hy₂⟩ ⟨z, hz₁, hz₂⟩,
    obtain ⟨a, rfl⟩ := quotient.exact (hz₂.trans hy₂.symm),
    exact h y hy₁ a hz₁ }
end

@[to_additive]
lemma image_inter_image_iff (U V : set β) :
  (quotient.mk '' U) ∩ (quotient.mk '' V) = ∅ ↔ ∀ x ∈ U, ∀ a : α, a • x ∉ V :=
set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff

variables (α β)

/-- The quotient by `mul_action.orbit_rel`, given a name to enable dot notation. -/
@[reducible, to_additive "The quotient by `add_action.orbit_rel`, given a name to enable dot
notation."]
def orbit_rel.quotient : Type* := quotient $ orbit_rel α β

variables {α β}

/-- The orbit corresponding to an element of the quotient by `mul_action.orbit_rel` -/
@[to_additive "The orbit corresponding to an element of the quotient by `add_action.orbit_rel`"]
def orbit_rel.quotient.orbit (x : orbit_rel.quotient α β) : set β :=
quotient.lift_on' x (orbit α) $ λ _ _, mul_action.orbit_eq_iff.2

@[simp, to_additive]
lemma orbit_rel.quotient.orbit_mk (b : β) :
  orbit_rel.quotient.orbit (quotient.mk' b : orbit_rel.quotient α β) = orbit α b := rfl

@[to_additive]
lemma orbit_rel.quotient.mem_orbit {b : β} {x : orbit_rel.quotient α β} :
  b ∈ x.orbit ↔ quotient.mk' b = x :=
by { induction x using quotient.induction_on', rw quotient.eq', refl }

/-- Note that `hφ = quotient.out_eq'` is a useful choice here. -/
@[to_additive "Note that `hφ = quotient.out_eq'` is a useful choice here."]
lemma orbit_rel.quotient.orbit_eq_orbit_out (x : orbit_rel.quotient α β)
  {φ : orbit_rel.quotient α β → β} (hφ : right_inverse φ quotient.mk') :
  orbit_rel.quotient.orbit x = orbit α (φ x) :=
begin
  conv_lhs { rw ←hφ x },
  induction x using quotient.induction_on',
  refl,
end

variables (α) (β)

local notation `Ω` := orbit_rel.quotient α β

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.

This version is expressed in terms of `mul_action.orbit_rel.quotient.orbit` instead of
`mul_action.orbit`, to avoid mentioning `quotient.out'`. -/
@[to_additive "Decomposition of a type `X` as a disjoint union of its orbits under an additive group
action.

This version is expressed in terms of `add_action.orbit_rel.quotient.orbit` instead of
`add_action.orbit`, to avoid mentioning `quotient.out'`. "]
def self_equiv_sigma_orbits' : β ≃ Σ ω : Ω, ω.orbit :=
calc  β
    ≃ Σ (ω : Ω), {b // quotient.mk' b = ω} : (equiv.sigma_fiber_equiv quotient.mk').symm
... ≃ Σ (ω : Ω), ω.orbit :
        equiv.sigma_congr_right $ λ ω, equiv.subtype_equiv_right $ λ x,
          orbit_rel.quotient.mem_orbit.symm

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive "Decomposition of a type `X` as a disjoint union of its orbits under an additive group
action."]
def self_equiv_sigma_orbits : β ≃ Σ (ω : Ω), orbit α ω.out' :=
(self_equiv_sigma_orbits' α β).trans $ equiv.sigma_congr_right $ λ i,
  equiv.set.of_eq $ orbit_rel.quotient.orbit_eq_orbit_out _ quotient.out_eq'

variables {α β}

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g • x` is `gSg⁻¹`. -/
lemma stabilizer_smul_eq_stabilizer_map_conj (g : α) (x : β) :
  (stabilizer α (g • x) = (stabilizer α x).map (mul_aut.conj g).to_monoid_hom) :=
begin
  ext h,
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul, mul_left_inv,
      one_smul, ← mem_stabilizer_iff, subgroup.mem_map_equiv, mul_aut.conj_symm_apply]
end

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizer_equiv_stabilizer_of_orbit_rel {x y : β} (h : (orbit_rel α β).rel x y) :
  stabilizer α x ≃* stabilizer α y :=
let g : α := classical.some h in
have hg : g • y = x := classical.some_spec h,
have this : stabilizer α x = (stabilizer α y).map (mul_aut.conj g).to_monoid_hom,
  by rw [← hg, stabilizer_smul_eq_stabilizer_map_conj],
(mul_equiv.subgroup_congr this).trans ((mul_aut.conj g).subgroup_map $ stabilizer α y).symm

end mul_action

namespace add_action

variables [add_group α] [add_action α β]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
lemma stabilizer_vadd_eq_stabilizer_map_conj (g : α) (x : β) :
  (stabilizer α (g +ᵥ x) = (stabilizer α x).map (add_aut.conj g).to_add_monoid_hom) :=
begin
  ext h,
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g) , vadd_vadd, vadd_vadd, vadd_vadd,
      add_left_neg, zero_vadd, ← mem_stabilizer_iff, add_subgroup.mem_map_equiv,
      add_aut.conj_symm_apply]
end

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizer_equiv_stabilizer_of_orbit_rel {x y : β}
  (h : (orbit_rel α β).rel x y) :
  stabilizer α x ≃+ stabilizer α y :=
let g : α := classical.some h in
have hg : g +ᵥ y = x := classical.some_spec h,
have this : stabilizer α x = (stabilizer α y).map (add_aut.conj g).to_add_monoid_hom,
  by rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj],
(add_equiv.add_subgroup_congr this).trans
  ((add_aut.conj g).add_subgroup_map $ stabilizer α y).symm

end add_action

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `is_smul_regular`.
The typeclass that restricts all terms of `M` to have this property is `no_zero_smul_divisors`. -/
lemma smul_cancel_of_non_zero_divisor {M R : Type*}
  [monoid M] [non_unital_non_assoc_ring R] [distrib_mul_action M R]
  (k : M) (h : ∀ (x : R), k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
  a = b :=
begin
  rw ←sub_eq_zero,
  refine h _ _,
  rw [smul_sub, h', sub_self]
end
