/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao
-/
import group_theory.group_action.conj_act
import algebra.star.unitary
import linear_algebra.clifford_algebra.star
import linear_algebra.clifford_algebra.even

/-!
# The Pin group and the Spin group

In this file we define `lipschitz` consisting all the elements in `(clifford_algebra)ˣ` closed
under conjugation and construct `pin_group` based on `lipschitz` and `unitary`, and we construct
`spin_group` based on `pin_group` and `clifford_algebra.even`. Also, we show `pin_group` and
`spin_group` form a group where the inverse is `star`.

## Main definitions

* `lipschitz`: the Lipschitz group with a quadratic form.
* `pin_group`: the Pin group with a quadratic form.
* `spin_group`: the Spin group with a quadratic form.

-/

variables {R : Type*} [field R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

section pin
open clifford_algebra mul_action
open_locale pointwise

/--
`lipschitz Q` is the subgroup of `(clifford_algebra Q)ˣ` consisting all the elements closed under
conjugation. See `mem_lipschitz_iff`.
-/
def lipschitz (Q : quadratic_form R M): subgroup (clifford_algebra Q)ˣ :=
(stabilizer (conj_act (clifford_algebra Q)ˣ) (ι Q).range).comap
  (conj_act.to_conj_act : (clifford_algebra Q)ˣ ≃* conj_act (clifford_algebra Q)ˣ)

lemma mem_lipschitz_iff {x : (clifford_algebra Q)ˣ} : x ∈ lipschitz Q
  ↔ conj_act.to_conj_act x • (ι Q).range = (ι Q).range := iff.rfl

/--
`pin_group Q` is the submonoid of `clifford_algebra Q` and defined as the infimum of `lipschitz Q`
and `unitary (clifford_algebra)`. See `mem_iff`.
-/
def pin_group (Q : quadratic_form R M) : submonoid (clifford_algebra Q) :=
(lipschitz Q).to_submonoid.map (units.coe_hom $ clifford_algebra Q) ⊓ unitary _

namespace pin_group

/-- An element is in `pin_group Q` if and only if it is in `lipschitz Q` and `unitary _`. -/
lemma mem_iff {x : clifford_algebra Q} : x ∈ pin_group Q ↔
  x ∈ (lipschitz Q).to_submonoid.map (units.coe_hom $ clifford_algebra Q) ∧
    x ∈ unitary (clifford_algebra Q) := iff.rfl
lemma mem_lipschitz {x : clifford_algebra Q} (hx : x ∈ pin_group Q) :
  x ∈ (lipschitz Q).to_submonoid.map (units.coe_hom $ clifford_algebra Q) := hx.1
lemma mem_unitary {x : clifford_algebra Q} (hx : x ∈ pin_group Q) :
  x ∈ unitary (clifford_algebra Q) := hx.2

@[simp] lemma star_mul_self_of_mem {x : clifford_algebra Q}
  (hx : x ∈ pin_group Q) : star x * x = 1 := (hx.2).1
@[simp] lemma mul_star_self_of_mem {x : clifford_algebra Q}
  (hx : x ∈ pin_group Q) : x * star x = 1 := (hx.2).2

/-- See `star_mem_iff` for both directions. -/
lemma star_mem {x : clifford_algebra Q} (hx : x ∈ pin_group Q) :
  star x ∈ pin_group Q :=
begin
  rw mem_iff at hx ⊢,
  refine ⟨_, unitary.star_mem hx.2⟩,
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, hx₂, hx₃⟩,
  simp only [subgroup.coe_to_submonoid, set_like.mem_coe] at hy₁,
  simp only [units.coe_hom_apply] at hy₂,
  simp only [submonoid.mem_map, subgroup.mem_to_submonoid,
    units.coe_hom_apply, exists_prop],
  refine ⟨star y, _, by simp only [hy₂, units.coe_star]⟩,
  rw ← hy₂ at hx₃,
  have hy₃ : y * star y = 1,
  { rw ← units.eq_iff,
    simp only [hx₃, units.coe_mul, units.coe_star, units.coe_one], },
  apply_fun (λ x, y⁻¹ * x) at hy₃,
  simp only [inv_mul_cancel_left, mul_one] at hy₃,
  simp only [hy₃, hy₁, inv_mem_iff],
end

/--
An element is in `pin_group Q` if and only if `star x` is in `pin_group Q`.
See `star_mem` for only one direction.
-/
@[simp] lemma star_mem_iff {x : clifford_algebra Q} :
  star x ∈ pin_group Q ↔ x ∈ pin_group Q :=
begin
  refine ⟨_, star_mem⟩,
  intro hx,
  convert star_mem hx,
  exact (star_star x).symm,
end

instance : has_star (pin_group Q) := ⟨λ x, ⟨star x, star_mem x.prop⟩⟩

@[simp, norm_cast] lemma coe_star {x : pin_group Q} :
  ↑(star x) = (star x : clifford_algebra Q) := rfl

lemma coe_star_mul_self (x : pin_group Q) :
  (star x : clifford_algebra Q) * x = 1 := star_mul_self_of_mem x.prop
lemma coe_mul_star_self (x : pin_group Q) :
  (x : clifford_algebra Q) * star x = 1 := mul_star_self_of_mem x.prop

@[simp] lemma star_mul_self (x : pin_group Q) : star x * x = 1 := subtype.ext $ coe_star_mul_self x
@[simp] lemma mul_star_self (x : pin_group Q) : x * star x = 1 := subtype.ext $ coe_mul_star_self x

/-- `pin_group Q` forms a group where the inverse is `star`. -/
instance : group (pin_group Q) :=
{ inv := star,
  mul_left_inv := star_mul_self,
  ..submonoid.to_monoid _ }

instance : has_involutive_star (pin_group Q) :=
⟨λ _, by { ext, simp only [coe_star, star_star] }⟩

instance : star_semigroup (pin_group Q) :=
⟨λ _ _, by { ext, simp only [coe_star, submonoid.coe_mul, star_mul] }⟩

instance : inhabited (pin_group Q) := ⟨1⟩

lemma star_eq_inv (x : pin_group Q) : star x = x⁻¹ := rfl

lemma star_eq_inv' : (star : pin_group Q → pin_group Q) = has_inv.inv := rfl

/-- The elements in `pin_group Q` embed into (clifford_algebra Q)ˣ. -/
@[simps]
def to_units : pin_group Q →* (clifford_algebra Q)ˣ :=
{ to_fun := λ x, ⟨x, ↑(x⁻¹), coe_mul_star_self x, coe_star_mul_self x⟩,
  map_one' := units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

lemma to_units_injective : function.injective (to_units : pin_group Q → (clifford_algebra Q)ˣ) :=
λ x y h, subtype.ext $ units.ext_iff.mp h

end pin_group
end pin

section spin
open clifford_algebra mul_action
open_locale pointwise

/--
`spin_group Q` is the submonoid of `clifford_algebra Q` and defined as the infimum of `pin_group Q`
and `clifford_algebra.even Q`. See `mem_iff`.
-/
def spin_group (Q : quadratic_form R M) :=
pin_group Q ⊓ (clifford_algebra.even Q).to_subring.to_submonoid

namespace spin_group

/-- An element is in `spin_group Q` if and only if it is in `pin_group Q` and `even Q`. -/
lemma mem_iff {x : clifford_algebra Q} : x ∈ spin_group Q ↔ x ∈ pin_group Q ∧
  x ∈ clifford_algebra.even Q := iff.rfl
lemma mem_pin {x : clifford_algebra Q} (hx : x ∈ spin_group Q) :
  x ∈ pin_group Q := hx.1
lemma mem_clifford_even {x : clifford_algebra Q} (hx : x ∈ spin_group Q) :
  x ∈ clifford_algebra.even Q := hx.2

@[simp] lemma star_mul_self_of_mem {x : clifford_algebra Q}
  (hx : x ∈ spin_group Q) : star x * x = 1 := ((hx.1).2).1
@[simp] lemma mul_star_self_of_mem {x : clifford_algebra Q}
  (hx : x ∈ spin_group Q) : x * star x = 1 := ((hx.1).2).2

/-- See `star_mem_iff` for both directions. -/
lemma star_mem {x : clifford_algebra Q} (hx : x ∈ spin_group Q) :
  star x ∈ spin_group Q :=
begin
  rw mem_iff at hx ⊢,
  cases hx with hx₁ hx₂,
  refine ⟨pin_group.star_mem hx₁, _⟩,
  dsimp only [clifford_algebra.even] at hx₂ ⊢,
  simp only [submodule.mem_to_subalgebra] at hx₂ ⊢,
  simp only [star_def, reverse_mem_even_odd_iff, involute_mem_even_odd_iff, hx₂],
end

/--
An element is in `spin_group Q` if and only if `star x` is in `spin_group Q`.
See `star_mem` for only one direction.
-/
@[simp] lemma star_mem_iff {x : clifford_algebra Q} :
  star x ∈ spin_group Q ↔ x ∈ spin_group Q :=
begin
  refine ⟨_, star_mem⟩,
  intro hx,
  convert star_mem hx,
  exact (star_star x).symm,
end

instance : has_star (spin_group Q) := ⟨λ x, ⟨star x, star_mem x.prop⟩⟩

@[simp, norm_cast] lemma coe_star {x : spin_group Q} :
  ↑(star x) = (star x : clifford_algebra Q) := rfl

lemma coe_star_mul_self (x : spin_group Q) :
  (star x : clifford_algebra Q) * x = 1 := star_mul_self_of_mem x.prop
lemma coe_mul_star_self (x : spin_group Q) :
  (x : clifford_algebra Q) * star x = 1 := mul_star_self_of_mem x.prop

@[simp] lemma star_mul_self (x : spin_group Q) : star x * x = 1 := subtype.ext $ coe_star_mul_self x
@[simp] lemma mul_star_self (x : spin_group Q) : x * star x = 1 := subtype.ext $ coe_mul_star_self x

/-- `spin_group Q` forms a group where the inverse is `star`. -/
instance : group (spin_group Q) :=
{ inv := star,
  mul_left_inv := star_mul_self,
  ..submonoid.to_monoid _ }

instance : has_involutive_star (spin_group Q) :=
⟨λ _, by { ext, simp only [coe_star, star_star] }⟩

instance : star_semigroup (spin_group Q) :=
⟨λ _ _, by { ext, simp only [coe_star, submonoid.coe_mul, star_mul] }⟩

instance : inhabited (spin_group Q) := ⟨1⟩

lemma star_eq_inv (x : spin_group Q) : star x = x⁻¹ := rfl

lemma star_eq_inv' : (star : spin_group Q → spin_group Q) = has_inv.inv := rfl

/-- The elements in `spin_group Q` embed into (clifford_algebra Q)ˣ. -/
@[simps]
def to_units : spin_group Q →* (clifford_algebra Q)ˣ :=
{ to_fun := λ x, ⟨x, ↑(x⁻¹), coe_mul_star_self x, coe_star_mul_self x⟩,
  map_one' := units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

lemma to_units_injective : function.injective (to_units : spin_group Q → (clifford_algebra Q)ˣ) :=
λ x y h, subtype.ext $ units.ext_iff.mp h

end spin_group
end spin
