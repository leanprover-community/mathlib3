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

In this file we define `lipschitz`, `pin_group` and `spin_group` and show they form a group.

## Main definitions

* `lipschitz`: the Lipschitz group with a quadratic form.
* `pin_group`: the Pin group defined as the infimum of `lipschitz` and `unitary`.
* `spin_group`: the Spin group defined as the infimum of `pin_group` and `clifford.even`.

## Implementation Notes

Here are some discussion about the latent ambiguity of definition :
https://mathoverflow.net/q/427881/172242 and https://mathoverflow.net/q/251288/172242

The definition of the Lipschitz group `{𝑥 ∈ 𝐶𝑙(𝑉,𝑞) │ 𝑥 𝑖𝑠 𝑖𝑛𝑣𝑒𝑟𝑡𝑖𝑏𝑙𝑒 𝑎𝑛𝑑 𝑥𝑣𝑥⁻¹∈ 𝑉}` is given by:
• Fulton, W. and Harris, J., 2004. Representation theory. New York: Springer, p.chapter 20.
• https://en.wikipedia.org/wiki/Clifford_algebra#Lipschitz_group
But they presumably form a group only in finite dimensions. So we define `lipschitz` with closure of
all the elements in the form of `ι Q m`. We show this definition is at least as large as the
other definition (See `mem_lipschitz_conj_act_le` and `mem_lipschitz_involute_le`) and the reverse
statement presumably being true only in finite dimensions.

## TODO

Try to show the reverse statement is true in finite dimensions.
-/

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

section pin
open clifford_algebra mul_action
open_locale pointwise

/-- `lipschitz` is the subgroup closure of all the elements in the form of `ι Q m` where `ι`
is the canonical linear map `M →ₗ[R] clifford_algebra Q`. -/
def lipschitz (Q : quadratic_form R M) :=
subgroup.closure (coe ⁻¹' set.range (ι Q) : set (clifford_algebra Q)ˣ)

/-- If x is in `lipschitz Q`, then the twisted conjugation of x is closed -/
lemma mem_lipschitz_conj_act_le {x : (clifford_algebra Q)ˣ} [invertible (2 : R)]
  (hx : x ∈ lipschitz Q) : conj_act.to_conj_act x • (ι Q).range ≤ (ι Q).range := sorry
lemma mem_lipschitz_involute_le {x : (clifford_algebra Q)ˣ} [invertible (2 : R)]
  (hx : x ∈ lipschitz Q) (y : M) : involute ↑x * (ι Q y) * ↑x⁻¹ ∈ (ι Q).range := sorry

lemma coe_mem_lipschitz_iff_mem {x : (clifford_algebra Q)ˣ} :
  ↑x ∈ (lipschitz Q).to_submonoid.map (units.coe_hom $ clifford_algebra Q) ↔ x ∈ lipschitz Q :=
begin
  simp only [submonoid.mem_map, subgroup.mem_to_submonoid, units.coe_hom_apply, exists_prop],
  norm_cast,
  exact exists_eq_right,
end

/-- `pin_group Q` is defined as the infimum of `lipschitz Q` and `unitary (clifford_algebra Q)`.
See `mem_iff`. -/
def pin_group (Q : quadratic_form R M) : submonoid (clifford_algebra Q) :=
(lipschitz Q).to_submonoid.map (units.coe_hom $ clifford_algebra Q) ⊓ unitary _

namespace pin_group

/-- An element is in `pin_group Q` if and only if it is in `lipschitz Q` and `unitary`. -/
lemma mem_iff {x : clifford_algebra Q} :
  x ∈ pin_group Q ↔ x ∈ (lipschitz Q).to_submonoid.map (units.coe_hom $ clifford_algebra Q) ∧
    x ∈ unitary (clifford_algebra Q) := iff.rfl
lemma mem_lipschitz {x : clifford_algebra Q} (hx : x ∈ pin_group Q) :
  x ∈ (lipschitz Q).to_submonoid.map (units.coe_hom $ clifford_algebra Q) := hx.1
lemma mem_unitary {x : clifford_algebra Q} (hx : x ∈ pin_group Q) :
  x ∈ unitary (clifford_algebra Q) := hx.2

lemma units_mem_iff {x : (clifford_algebra Q)ˣ} :
  ↑x ∈ pin_group Q ↔ x ∈ lipschitz Q ∧ ↑x ∈ unitary (clifford_algebra Q) :=
by rw [mem_iff, coe_mem_lipschitz_iff_mem]
lemma units_mem_lipschitz {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ pin_group Q) :
  x ∈ lipschitz Q :=
begin
  rw units_mem_iff at hx,
  exact hx.1,
end

lemma units_mem_conj_act_le {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ pin_group Q)
  [invertible (2 : R)] : conj_act.to_conj_act x • (ι Q).range ≤ (ι Q).range :=
mem_lipschitz_conj_act_le (units_mem_lipschitz hx)
lemma units_mem_involute_act_le {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ pin_group Q)
  [invertible (2 : R)] (y : M) : involute ↑x * (ι Q y) * ↑x⁻¹ ∈ (ι Q).range :=
mem_lipschitz_involute_le (units_mem_lipschitz hx) y

@[simp] lemma star_mul_self_of_mem {x : clifford_algebra Q} (hx : x ∈ pin_group Q) :
  star x * x = 1 := (hx.2).1
@[simp] lemma mul_star_self_of_mem {x : clifford_algebra Q} (hx : x ∈ pin_group Q) :
  x * star x = 1 := (hx.2).2

/-- See `star_mem_iff` for both directions. -/
lemma star_mem {x : clifford_algebra Q} (hx : x ∈ pin_group Q) : star x ∈ pin_group Q :=
begin
  rw mem_iff at hx ⊢,
  refine ⟨_, unitary.star_mem hx.2⟩,
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, hx₂, hx₃⟩,
  simp only [subgroup.coe_to_submonoid, set_like.mem_coe] at hy₁,
  simp only [units.coe_hom_apply] at hy₂,
  simp only [submonoid.mem_map, subgroup.mem_to_submonoid, units.coe_hom_apply, exists_prop],
  refine ⟨star y, _, by simp only [hy₂, units.coe_star]⟩,
  rw ← hy₂ at hx₃,
  have hy₃ : y * star y = 1,
  { rw ← units.eq_iff,
    simp only [hx₃, units.coe_mul, units.coe_star, units.coe_one], },
  apply_fun (λ x, y⁻¹ * x) at hy₃,
  simp only [inv_mul_cancel_left, mul_one] at hy₃,
  simp only [hy₃, hy₁, inv_mem_iff],
end

/-- An element is in `pin_group Q` if and only if `star x` is in `pin_group Q`.
See `star_mem` for only one direction. -/
@[simp] lemma star_mem_iff {x : clifford_algebra Q} : star x ∈ pin_group Q ↔ x ∈ pin_group Q :=
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

instance : has_involutive_star (pin_group Q) := ⟨λ _, by { ext, simp only [coe_star, star_star] }⟩

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

/-- `spin_group Q` is defined as the infimum of `pin_group Q` and `clifford_algebra.even Q`.
See `mem_iff`. -/
def spin_group (Q : quadratic_form R M) :=
pin_group Q ⊓ (clifford_algebra.even Q).to_subring.to_submonoid

namespace spin_group

/-- An element is in `spin_group Q` if and only if it is in `pin_group Q` and `even Q`. -/
lemma mem_iff {x : clifford_algebra Q} : x ∈ spin_group Q ↔ x ∈ pin_group Q ∧ x ∈ even Q := iff.rfl
lemma mem_pin {x : clifford_algebra Q} (hx : x ∈ spin_group Q) : x ∈ pin_group Q := hx.1
lemma mem_even {x : clifford_algebra Q} (hx : x ∈ spin_group Q) : x ∈ even Q := hx.2

lemma units_mem_lipschitz {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ spin_group Q) :
  x ∈ lipschitz Q := pin_group.units_mem_lipschitz (mem_pin hx)

lemma mem_involute_eq {x : clifford_algebra Q} (hx : x ∈ spin_group Q) : involute x = x :=
involute_eq_of_mem_even (mem_even hx)

lemma units_involute_act_eq_conj_act {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ spin_group Q)
  [invertible (2 : R)] (y : M) : involute ↑x * (ι Q y) * ↑x⁻¹ = conj_act.to_conj_act x • (ι Q y) :=
by simp_rw [has_smul.smul, conj_act.of_conj_act_to_conj_act, units.mul_left_inj,
  mem_involute_eq hx]

lemma units_mem_conj_act_le {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ spin_group Q)
  [invertible (2 : R)] : conj_act.to_conj_act x • (ι Q).range ≤ (ι Q).range :=
mem_lipschitz_conj_act_le (units_mem_lipschitz hx)
lemma units_mem_involute_act_le {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ spin_group Q)
  [invertible (2 : R)] (y : M) : involute ↑x * (ι Q y) * ↑x⁻¹ ∈ (ι Q).range :=
mem_lipschitz_involute_le (units_mem_lipschitz hx) y

@[simp] lemma star_mul_self_of_mem {x : clifford_algebra Q} (hx : x ∈ spin_group Q) :
  star x * x = 1 := ((hx.1).2).1
@[simp] lemma mul_star_self_of_mem {x : clifford_algebra Q} (hx : x ∈ spin_group Q) :
  x * star x = 1 := ((hx.1).2).2

/-- See `star_mem_iff` for both directions. -/
lemma star_mem {x : clifford_algebra Q} (hx : x ∈ spin_group Q) : star x ∈ spin_group Q :=
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
@[simp] lemma star_mem_iff {x : clifford_algebra Q} : star x ∈ spin_group Q ↔ x ∈ spin_group Q :=
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
