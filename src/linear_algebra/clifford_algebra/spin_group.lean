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
all the elements in the form of `ι Q m`, and we show this definition is at least as large as the
other definition (See `mem_lipschitz_conj_act_le` and `mem_lipschitz_involute_le`). The reverse
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

/-- If x is in `lipschitz Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
lemma mem_lipschitz_conj_act_le {x : (clifford_algebra Q)ˣ} [invertible (2 : R)]
  (hx : x ∈ lipschitz Q) : conj_act.to_conj_act x • (ι Q).range ≤ (ι Q).range :=
begin
  refine @subgroup.closure_induction'' _ _ _ _ _ hx _ _ _ _,
  { rintros x ⟨z, hz⟩ y ⟨a, ha⟩,
    simp only [has_smul.smul, set_like.mem_coe, linear_map.mem_range,
      distrib_mul_action.to_linear_map_apply, conj_act.of_conj_act_to_conj_act] at ha,
    rcases ha with ⟨⟨b, hb⟩, ha1⟩,
    subst hb,
    letI := x.invertible,
    letI : invertible (ι Q z) := by rwa hz,
    rw [linear_map.mem_range, ← ha1, ← inv_of_units x],
    suffices : ∃ (y : M), (ι Q) y = (ι Q z) * (ι Q) b * ⅟ (ι Q z),
    { convert this,
      ext1,
      congr';
      simp only [hz.symm, subsingleton.helim (congr_arg invertible hz.symm)], },
    letI := invertible_of_invertible_ι Q z,
    refine ⟨(⅟(Q z) * quadratic_form.polar Q z b) • z - b, (ι_mul_ι_mul_inv_of_ι Q z b).symm⟩, },
  { rintros x ⟨z, hz1⟩ y ⟨a, ⟨b, hb⟩, ha2⟩,
    simp only [conj_act.to_conj_act_inv, distrib_mul_action.to_linear_map_apply,
      has_smul.smul, conj_act.of_conj_act_inv, conj_act.of_conj_act_to_conj_act,
        inv_inv] at ha2,
    subst hb,
    subst ha2,
    letI := x.invertible,
    letI : invertible (ι Q z) := by rwa hz1,
    rw [linear_map.mem_range, ← inv_of_units x],
    suffices : ∃ (y : M), (ι Q) y = ⅟ (ι Q z) * (ι Q) b * (ι Q z),
    { convert this,
      ext1,
      congr';
      simp only [hz1.symm, subsingleton.helim (congr_arg invertible hz1.symm)], },
    letI := invertible_of_invertible_ι Q z,
    refine ⟨(⅟(Q z) * quadratic_form.polar Q z b) • z - b, (inv_of_ι_mul_ι_mul_ι Q z b).symm⟩, },
  { simp only [conj_act.to_conj_act_one, one_smul, le_refl], },
  { intros x y hx1 hy1 z hz1,
    simp only [conj_act.to_conj_act_mul] at hz1,
    suffices : (conj_act.to_conj_act x * conj_act.to_conj_act y) • (ι Q).range ≤ (ι Q).range,
    { exact this hz1, },
    { rintros m ⟨a, ⟨b, hb⟩, ha⟩,
      simp only [distrib_mul_action.to_linear_map_apply, has_smul.smul, conj_act.of_conj_act_mul,
       conj_act.of_conj_act_to_conj_act, units.coe_mul, mul_inv_rev] at ha,
      subst hb,
      have hb : ↑x * (↑y * (ι Q) b * ↑y⁻¹) * ↑x⁻¹ = m := by simp_rw [← ha, mul_assoc],
      have hy2 : ↑y * (ι Q) b * ↑y⁻¹ ∈ conj_act.to_conj_act y • (ι Q).range := by simp only
        [has_smul.smul, exists_exists_eq_and, exists_apply_eq_apply, submodule.mem_map,
          linear_map.mem_range, distrib_mul_action.to_linear_map_apply,
            conj_act.of_conj_act_to_conj_act],
      specialize hy1 hy2,
      have hx2 : ↑x * (↑y * (ι Q) b * ↑y⁻¹) * ↑x⁻¹ ∈ conj_act.to_conj_act x • (ι Q).range,
      { simp only [has_smul.smul, units.mul_left_inj, units.mul_right_inj, exists_exists_eq_and,
          submodule.mem_map, linear_map.mem_range, distrib_mul_action.to_linear_map_apply,
            conj_act.of_conj_act_to_conj_act],
        exact hy1, },
      specialize hx1 hx2,
      rwa hb at hx1, }, },
end

/-- This is another version of `mem_lipschitz_conj_act_le` which uses `involute`.-/
lemma mem_lipschitz_involute_le {x : (clifford_algebra Q)ˣ} [invertible (2 : R)]
  (hx : x ∈ lipschitz Q) (y : M) : involute ↑x * (ι Q y) * ↑x⁻¹ ∈ (ι Q).range :=
begin
  revert y,
  refine @subgroup.closure_induction'' _ _ _ _ _ hx _ _ _ _,
  { rintros x ⟨z, hz⟩ y,
    letI := x.invertible,
    letI : invertible (ι Q z) := by rwa hz,
    rw [linear_map.mem_range, ← inv_of_units x],
    suffices : ∃ (y_1 : M), (ι Q) y_1 = -(ι Q z) * (ι Q) y * ⅟ (ι Q z),
    { convert this,
      ext1,
      congr',
      { rw [← hz, involute_ι], },
      { exact hz.symm, },
      { exact subsingleton.helim (congr_arg invertible hz.symm) _ _, }, },
    letI := invertible_of_invertible_ι Q z,
    refine ⟨-((⅟(Q z) * quadratic_form.polar Q z y) • z - y), by simp only
      [map_neg, neg_mul, ι_mul_ι_mul_inv_of_ι Q z y]⟩, },
  { rintros x ⟨z, hz⟩ y,
    letI := x.invertible,
    letI : invertible (ι Q z) := by rwa hz,
    letI := invertible_neg (ι Q z),
    letI := invertible.map (involute : clifford_algebra Q →ₐ[R] clifford_algebra Q) ↑x,
    rw [inv_inv, linear_map.mem_range, ← inv_of_units x, map_inv_of],
    suffices : ∃ (y_1 : M), (ι Q) y_1 = -⅟ (ι Q z) * (ι Q) y * (ι Q z),
    { convert this,
      ext1,
      congr',
      { rw ← inv_of_neg,
        apply invertible_unique,
        rw [← hz, involute_ι], },
      { exact hz.symm, }, },
    letI := invertible_of_invertible_ι Q z,
    refine ⟨-((⅟(Q z) * quadratic_form.polar Q z y) • z - y), by simp only
      [map_neg, neg_mul, inv_of_ι_mul_ι_mul_ι Q z y]⟩, },
  { simp only [units.coe_one, map_one, one_mul, inv_one, mul_one,
      linear_map.mem_range, exists_apply_eq_apply, forall_const], },
  { intros a b ha hb y,
    simp only [units.coe_mul, map_mul, mul_inv_rev, linear_map.mem_range],
    cases hb y with c hc,
    suffices : ∃ (y_1 : M), (ι Q) y_1 = involute ↑a * (involute ↑b * (ι Q) y * ↑b⁻¹) * ↑a⁻¹,
    { cases this with p hp,
      refine ⟨p, by simp only [hp, mul_assoc]⟩, },
    rw ← hc,
    exact ha c, },
end

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
  x ∈ lipschitz Q := ((units_mem_iff).1 hx).1

/-- If x is in `pin_group Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
lemma units_mem_conj_act_le {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ pin_group Q)
  [invertible (2 : R)] : conj_act.to_conj_act x • (ι Q).range ≤ (ι Q).range :=
mem_lipschitz_conj_act_le (units_mem_lipschitz hx)

/-- This is another version of `units_mem_conj_act_le` which uses `involute`. -/
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

/-- If x is in `spin_group Q`, then `involute x` is equal to x.-/
lemma mem_involute_eq {x : clifford_algebra Q} (hx : x ∈ spin_group Q) : involute x = x :=
involute_eq_of_mem_even (mem_even hx)

lemma units_involute_act_eq_conj_act {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ spin_group Q)
  [invertible (2 : R)] (y : M) : involute ↑x * (ι Q y) * ↑x⁻¹ = conj_act.to_conj_act x • (ι Q y) :=
by simp_rw [has_smul.smul, conj_act.of_conj_act_to_conj_act, units.mul_left_inj,
  mem_involute_eq hx]

/-- If x is in `spin_group Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions.-/
lemma units_mem_conj_act_le {x : (clifford_algebra Q)ˣ} (hx : ↑x ∈ spin_group Q)
  [invertible (2 : R)] : conj_act.to_conj_act x • (ι Q).range ≤ (ι Q).range :=
mem_lipschitz_conj_act_le (units_mem_lipschitz hx)

/-- This is another version of `units_mem_conj_act_le` which uses `involute`.-/
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

instance : has_involutive_star (spin_group Q) := ⟨λ _, by { ext, simp only [coe_star, star_star] }⟩

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
