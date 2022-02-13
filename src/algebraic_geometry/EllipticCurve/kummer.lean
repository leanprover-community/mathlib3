/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import data.zmod.quotient
import number_theory.class_number.number_field

-- Note: temporary
import algebraic_geometry.EllipticCurve.group
import algebraic_geometry.EllipticCurve.valuation

/-!
# Kummer theory lemmas
-/

noncomputable theory
open_locale classical number_field

universe u

variables {K : Type u} [field K]

----------------------------------------------------------------------------------------------------
/-! ## The subgroup `K(S, n)` -/

section K_S_n

private def with_zero_units {α : Type u} [group α] : (with_zero α)ˣ ≃* α :=
{ to_fun    := λ x, (with_zero.ne_zero_iff_exists.mp x.ne_zero).some,
  inv_fun   := λ x,
  ⟨_, _, mul_inv_cancel $ @with_zero.coe_ne_zero _ x, inv_mul_cancel $ @with_zero.coe_ne_zero _ x⟩,
  left_inv  := λ x,
  by simp only [(with_zero.ne_zero_iff_exists.mp x.ne_zero).some_spec, units.mk_coe],
  right_inv := λ x,
  by { rw [← with_zero.coe_inj,
           (with_zero.ne_zero_iff_exists.mp (_ : (with_zero α)ˣ).ne_zero).some_spec],
       refl },
  map_mul'  := λ x y,
  by { rw [← with_zero.coe_inj, with_zero.coe_mul,
           (with_zero.ne_zero_iff_exists.mp (x * y).ne_zero).some_spec,
           (with_zero.ne_zero_iff_exists.mp x.ne_zero).some_spec,
           (with_zero.ne_zero_iff_exists.mp y.ne_zero).some_spec],
       refl } }

/-- The primes of a number field. -/
@[nolint has_inhabited_instance] def primes (K : Type u) [field K] [number_field K] : Type u :=
maximal_spectrum $ 𝓞 K

variables [number_field K] {S S' : finset $ primes K} {n : ℕ}

/-- The multiplicative valuation of a unit. -/
def val_of_unit (p : primes K) : Kˣ →* multiplicative ℤ :=
with_zero_units.to_monoid_hom.comp $ units.map $ @maximal_spectrum.valuation _ _ _ _ K _ _ _ p

local notation n`⬝`K := (zpow_group_hom n : Kˣ →* Kˣ).range

/-- The multiplicative valuation of a unit modulo `n`-th powers. -/
def val_of_unit_mod (p : primes K) : Kˣ ⧸ (n⬝K) →* multiplicative (zmod n) :=
(int.quotient_zmultiples_nat_equiv_zmod n).to_multiplicative.to_monoid_hom.comp $
  quotient_group.map (n⬝K) (add_subgroup.zmultiples (n : ℤ)).to_subgroup (val_of_unit p) $
begin
  rintro x ⟨y, hy⟩,
  rw [← hy],
  exact ⟨val_of_unit p y, by { rw [zpow_group_hom_apply, map_zpow, int.to_add_zpow], refl }⟩
end

/-- The subgroup `K(S, n) = {b(Kˣ)ⁿ ∈ Kˣ/(Kˣ)ⁿ | ∀ p ∉ S, ord_p(b) ≡ 0 mod n}`. -/
def K_S_n : subgroup (Kˣ ⧸ (n⬝K)) :=
{ carrier  := {b : Kˣ ⧸ (n⬝K) | ∀ p ∉ S, val_of_unit_mod p b = 1},
  one_mem' := λ p _, by rw [map_one],
  mul_mem' := λ _ _ hx hy p hp, by rw [map_mul, hx p hp, hy p hp, one_mul],
  inv_mem' := λ _ hx p hp, by rw [map_inv, hx p hp, one_inv] }

notation K⟮S, n⟯ := @K_S_n K _ _ S n

lemma K_S_n.one_mem : (1 : Kˣ ⧸ (n⬝K)) ∈ K⟮S, n⟯ := K_S_n.one_mem'

lemma K_S_n.mul_mem {x y : Kˣ ⧸ (n⬝K)} (hx : x ∈ K⟮S, n⟯) (hy : y ∈ K⟮S, n⟯) : x * y ∈ K⟮S, n⟯ :=
K_S_n.mul_mem' hx hy

lemma K_S_n.inv_mem {x : Kˣ ⧸ (n⬝K)} (hx : x ∈ K⟮S, n⟯) : x⁻¹ ∈ K⟮S, n⟯ := K_S_n.inv_mem' hx

lemma K_S_n.monotone (hS : S' ⊆ S) : K⟮S', n⟯ ≤ K⟮S, n⟯ := λ _ hb p hp, hb p $ mt (@hS p) hp

/-- The multiplicative valuation on K_S_n. -/
def K_S_n.val : K⟮S, n⟯ →* S → multiplicative (zmod n) :=
{ to_fun   := λ b p, val_of_unit_mod (p : primes K) (b : Kˣ ⧸ (n⬝K)),
  map_one' := funext $ λ p, map_one $ val_of_unit_mod p,
  map_mul' := λ x y, funext $ λ p, map_mul (val_of_unit_mod p) x y }

@[simp] lemma K_S_n.val.map_one : K_S_n.val (1 : K⟮S, n⟯) = 1 := K_S_n.val.map_one'

@[simp] lemma K_S_n.val.map_mul (x y : K⟮S, n⟯) : K_S_n.val (x * y) = K_S_n.val x * K_S_n.val y :=
K_S_n.val.map_mul' x y

lemma K_S_n.val_ker : K_S_n.val.ker = K⟮∅, n⟯.subgroup_of K⟮S, n⟯ :=
begin
  ext ⟨x, hx⟩,
  split,
  { intros hx' p _,
    by_cases hp : p ∈ S,
    { exact congr_fun hx' ⟨p, hp⟩ },
    { exact hx p hp } },
  { exact λ hx', funext $ λ p, hx' p $ finset.not_mem_empty p }
end

/-- A group homomorphism `K(∅, n) → Cl(K)`. -/
def K_0_n.to_class : K⟮∅, n⟯ →* class_group (𝓞 K) K := sorry

/-- A group homomorphism `𝓞ˣ → K(S, n)`. -/
def K_0_n.from_unit : (𝓞 K)ˣ →* K⟮∅, n⟯ := sorry

lemma K_0_n.to_class_ker : (K_0_n.to_class.ker : subgroup K⟮∅, n⟯) = K_0_n.from_unit.range := sorry

local notation n`⬝𝓞`K := (zpow_group_hom n : (𝓞 K)ˣ →* (𝓞 K)ˣ).range

lemma K_0_n.from_unit_ker : (@K_0_n.from_unit K _ _ n).ker = (n⬝𝓞K) := sorry

-- Input : finite generation of unit group or Dirichlet's unit theorem
/-- `𝓞ˣ/(𝓞ˣ)ⁿ` is finite. -/
instance : fintype $ (𝓞 K)ˣ ⧸ (n⬝𝓞K) := sorry

/-- `K(∅, n)` is finite. -/
def K_0_n.fintype : fintype K⟮∅, n⟯ := group.fintype_of_ker_codom
begin
  rw [K_0_n.to_class_ker],
  apply fintype.of_equiv _ (quotient_group.quotient_ker_equiv_range K_0_n.from_unit).to_equiv,
  rw [K_0_n.from_unit_ker],
  exact has_quotient.quotient.fintype
end $ number_field.ring_of_integers.class_group.fintype K

variables [fact (0 < n)]

/-- `K(S, n)` is finite. -/
instance : fintype K⟮S, n⟯ := group.fintype_of_ker_codom
begin
  rw [@K_S_n.val_ker K _ _ S n],
  exact @fintype.of_equiv _ K⟮∅, n⟯ K_0_n.fintype
    (subgroup.comap_subtype_equiv_of_le $ K_S_n.monotone $ finset.empty_subset S).symm.to_equiv
end $ by exact pi.fintype

notation K⟮S, n⟯`²` := (K⟮S, n⟯.prod K⟮S, n⟯).to_add_subgroup

/-- `K(S, n) × K(S, n)` is finite. -/
instance : fintype K⟮S, n⟯² := fintype.of_equiv _ (subgroup.prod_equiv K⟮S, n⟯ K⟮S, n⟯).symm.to_equiv

end K_S_n

----------------------------------------------------------------------------------------------------
