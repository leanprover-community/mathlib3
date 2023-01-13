/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import ring_theory.witt_vector.teichmuller
import ring_theory.witt_vector.compare
import number_theory.padic_int_properties
import number_theory.dirichlet_character_properties
--import data.nat.modeq
--import topology.discrete_quotient
--import data.set.prod
--import algebra.order.sub
--import algebra.pointwise
--import data.real.basic
--import topology.algebra.continuous_monoid_hom

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure`

## Implementation notes
Removed `weight_space` since `continuous_monoid_hom` now exists. Fixing the convention to be
  `d.coprime p` instead of `d.gcd p = 1`.

## TODO
* Separate into different files : `padic_int_properties`, `zmod_properties`,
  `dirichlet_char_properties`, and `teich_char_properties`
* Delete `pri_dir_char_extend'` and replace with `dirichlet_char_extend`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

variables (p : ℕ) [fact p.prime]

/-- The Teichmuller character defined on `p`-adic units in terms of Witt vectors. -/
noncomputable abbreviation teichmuller_character : ℤ_[p]ˣ →* ℤ_[p] :=
(witt_vector.equiv p).to_monoid_hom.comp ((witt_vector.teichmuller p).comp
  ((padic_int.to_zmod).to_monoid_hom.comp (units.coe_hom (ℤ_[p]))))
-- is this just taking (a : ℤ_[p]) to (to_zmod a : ℤ_[p])?

variable {p}
lemma teichmuller_character_root_of_unity (a : units ℤ_[p]) :
  (teichmuller_character p a)^(p - 1) = 1 :=
begin
  rw [←monoid_hom.map_pow],
  simp only [monoid_hom.coe_comp, ring_hom.to_monoid_hom_eq_coe, ring_hom.coe_monoid_hom,
    function.comp_app, units.coe_hom_apply, units.coe_pow, ring_hom.map_pow,
    padic_int.unit_pow_eq_one a, monoid_hom.map_one],
end

/-- The Teichmuller character defined on 𝔽ₚ*. -/
noncomputable abbreviation teichmuller_character_mod_p (p : ℕ) [fact (nat.prime p)] :
  dirichlet_character ℤ_[p] p :=
units.map (((witt_vector.equiv p).to_monoid_hom).comp (witt_vector.teichmuller p))

namespace units
lemma map_injective {M N : Type*} [monoid M] [monoid N] (f : M →* N)
  (hf : function.injective f) : function.injective (units.map f) :=
λ a b h, units.eq_iff.1 (hf (units.eq_iff.2 h))
end units

lemma teichmuller_character_mod_p_injective (p : ℕ) [fact (nat.prime p)] :
  function.injective (teichmuller_character_mod_p p) :=
begin
  change function.injective (function.comp (units.map (witt_vector.equiv p).to_monoid_hom)
    (units.map (@witt_vector.teichmuller p (zmod p) _ _))),
  refine function.injective.comp (units.map_injective _
    (equiv.injective (witt_vector.equiv p).to_equiv))
    (units.map_injective _ (λ a b h, witt_vector.ext_iff.1 h 0)),
end

namespace teichmuller_character
lemma is_odd_or_is_even : ((teichmuller_character p)) (-1 : units (ℤ_[p])) = -1 ∨
  ((teichmuller_character p)) (-1 : units (ℤ_[p])) = 1 :=
begin
  suffices : ((teichmuller_character p) (-1))^2 = 1,
  { conv_rhs at this { rw ←one_pow 2 },
    rw [←sub_eq_zero, sq_sub_sq, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this,
    apply this, },
  { rw [←monoid_hom.map_pow, ←monoid_hom.map_one (teichmuller_character p), neg_one_sq], },
end

open dirichlet_character
lemma eval_neg_one (hp : 2 < p) : (teichmuller_character_mod_p p (-1)) = -1 :=
begin
  cases dirichlet_character.is_odd_or_is_even (teichmuller_character_mod_p p),
  { exact h, },
  { rw [is_even, ←monoid_hom.map_one (teichmuller_character_mod_p p)] at h,
    have := teichmuller_character_mod_p_injective p h,
    rw [eq_comm, ←units.eq_iff, units.coe_one, units.coe_neg_one, eq_neg_iff_add_eq_zero,
      ←nat.cast_one, ←nat.cast_add, zmod.nat_coe_zmod_eq_zero_iff_dvd,
      nat.dvd_prime (nat.prime_two)] at this,
    exfalso, cases this,
    { apply nat.prime.ne_one (fact.out _) this, },
    { apply ne_of_lt hp this.symm, }, },
end
end teichmuller_character

variables {R : Type*} [normed_comm_ring R] {m : ℕ}
variables (p R)
/-- Returns ω⁻¹ : ℤ/pℤ* →* R*. -/
noncomputable abbreviation teichmuller_character_mod_p' [algebra ℚ_[p] R] :
  dirichlet_character R p :=
((units.map ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)).to_monoid_hom).comp
(teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹

instance char_zero_of_nontrivial_of_normed_algebra [nontrivial R] [algebra ℚ_[p] R] :
  char_zero R :=
(ring_hom.char_zero_iff ((algebra_map ℚ_[p] R).injective)).1 infer_instance

variables {p R}
lemma change_level_eval_neg_one' [no_zero_divisors R] [algebra ℚ_[p] R] [nontrivial R]
  (hp : 2 < p) : (teichmuller_character_mod_p' p R) (-1 : (zmod p)ˣ) = (-1 : units R) :=
begin
  cases dirichlet_character.is_odd_or_is_even (teichmuller_character_mod_p' p R),
  { exact h, },
  { exfalso,
    suffices : ((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
      (teichmuller_character_mod_p p)⁻¹) (-1) = 1,
    { simp only [monoid_hom.comp_apply, monoid_hom.inv_apply, map_inv, inv_eq_one] at this,
      rw [teichmuller_character.eval_neg_one hp, ←units.eq_iff, units.coe_map] at this,
      simp only [ring_hom.to_monoid_hom_eq_coe, units.coe_neg_one, ring_hom.coe_monoid_hom,
        map_neg, map_one, units.coe_one] at this,
      apply @nat.cast_add_one_ne_zero R _ _ _ 1,
      rw [←eq_neg_iff_add_eq_zero, nat.cast_one, this], },
    { convert h, }, },
end
-- maybe can be simplified

lemma change_level_pow_eval_neg_one' [algebra ℚ_[p] R] [nontrivial R] [no_zero_divisors R] (k : ℕ)
  (hp : 2 < p) : ((teichmuller_character_mod_p' p R ^ k) is_unit_one.neg.unit) = (-1) ^ k :=
begin
  have : (is_unit_one.neg.unit : (zmod p)ˣ) = -1,
  { rw [←units.eq_iff, is_unit.unit_spec, units.coe_neg_one], },
  rw [dirichlet_character.pow_apply, this, change_level_eval_neg_one' hp],
  any_goals { apply_instance, },
end
