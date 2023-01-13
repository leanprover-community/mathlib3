/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.padic_int_clopen_properties
import number_theory.L_functions

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
* change `E_c` to `(algebra_map ℚ ℚ_[p])`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables (p : ℕ) [fact p.prime] (d : ℕ)
variables (R : Type*) [normed_comm_ring R] (m : ℕ)

open locally_constant zmod nat

/-- Extending the primitive Dirichlet character χ with level (d* p^m) ; We use the composition
  of χ with the Chinese remainder and `to_zmod_pow` -/
noncomputable abbreviation dirichlet_char_extend (hd : d.coprime p)
  (χ : (zmod (d*(p^m)))ˣ →* Rˣ) : ((zmod d)ˣ × ℤ_[p]ˣ) →* Rˣ :=
χ.comp (((units.map (zmod.chinese_remainder
(coprime.pow_right m hd)).symm.to_monoid_hom).comp (mul_equiv.to_monoid_hom
(mul_equiv.symm mul_equiv.prod_units))).comp (monoid_hom.prod_map (monoid_hom.id (units (zmod d)))
(units.map (padic_int.to_zmod_pow m).to_monoid_hom)))
-- build API?

open padic_int
variables (c : ℕ)

/-- A Bernoulli measure, as defined by Washington. -/
noncomputable def E_c := λ (n : ℕ) (a : (zmod (d * (p^n)))), (algebra_map ℚ ℚ_[p])
  (int.fract ((a.val : ℚ) / (d*p^n)) -
  c * int.fract (((((((c : zmod (d * p^(2 * n)))⁻¹).val : ℚ) * (a : ℚ))) : ℚ) / (d * p^n)) +
  (c - 1)/2)

variables [algebra ℚ_[p] R] {c}

open clopen_from

/-- The set of Bernoulli measures. -/
def bernoulli_measure := {x : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R |
   ∀ (n : ℕ) (a : zmod (d * (p^n))), x (char_fn R (is_clopen a)) =
   (algebra_map ℚ_[p] R) (E_c p d c n a)}

/-- A sequence has the `is_eventually_constant` predicate if all the elements of the sequence
  are eventually the same. -/
def is_eventually_constant {α : Type*} (a : ℕ → α) : Prop :=
 { n | ∀ m, n ≤ m → a (nat.succ m) = a m }.nonempty

/-- An eventually constant sequence is a sequence which has the `is_eventually_constant`
  predicate. -/
structure eventually_constant_seq {α : Type*} :=
(to_seq : ℕ → α)
(is_eventually_const : is_eventually_constant to_seq)

namespace eventually_constant_seq

/-- The smallest number `m` for the sequence `a` such that `a n = a (n + 1)` for all `n ≥ m`. -/
noncomputable def sequence_limit_index' {α : Type*} (a : @eventually_constant_seq α) : ℕ :=
Inf { n | ∀ m, n ≤ m → a.to_seq m.succ = a.to_seq m }

/-- The smallest number `m` for the sequence `a` such that `a n = a m` for all `n ≥ m`. -/
noncomputable def sequence_limit_index {α : Type*} (a : ℕ → α) : ℕ :=
Inf { n | ∀ m, n ≤ m → a n = a m }

/-- The limit of an `eventually_constant_seq`. -/
noncomputable def sequence_limit {α : Type*} (a : @eventually_constant_seq α) :=
a.to_seq (sequence_limit_index' a)

lemma sequence_limit_eq {α : Type*} (a : @eventually_constant_seq α) (m : ℕ)
  (hm : sequence_limit_index' a ≤ m) : sequence_limit a = a.to_seq m :=
begin
  rw sequence_limit,
  induction m with d hd,
  { rw nat.le_zero_iff at hm, rw hm, },
  { have := nat.of_le_succ hm,
    cases this,
    { rw hd this,
      refine (nat.Inf_mem a.is_eventually_const d _).symm,
      exact this, },
    { rw this, }, },
end

end eventually_constant_seq
