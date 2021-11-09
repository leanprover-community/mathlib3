/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import group_theory.order_of_element
import algebra.punit_instances
import algebra.gcd_monoid.finset

/-!
# Exponent of a group

This file defines the exponent of a group. For a group `G` it is defined to be the minimal `n≥1`
such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G` it is equal to the lowest common
multiple of the order of all elements of the group `G`.

## Main definitions

* `exponent_exists` is a predicate on a monoid `G` saying that there is some positive `n` such that
  `g ^ n = 1` for all `g ∈ G`.
* `exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that `g ^ n = 1`
  for all `g ∈ G`, by convention it is `0` if no such `n` exists.

## TODO
* Show that for a finite group `G`, the exponent is equal to the lcm of the orders of its elements.
* Provide additive versions of all notions.
* Compute the exponent of cyclic groups.
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/

universe u

variables (G : Type u) [monoid G]

open_locale classical

def exponent_exists  := ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1

noncomputable def exponent :=
if h : exponent_exists G then nat.find h else 0

lemma pow_exponent_eq_one (g : G) : g ^ exponent G = 1 :=
begin
  by_cases exponent_exists G,
  { simp_rw [exponent, dif_pos h],
    exact (nat.find_spec h).2 g},
  { simp_rw [exponent, dif_neg h, pow_zero] }
end

lemma exponent_pos_of_exists (n : ℕ) (hpos : 0 < n)
(hG : ∀ g : G, g ^ n = 1) : 0 < exponent G :=
begin
  have h : ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1,
      { exact ⟨n, hpos, hG⟩ },
  rw [exponent, dif_pos],
  exact (nat.find_spec h).1,
end

lemma exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
  exponent G ≤ n :=
begin
  rw [exponent, dif_pos],
  { apply nat.find_min',
    exact ⟨hpos, hG⟩ },
  { exact ⟨n, hpos, hG⟩ },
end

lemma exp_punit_eq_one : exponent punit = 1 :=
begin
  apply le_antisymm,
  { apply exponent_min' _ _ nat.one_pos,
    intro g,
    refl },
  { apply nat.succ_le_of_lt,
    apply exponent_pos_of_exists _ 1 (nat.one_pos),
    intro g,
    refl },
end

lemma order_dvd_exponent (g : G) : (order_of g) ∣ exponent G :=
by exact order_of_dvd_of_pow_eq_one (pow_exponent_eq_one G g)
