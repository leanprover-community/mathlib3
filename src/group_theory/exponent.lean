/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import group_theory.order_of_element
import algebra.punit_instances
import algebra.gcd_monoid.finset
import ring_theory.int.basic

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G` it is equal to
the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `monoid.exponent_exists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `add_monoid.exponent_exists` the additive version of `monoid.exponent_exists`.
* `add_monoid.exponent` the additive version of `monoid.exponent`.

## Main results

* `lcm_order_eq_exponent`: For a finite group `G`, the exponent is equal to the `lcm` of the order
  of its elements.

## TODO
* Compute the exponent of cyclic groups.
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/

universe u

variables (G : Type u) [monoid G]

open_locale classical

namespace monoid

/--A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
  for all `g`.-/
@[to_additive "A predicate on an additive monoid saying that there is a positive integer `n` such
  that `n • g = 0` for all `g`."]
def exponent_exists  := ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1

/--The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
  `g ∈ G` if it exists, otherwise it is zero by convention.-/
@[to_additive "The exponent of an additive group is the smallest positive integer `n` such that
  `n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention."]
noncomputable def exponent :=
if h : exponent_exists G then nat.find h else 0

@[to_additive exponent_nsmul_eq_zero]
lemma pow_exponent_eq_one (g : G) : g ^ exponent G = 1 :=
begin
  by_cases exponent_exists G,
  { simp_rw [exponent, dif_pos h],
    exact (nat.find_spec h).2 g},
  { simp_rw [exponent, dif_neg h, pow_zero] }
end

@[to_additive nsmul_eq_mod_exponent]
lemma pow_eq_mod_exponent {n : ℕ} (g : G): g ^ n = g ^ (n % exponent G) :=
calc g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) : by rw [nat.mod_add_div]
  ... = g ^ (n % exponent G) : by simp [pow_add, pow_mul, pow_exponent_eq_one]

@[to_additive]
lemma exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
  0 < exponent G :=
begin
  have h : ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1 := ⟨n, hpos, hG⟩,
  rw [exponent, dif_pos],
  exact (nat.find_spec h).1,
end

@[to_additive]
lemma exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
  exponent G ≤ n :=
begin
  rw [exponent, dif_pos],
  { apply nat.find_min',
    exact ⟨hpos, hG⟩ },
  { exact ⟨n, hpos, hG⟩ },
end

@[to_additive]
lemma exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, g ^ m ≠ 1 :=
begin
  by_contradiction,
  push_neg at h,
  have hcon : exponent G ≤ m := exponent_min' G m hpos h,
  linarith,
end

@[simp, to_additive]
lemma exp_eq_one_of_subsingleton [subsingleton G] : exponent G = 1 :=
begin
  apply le_antisymm,
  { apply exponent_min' _ _ nat.one_pos,
    simp },
  { apply nat.succ_le_of_lt,
    apply exponent_pos_of_exists _ 1 (nat.one_pos),
    simp },
end

@[to_additive add_order_dvd_exponent]
lemma order_dvd_exponent (g : G) : (order_of g) ∣ exponent G :=
order_of_dvd_of_pow_eq_one (pow_exponent_eq_one G g)

@[to_additive]
lemma exponent_dvd_of_forall_pow_eq_one (n : ℕ) (hG : ∀ g : G, g ^ n = 1) :
  exponent G ∣ n :=
begin
  by_cases hpos : n = 0, { simp [hpos], },
  apply nat.dvd_of_mod_eq_zero,
  by_contradiction h,
  have h₁ := nat.pos_of_ne_zero h,
  have h₂ : n % exponent G < exponent G :=
    nat.mod_lt _ (exponent_pos_of_exists _ n (nat.pos_of_ne_zero hpos) hG),
  have h₃ : exponent G ≤ n % exponent G,
  { apply exponent_min' _ _ h₁,
    simp_rw ←pow_eq_mod_exponent,
    exact hG },
  linarith,
end

variable [fintype G]

@[to_additive lcm_add_order_of_dvd_exponent]
lemma lcm_order_of_dvd_exponent : (finset.univ : finset G).lcm order_of ∣ exponent G :=
begin
  apply finset.lcm_dvd,
  intros g hg,
  exact order_dvd_exponent G g
end

@[to_additive lcm_add_order_eq_exponent]
lemma lcm_order_eq_exponent {H : Type u} [fintype H] [left_cancel_monoid H] :
  (finset.univ : finset H).lcm order_of = exponent H :=
begin
  apply nat.dvd_antisymm (lcm_order_of_dvd_exponent H),
  apply exponent_dvd_of_forall_pow_eq_one,
  intro g,
  have h : (order_of g) ∣ (finset.univ : finset H).lcm order_of,
  { apply finset.dvd_lcm,
    exact finset.mem_univ g },
  cases h with m hm,
  rw [hm, pow_mul, pow_order_of_eq_one, one_pow]
end

end monoid
