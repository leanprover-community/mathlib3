/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import group_theory.order_of_element
import algebra.punit_instances
import algebra.gcd_monoid.finset
import tactic.by_contra
import number_theory.padics.padic_norm

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G`,
it is equal to the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `monoid.exponent_exists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `add_monoid.exponent_exists` the additive version of `monoid.exponent_exists`.
* `add_monoid.exponent` the additive version of `monoid.exponent`.

## Main results

* `monoid.lcm_order_eq_exponent`: For a finite left cancel monoid `G`, the exponent is equal to the
  `finset.lcm` of the order of its elements.
* `monoid.exponent_eq_Sup_order_of`: For a finite commutative cancel monoid, the exponent is
  equal to the supremum of the order of its elements.

## TODO
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
* `monoid.exponent_eq_Sup_order_of` can be generalised to infinite groups.
-/

universe u

variable {G : Type u}

open_locale classical

namespace monoid

section monoid

variables (G) [monoid G]

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

variable {G}

@[to_additive]
lemma exponent_eq_zero_iff : exponent G = 0 ↔ ¬ exponent_exists G :=
begin
  rw [exponent],
  split_ifs,
  { simp [h, @not_lt_zero' ℕ] }, --if this isn't done this way, `to_additive` freaks
  { tauto }
end

@[to_additive]
lemma exponent_eq_zero_of_order_zero {g : G} (hg : order_of g = 0) : exponent G = 0 :=
exponent_eq_zero_iff.mpr $ λ ⟨n, hn, hgn⟩, order_of_eq_zero_iff'.mp hg n hn $ hgn g

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
  by_contra' h,
  have hcon : exponent G ≤ m := exponent_min' m hpos h,
  linarith,
end

@[simp, to_additive]
lemma exp_eq_one_of_subsingleton [subsingleton G] : exponent G = 1 :=
begin
  apply le_antisymm,
  { apply exponent_min' _ nat.one_pos,
    simp },
  { apply nat.succ_le_of_lt,
    apply exponent_pos_of_exists 1 (nat.one_pos),
    simp },
end

@[to_additive add_order_dvd_exponent]
lemma order_dvd_exponent (g : G) : (order_of g) ∣ exponent G :=
order_of_dvd_of_pow_eq_one $ pow_exponent_eq_one g

variable (G)

@[to_additive exponent_dvd_of_forall_nsmul_eq_zero]
lemma exponent_dvd_of_forall_pow_eq_one (G) [monoid G] (n : ℕ) (hpos : 0 < n)
  (hG : ∀ g : G, g ^ n = 1) : exponent G ∣ n :=
begin
  apply nat.dvd_of_mod_eq_zero,
  by_contradiction h,
  have h₁ := nat.pos_of_ne_zero h,
  have h₂ : n % exponent G < exponent G := nat.mod_lt _ (exponent_pos_of_exists n hpos hG),
  have h₃ : exponent G ≤ n % exponent G,
  { apply exponent_min' _ h₁,
    simp_rw ←pow_eq_mod_exponent,
    exact hG },
  linarith,
end

@[to_additive lcm_add_order_of_dvd_exponent]
lemma lcm_order_of_dvd_exponent [fintype G] : (finset.univ : finset G).lcm order_of ∣ exponent G :=
begin
  apply finset.lcm_dvd,
  intros g hg,
  exact order_dvd_exponent g
end

@[to_additive]
lemma exists_max_prime_pow_dvd_exponent {p : ℕ} (hp : p.prime) :
  ∃ g : G, order_of g = p ^ padic_val_nat p (exponent G) :=
begin
  haveI := fact.mk hp,
  rcases (padic_val_nat p $ exponent G).eq_zero_or_pos with h | h,
  { refine ⟨1, by rw [h, pow_zero, order_of_one]⟩ },
  have he : 0 < exponent G := ne.bot_lt (λ t, by {rw t at h, exact h.ne' (padic_val_nat_zero _) }),
  have := nat.div_pos (nat.le_of_dvd he $ dvd_of_one_le_padic_val_nat h) hp.pos,
  obtain ⟨g, hg⟩ : ∃ (g : G), g ^ (exponent G / p) ≠ 1,
  { suffices key : ¬ exponent G ∣ exponent G / p,
    { by simpa using mt (exponent_dvd_of_forall_pow_eq_one G (exponent G / p) this) key },
    exact λ hd, hp.one_lt.not_le ((mul_le_iff_le_one_left he).mp $
                nat.le_of_dvd he $ nat.mul_dvd_of_dvd_div (dvd_of_one_le_padic_val_nat h) hd) },
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := pow_padic_val_nat_dvd; try {apply_instance},
  obtain ⟨t, ht⟩ := nat.exists_eq_succ_of_ne_zero h.ne',
  refine ⟨g ^ k, _⟩,
  rw ht,
  apply order_of_eq_prime_pow,
  { rwa [hk, mul_comm, ht, pow_succ', ←mul_assoc, nat.mul_div_cancel _ hp.pos, pow_mul] at hg },
  { rw [←nat.succ_eq_add_one, ←ht, ←pow_mul, mul_comm, ←hk],
    exact pow_exponent_eq_one g },
end

end monoid

section left_cancel_monoid

variable [left_cancel_monoid G]

@[to_additive lcm_add_order_eq_exponent]
lemma lcm_order_eq_exponent [fintype G] : (finset.univ : finset G).lcm order_of = exponent G :=
begin
  apply nat.dvd_antisymm (lcm_order_of_dvd_exponent G),
  apply exponent_dvd_of_forall_pow_eq_one,
  { apply nat.pos_of_ne_zero,
    by_contradiction,
    rw finset.lcm_eq_zero_iff at h,
    cases h with g hg,
    simp only [true_and, set.mem_univ, finset.coe_univ] at hg,
    exact ne_of_gt (order_of_pos g) hg },
  { intro g,
    have h : (order_of g) ∣ (finset.univ : finset G).lcm order_of,
    { apply finset.dvd_lcm,
      exact finset.mem_univ g },
    cases h with m hm,
    rw [hm, pow_mul, pow_order_of_eq_one, one_pow] },
end

@[to_additive]
lemma exponent_ne_zero_of_fintype [fintype G] : exponent G ≠ 0 :=
by simpa [←lcm_order_eq_exponent, finset.lcm_eq_zero_iff] using λ x, (order_of_pos x).ne'

end left_cancel_monoid

section comm_monoid

variable [cancel_comm_monoid G]

@[to_additive] lemma exponent_eq_Sup_order_of (h : ∀ g : G, 0 < order_of g) :
  exponent G = Sup (set.range (order_of : G → ℕ)) :=
begin
  rcases eq_or_ne (exponent G) 0 with he | he,
  { rw [he, set.infinite.nat.Sup_eq_zero],
    contrapose! he,
    replace he := not_not.mp he,
    lift (set.range order_of) to finset ℕ using he with t ht,
    have htpos : 0 < t.prod id,
    { apply finset.prod_pos,
      intros a ha,
      rw [←finset.mem_coe, ht] at ha,
      obtain ⟨k, hk⟩ := ha,
      exact hk ▸ (h _) },
    suffices : exponent G ∣ t.prod id,
    { intro h,
      rw [h, zero_dvd_iff] at this,
      exact htpos.ne' this },
    refine exponent_dvd_of_forall_pow_eq_one _ _ htpos (λ g, _),
    rw pow_eq_mod_order_of,
    convert pow_zero g,
    apply nat.mod_eq_zero_of_dvd,
    apply finset.dvd_prod_of_mem,
    rw [←finset.mem_coe, ht],
    exact set.mem_range_self _ },
  have hne : (set.range (order_of : G → ℕ)).nonempty := ⟨1, by simp⟩,
  have hfin : (set.range (order_of : G → ℕ)).finite,
  { by_contra h,
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := set.infinite.exists_nat_lt h (exponent G),
    apply pow_ne_one_of_lt_order_of' he het,
    exact pow_exponent_eq_one t },
  have := hne.cSup_mem hfin,
  obtain ⟨t, ht⟩ := this,
  symmetry,
  apply nat.dvd_antisymm,
  { rw ←ht,
    apply order_dvd_exponent },
  refine nat.dvd_of_factors_subperm he _,
  rw list.subperm_ext_iff,
  by_contra' h,
  obtain ⟨p, hp, hpe⟩ := h,
  haveI hp := fact.mk (nat.prime_of_mem_factors hp),
  simp only [←padic_val_nat_eq_factors_count p] at hpe,
  set k := padic_val_nat p (order_of t) with hk,
  obtain ⟨g, hg⟩ := exists_max_prime_pow_dvd_exponent G hp.1,
  suffices : order_of t < order_of (t ^ (p ^ k) * g),
  { rw ht at this,
    exact this.not_le (le_cSup hfin.bdd_above $ by simp) },
  have hpk  : p ^ k ∣ order_of t := pow_padic_val_nat_dvd,
  have hpk' : order_of (t ^ p ^ k) = order_of t / p ^ k,
  { rw [order_of_pow' t (pow_ne_zero k hp.1.ne_zero), nat.gcd_eq_right hpk] },
  obtain ⟨a, ha⟩ := nat.exists_eq_add_of_lt hpe,
  have hcoprime : (order_of (t ^ p ^ k)).coprime (order_of g),
  { rw [hg, nat.coprime_pow_right_iff, nat.coprime_comm],
    apply or.resolve_right (nat.coprime_or_dvd_of_prime hp.1 _),
    nth_rewrite 0 ←pow_one p,
    convert pow_succ_padic_val_nat_not_dvd (h $ t ^ p ^ k),
    rw [hpk', padic_val_nat.div_pow hpk, hk, nat.sub_self],
    { apply_instance },
    rw ha,
    exact nat.succ_pos _ },
  rw [(commute.all _ g).order_of_mul_eq_mul_order_of_of_coprime hcoprime,
      hpk', hg, ha, ←ht, ←hk, pow_add, pow_add, pow_one],
  convert_to order_of t < (order_of t / p ^ k * p ^ k) * p ^ a * p, ac_refl,
  rw [nat.div_mul_cancel hpk, mul_assoc, lt_mul_iff_one_lt_right $ h t, ←pow_succ'],
  exact one_lt_pow hp.1.one_lt a.succ_ne_zero
end

@[to_additive]
lemma exponent_eq_max'_order_of [fintype G] :
  exponent G = ((@finset.univ G _).image order_of).max' ⟨1, by simp⟩ :=
begin
  rw [←finset.nonempty.cSup_eq_max', finset.coe_image, finset.coe_univ, set.image_univ],
  exact exponent_eq_Sup_order_of order_of_pos
end

end comm_monoid

end monoid
