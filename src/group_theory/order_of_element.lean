/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
import data.int.gcd
import algebra.iterate_hom
import algebra.pointwise
import dynamics.periodic_pts
import group_theory.coset

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`x ∈ G` is the minimal `n ≥ 1` such that `x ^ n = 1`.

## Main definitions

* `is_of_fin_order` is a predicate on an element `x` of a monoid `G` saying that `x` is of finite
  order.
* `is_of_fin_add_order` is the additive analogue of `is_of_find_order`.
* `order_of x` defines the order of an element `x` of a monoid `G`, by convention its value is `0`
  if `x` has infinite order.
* `add_order_of` is the additive analogue of `order_of`.

## Tags
order of an element
-/

open function nat
open_locale pointwise

universes u v

variables {G : Type u} {A : Type v}
variables {x y : G} {a b : A} {n m : ℕ}

section monoid_add_monoid

variables [monoid G] [add_monoid A]

section is_of_fin_order

@[to_additive is_periodic_pt_add_iff_nsmul_eq_zero]
lemma is_periodic_pt_mul_iff_pow_eq_one (x : G) : is_periodic_pt ((*) x) n 1 ↔ x ^ n = 1 :=
by rw [is_periodic_pt, is_fixed_pt, mul_left_iterate, mul_one]

/-- `is_of_fin_add_order` is a predicate on an element `a` of an additive monoid to be of finite
order, i.e. there exists `n ≥ 1` such that `n • a = 0`.-/
def is_of_fin_add_order (a : A) : Prop :=
(0 : A) ∈ periodic_pts ((+) a)

/-- `is_of_fin_order` is a predicate on an element `x` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `x ^ n = 1`.-/
@[to_additive is_of_fin_add_order]
def is_of_fin_order (x : G) : Prop :=
(1 : G) ∈ periodic_pts ((*) x)

lemma is_of_fin_add_order_of_mul_iff :
  is_of_fin_add_order (additive.of_mul x) ↔ is_of_fin_order x := iff.rfl

lemma is_of_fin_order_of_add_iff :
  is_of_fin_order (multiplicative.of_add a) ↔ is_of_fin_add_order a := iff.rfl

@[to_additive is_of_fin_add_order_iff_nsmul_eq_zero]
lemma is_of_fin_order_iff_pow_eq_one (x : G) :
  is_of_fin_order x ↔ ∃ n, 0 < n ∧ x ^ n = 1 :=
by { convert iff.rfl, simp [is_periodic_pt_mul_iff_pow_eq_one] }

end is_of_fin_order

/-- `order_of x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `order_of x` is `0` by convention.-/
@[to_additive add_order_of
"`add_order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it
exists. Otherwise, i.e. if `a` is of infinite order, then `add_order_of a` is `0` by convention."]
noncomputable def order_of (x : G) : ℕ :=
minimal_period ((*) x) 1

@[simp] lemma add_order_of_of_mul_eq_order_of (x : G) :
  add_order_of (additive.of_mul x) = order_of x := rfl

@[simp] lemma order_of_of_add_eq_add_order_of (a : A) :
  order_of (multiplicative.of_add a) = add_order_of a := rfl

@[to_additive add_order_of_pos']
lemma order_of_pos' (h : is_of_fin_order x) : 0 < order_of x :=
minimal_period_pos_of_mem_periodic_pts h

@[to_additive add_order_of_nsmul_eq_zero]
lemma pow_order_of_eq_one (x : G) : x ^ order_of x = 1 :=
begin
  convert is_periodic_pt_minimal_period ((*) x) _,
  rw [order_of, mul_left_iterate, mul_one],
end

@[to_additive add_order_of_eq_zero]
lemma order_of_eq_zero (h : ¬ is_of_fin_order x) : order_of x = 0 :=
by rwa [order_of, minimal_period, dif_neg]

@[to_additive add_order_of_eq_zero_iff] lemma order_of_eq_zero_iff :
  order_of x = 0 ↔ ¬ is_of_fin_order x :=
⟨λ h H, (order_of_pos' H).ne' h, order_of_eq_zero⟩

@[to_additive add_order_of_eq_zero_iff'] lemma order_of_eq_zero_iff' :
  order_of x = 0 ↔ ∀ n : ℕ, 0 < n → x ^ n ≠ 1 :=
by simp_rw [order_of_eq_zero_iff, is_of_fin_order_iff_pow_eq_one, not_exists, not_and]

@[to_additive nsmul_ne_zero_of_lt_add_order_of']
lemma pow_ne_one_of_lt_order_of' (n0 : n ≠ 0) (h : n < order_of x) : x ^ n ≠ 1 :=
λ j, not_is_periodic_pt_of_pos_of_lt_minimal_period n0 h
  ((is_periodic_pt_mul_iff_pow_eq_one x).mpr j)

@[to_additive add_order_of_le_of_nsmul_eq_zero]
lemma order_of_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : order_of x ≤ n :=
is_periodic_pt.minimal_period_le hn (by rwa is_periodic_pt_mul_iff_pow_eq_one)

@[simp, to_additive] lemma order_of_one : order_of (1 : G) = 1 :=
by rw [order_of, one_mul_eq_id, minimal_period_id]

@[simp, to_additive add_monoid.order_of_eq_one_iff] lemma order_of_eq_one_iff :
  order_of x = 1 ↔ x = 1 :=
by rw [order_of, is_fixed_point_iff_minimal_period_eq_one, is_fixed_pt, mul_one]

@[to_additive nsmul_eq_mod_add_order_of]
lemma pow_eq_mod_order_of {n : ℕ} : x ^ n = x ^ (n % order_of x) :=
calc x ^ n = x ^ (n % order_of x + order_of x * (n / order_of x)) : by rw [nat.mod_add_div]
       ... = x ^ (n % order_of x) : by simp [pow_add, pow_mul, pow_order_of_eq_one]

@[to_additive add_order_of_dvd_of_nsmul_eq_zero]
lemma order_of_dvd_of_pow_eq_one (h : x ^ n = 1) : order_of x ∣ n :=
is_periodic_pt.minimal_period_dvd ((is_periodic_pt_mul_iff_pow_eq_one _).mpr h)

@[to_additive add_order_of_dvd_iff_nsmul_eq_zero]
lemma order_of_dvd_iff_pow_eq_one {n : ℕ} : order_of x ∣ n ↔ x ^ n = 1 :=
⟨λ h, by rw [pow_eq_mod_order_of, nat.mod_eq_zero_of_dvd h, pow_zero], order_of_dvd_of_pow_eq_one⟩

@[to_additive exists_nsmul_eq_self_of_coprime]
lemma exists_pow_eq_self_of_coprime (h : n.coprime (order_of x)) :
  ∃ m : ℕ, (x ^ n) ^ m = x :=
begin
  by_cases h0 : order_of x = 0,
  { rw [h0, coprime_zero_right] at h,
    exact ⟨1, by rw [h, pow_one, pow_one]⟩ },
  by_cases h1 : order_of x = 1,
  { exact ⟨0, by rw [order_of_eq_one_iff.mp h1, one_pow, one_pow]⟩ },
  obtain ⟨m, hm⟩ :=
    exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩),
  exact ⟨m, by rw [←pow_mul, pow_eq_mod_order_of, hm, pow_one]⟩,
end

/--
If `x^n = 1`, but `x^(n/p) ≠ 1` for all prime factors `p` of `r`,
then `x` has order `n` in `G`.
-/
@[to_additive add_order_of_eq_of_nsmul_and_div_prime_nsmul]
theorem order_of_eq_of_pow_and_pow_div_prime (hn : 0 < n) (hx : x^n = 1)
  (hd : ∀ p : ℕ, p.prime → p ∣ n → x^(n/p) ≠ 1) :
  order_of x = n :=
begin
  -- Let `a` be `n/(order_of x)`, and show `a = 1`
  cases exists_eq_mul_right_of_dvd (order_of_dvd_of_pow_eq_one hx) with a ha,
  suffices : a = 1, by simp [this, ha],
  -- Assume `a` is not one...
  by_contra,
  have a_min_fac_dvd_p_sub_one : a.min_fac ∣ n,
  { obtain ⟨b, hb⟩ : ∃ (b : ℕ), a = b * a.min_fac := exists_eq_mul_left_of_dvd a.min_fac_dvd,
    rw [hb, ←mul_assoc] at ha,
    exact dvd.intro_left (order_of x * b) ha.symm, },
  -- Use the minimum prime factor of `a` as `p`.
  refine hd a.min_fac (nat.min_fac_prime h) a_min_fac_dvd_p_sub_one _,
  rw [←order_of_dvd_iff_pow_eq_one, nat.dvd_div_iff (a_min_fac_dvd_p_sub_one),
      ha, mul_comm, nat.mul_dvd_mul_iff_left (order_of_pos' _)],
  { exact nat.min_fac_dvd a, },
  { rw is_of_fin_order_iff_pow_eq_one,
    exact Exists.intro n (id ⟨hn, hx⟩) },
end

@[to_additive add_order_of_eq_add_order_of_iff]
lemma order_of_eq_order_of_iff {H : Type*} [monoid H] {y : H} :
  order_of x = order_of y ↔ ∀ n : ℕ, x ^ n = 1 ↔ y ^ n = 1 :=
by simp_rw [← is_periodic_pt_mul_iff_pow_eq_one, ← minimal_period_eq_minimal_period_iff, order_of]

@[to_additive add_order_of_injective]
lemma order_of_injective {H : Type*} [monoid H] (f : G →* H)
  (hf : function.injective f) (x : G) : order_of (f x) = order_of x :=
by simp_rw [order_of_eq_order_of_iff, ←f.map_pow, ←f.map_one, hf.eq_iff, iff_self, forall_const]

@[simp, norm_cast, to_additive] lemma order_of_submonoid {H : submonoid G}
  (y : H) : order_of (y : G) = order_of y :=
order_of_injective H.subtype subtype.coe_injective y

@[to_additive order_of_add_units]
lemma order_of_units {y : units G} : order_of (y : G) = order_of y :=
order_of_injective (units.coe_hom G) units.ext y

variables (x)

@[to_additive add_order_of_nsmul']
lemma order_of_pow' (h : n ≠ 0) :
  order_of (x ^ n) = order_of x / gcd (order_of x) n :=
begin
  convert minimal_period_iterate_eq_div_gcd h,
  simp only [order_of, mul_left_iterate],
end

variables (a) (n)

@[to_additive add_order_of_nsmul'']
lemma order_of_pow'' (h : is_of_fin_order x) :
  order_of (x ^ n) = order_of x / gcd (order_of x) n :=
begin
  convert minimal_period_iterate_eq_div_gcd' h,
  simp only [order_of, mul_left_iterate],
end

@[to_additive]
lemma commute.order_of_mul_dvd_lcm {x y : G} (h : commute x y) :
  order_of (x * y) ∣ nat.lcm (order_of x) (order_of y) :=
begin
  convert function.commute.minimal_period_of_comp_dvd_lcm h.function_commute_mul_left,
  rw [order_of, comp_mul_left],
end

@[to_additive add_order_of_add_dvd_mul_add_order_of]
lemma commute.order_of_mul_dvd_mul_order_of {x y : G} (h : commute x y) :
  order_of (x * y) ∣ (order_of x) * (order_of y) :=
dvd_trans h.order_of_mul_dvd_lcm (lcm_dvd_mul _ _)

@[to_additive add_order_of_add_eq_mul_add_order_of_of_coprime]
lemma commute.order_of_mul_eq_mul_order_of_of_coprime {x y : G} (h : commute x y)
  (hco : nat.coprime (order_of x) (order_of y)) :
  order_of (x * y) = (order_of x) * (order_of y) :=
begin
  convert h.function_commute_mul_left.minimal_period_of_comp_eq_mul_of_coprime hco,
  simp only [order_of, comp_mul_left],
end

section p_prime

variables {a x n} {p : ℕ} [hp : fact p.prime]
include hp

@[to_additive add_order_of_eq_prime]
lemma order_of_eq_prime (hg : x ^ p = 1) (hg1 : x ≠ 1) : order_of x = p :=
minimal_period_eq_prime ((is_periodic_pt_mul_iff_pow_eq_one _).mpr hg)
  (by rwa [is_fixed_pt, mul_one])

@[to_additive add_order_of_eq_prime_pow]
lemma order_of_eq_prime_pow (hnot : ¬ x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1) :
  order_of x = p ^ (n + 1) :=
begin
  apply minimal_period_eq_prime_pow;
  rwa is_periodic_pt_mul_iff_pow_eq_one,
end

omit hp
-- An example on how to determine the order of an element of a finite group.
example : order_of (-1 : units ℤ) = 2 :=
begin
  haveI := fact_prime_two,
  exact order_of_eq_prime (int.units_sq _) dec_trivial,
end

end p_prime

end monoid_add_monoid

section cancel_monoid
variables [left_cancel_monoid G] (x y)

@[to_additive nsmul_injective_aux]
lemma pow_injective_aux (h : n ≤ m)
  (hm : m < order_of x) (eq : x ^ n = x ^ m) : n = m :=
by_contradiction $ assume ne : n ≠ m,
  have h₁ : m - n > 0, from nat.pos_of_ne_zero (by simp [tsub_eq_iff_eq_add_of_le h, ne.symm]),
  have h₂ : m = n + (m - n) := (add_tsub_cancel_of_le h).symm,
  have h₃ : x ^ (m - n) = 1,
    by { rw [h₂, pow_add] at eq, apply mul_left_cancel, convert eq.symm, exact mul_one (x ^ n) },
  have le : order_of x ≤ m - n, from order_of_le_of_pow_eq_one h₁ h₃,
  have lt : m - n < order_of x,
    from (tsub_lt_iff_left h).mpr $ nat.lt_add_left _ _ _ hm,
  lt_irrefl _ (le.trans_lt lt)

@[to_additive nsmul_injective_of_lt_add_order_of]
lemma pow_injective_of_lt_order_of
  (hn : n < order_of x) (hm : m < order_of x) (eq : x ^ n = x ^ m) : n = m :=
(le_total n m).elim
  (assume h, pow_injective_aux x h hm eq)
  (assume h, (pow_injective_aux x h hn eq.symm).symm)

@[to_additive mem_multiples_iff_mem_range_add_order_of']
lemma mem_powers_iff_mem_range_order_of' [decidable_eq G] (hx : 0 < order_of x) :
  y ∈ submonoid.powers x ↔ y ∈ (finset.range (order_of x)).image ((^) x : ℕ → G) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' hx (λ i, pow_eq_mod_order_of.symm)

end cancel_monoid

section group
variables [group G] [add_group A] {x a} {i : ℤ}

@[to_additive add_order_of_dvd_iff_zsmul_eq_zero]
lemma order_of_dvd_iff_zpow_eq_one : (order_of x : ℤ) ∣ i ↔ x ^ i = 1 :=
begin
  rcases int.eq_coe_or_neg i with ⟨i, rfl|rfl⟩,
  { rw [int.coe_nat_dvd, order_of_dvd_iff_pow_eq_one, zpow_coe_nat] },
  { rw [dvd_neg, int.coe_nat_dvd, zpow_neg, inv_eq_one, zpow_coe_nat,
      order_of_dvd_iff_pow_eq_one] }
end

@[simp, norm_cast, to_additive] lemma order_of_subgroup {H : subgroup G}
  (y: H) : order_of (y : G) = order_of y :=
order_of_injective H.subtype subtype.coe_injective y

@[to_additive zsmul_eq_mod_add_order_of]
lemma zpow_eq_mod_order_of : x ^ i = x ^ (i % order_of x) :=
calc x ^ i = x ^ (i % order_of x + order_of x * (i / order_of x)) :
    by rw [int.mod_add_div]
       ... = x ^ (i % order_of x) :
    by simp [zpow_add, zpow_mul, pow_order_of_eq_one]
    set_option pp.all true

@[to_additive nsmul_inj_iff_of_add_order_of_eq_zero]
lemma pow_inj_iff_of_order_of_eq_zero (h : order_of x = 0) {n m : ℕ} :
  x ^ n = x ^ m ↔ n = m :=
begin
  rw [order_of_eq_zero_iff, is_of_fin_order_iff_pow_eq_one] at h,
  push_neg at h,
  induction n with n IH generalizing m,
  { cases m,
    { simp },
    { simpa [eq_comm] using h m.succ m.zero_lt_succ } },
  { cases m,
    { simpa using h n.succ n.zero_lt_succ },
    { simp [pow_succ, IH] } }
end

@[to_additive nsmul_inj_mod]
lemma pow_inj_mod {n m : ℕ} :
  x ^ n = x ^ m ↔ n % order_of x = m % order_of x :=
begin
  cases (order_of x).zero_le.eq_or_lt with hx hx,
  { simp [pow_inj_iff_of_order_of_eq_zero, hx.symm] },
  rw [pow_eq_mod_order_of, @pow_eq_mod_order_of _ _ _ m],
  exact ⟨pow_injective_of_lt_order_of _ (nat.mod_lt _ hx) (nat.mod_lt _ hx), λ h, congr_arg _ h⟩
end


end group

section fintype
variables [fintype G] [fintype A]

section finite_monoid
variables [monoid G] [add_monoid A]
open_locale big_operators

@[to_additive sum_card_add_order_of_eq_card_nsmul_eq_zero]
lemma sum_card_order_of_eq_card_pow_eq_one [decidable_eq G] (hn : 0 < n) :
  ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ x : G, order_of x = m)).card
  = (finset.univ.filter (λ x : G, x ^ n = 1)).card :=
calc ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ x : G, order_of x = m)).card
    = _ : (finset.card_bUnion (by { intros, apply finset.disjoint_filter.2, cc })).symm
... = _ : congr_arg finset.card (finset.ext (begin
  assume x,
  suffices : order_of x ≤ n ∧ order_of x ∣ n ↔ x ^ n = 1,
  { simpa [nat.lt_succ_iff], },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in by rw [hm, pow_mul, pow_order_of_eq_one, one_pow],
    λ h, ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩
end))

end finite_monoid

section finite_cancel_monoid
-- TODO: Of course everything also works for right_cancel_monoids.
variables [left_cancel_monoid G] [add_left_cancel_monoid A]

-- TODO: Use this to show that a finite left cancellative monoid is a group.
@[to_additive exists_nsmul_eq_zero]
lemma exists_pow_eq_one (x : G) : is_of_fin_order x :=
begin
  refine (is_of_fin_order_iff_pow_eq_one _).mpr _,
  obtain ⟨i, j, a_eq, ne⟩ : ∃(i j : ℕ), x ^ i = x ^ j ∧ i ≠ j :=
    by simpa only [not_forall, exists_prop, injective]
      using (not_injective_infinite_fintype (λi:ℕ, x^i)),
  wlog h'' : j ≤ i,
  refine ⟨i - j, tsub_pos_of_lt (lt_of_le_of_ne h'' ne.symm), mul_right_injective (x^j) _⟩,
  rw [mul_one, ← pow_add, ← a_eq, add_tsub_cancel_of_le h''],
end

@[to_additive add_order_of_le_card_univ]
lemma order_of_le_card_univ : order_of x ≤ fintype.card G :=
finset.le_card_of_inj_on_range ((^) x)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, pow_injective_of_lt_order_of x hi hj)

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
@[to_additive add_order_of_pos
"This is the same as `add_order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative additive monoid."]
lemma order_of_pos (x : G) : 0 < order_of x := order_of_pos' (exists_pow_eq_one x)

open nat

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid.-/
@[to_additive add_order_of_nsmul
"This is the same as `add_order_of_nsmul'` and `add_order_of_nsmul` but with one assumption less
which is automatic in the case of a finite cancellative additive monoid."]
lemma order_of_pow (x : G) :
  order_of (x ^ n) = order_of x / gcd (order_of x) n := order_of_pow'' _ _ (exists_pow_eq_one _)

@[to_additive mem_multiples_iff_mem_range_add_order_of]
lemma mem_powers_iff_mem_range_order_of [decidable_eq G] :
  y ∈ submonoid.powers x ↔ y ∈ (finset.range (order_of x)).image ((^) x : ℕ → G) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos x)
  (assume i, pow_eq_mod_order_of.symm)

@[to_additive decidable_multiples]
noncomputable instance decidable_powers [decidable_eq G] :
  decidable_pred (∈ submonoid.powers x) :=
begin
  assume y,
  apply decidable_of_iff'
    (y ∈ (finset.range (order_of x)).image ((^) x)),
  exact mem_powers_iff_mem_range_order_of
end

/--The equivalence between `fin (order_of x)` and `submonoid.powers x`, sending `i` to `x ^ i`."-/
@[to_additive fin_equiv_multiples "The equivalence between `fin (add_order_of a)` and
`add_submonoid.multiples a`, sending `i` to `i • a`."]
noncomputable def fin_equiv_powers (x : G) :
  fin (order_of x) ≃ (submonoid.powers x : set G) :=
equiv.of_bijective (λ n, ⟨x ^ ↑n, ⟨n, rfl⟩⟩) ⟨λ ⟨i, hi⟩ ⟨j, hj⟩ ij,
  subtype.mk_eq_mk.2 (pow_injective_of_lt_order_of x hi hj (subtype.mk_eq_mk.1 ij)),
  λ ⟨_, i, rfl⟩, ⟨⟨i % order_of x, mod_lt i (order_of_pos x)⟩, subtype.eq pow_eq_mod_order_of.symm⟩⟩

@[simp, to_additive fin_equiv_multiples_apply]
lemma fin_equiv_powers_apply {x : G} {n : fin (order_of x)} :
  fin_equiv_powers x n = ⟨x ^ ↑n, n, rfl⟩ := rfl

@[simp, to_additive fin_equiv_multiples_symm_apply]
lemma fin_equiv_powers_symm_apply (x : G) (n : ℕ)
  {hn : ∃ (m : ℕ), x ^ m = x ^ n} :
  ((fin_equiv_powers x).symm ⟨x ^ n, hn⟩) = ⟨n % order_of x, nat.mod_lt _ (order_of_pos x)⟩ :=
by rw [equiv.symm_apply_eq, fin_equiv_powers_apply, subtype.mk_eq_mk,
  pow_eq_mod_order_of, fin.coe_mk]

/-- The equivalence between `submonoid.powers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive multiples_equiv_multiples
"The equivalence between `submonoid.multiples` of two elements `a, b` of the same additive order,
  mapping `i • a` to `i • b`."]
noncomputable def powers_equiv_powers (h : order_of x = order_of y) :
  (submonoid.powers x : set G) ≃ (submonoid.powers y : set G) :=
(fin_equiv_powers x).symm.trans ((fin.cast h).to_equiv.trans (fin_equiv_powers y))

@[simp, to_additive multiples_equiv_multiples_apply]
lemma powers_equiv_powers_apply (h : order_of x = order_of y)
  (n : ℕ) : powers_equiv_powers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩ :=
begin
  rw [powers_equiv_powers, equiv.trans_apply, equiv.trans_apply,
    fin_equiv_powers_symm_apply, ← equiv.eq_symm_apply, fin_equiv_powers_symm_apply],
  simp [h]
end

@[to_additive add_order_of_eq_card_multiples]
lemma order_eq_card_powers [decidable_eq G] :
  order_of x = fintype.card (submonoid.powers x : set G) :=
(fintype.card_fin (order_of x)).symm.trans (fintype.card_eq.2 ⟨fin_equiv_powers x⟩)

end finite_cancel_monoid

section finite_group
variables [group G] [add_group A]

@[to_additive]
lemma exists_zpow_eq_one (x : G) : ∃ (i : ℤ) (H : i ≠ 0), x ^ (i : ℤ) = 1 :=
begin
  rcases exists_pow_eq_one x with ⟨w, hw1, hw2⟩,
  refine ⟨w, int.coe_nat_ne_zero.mpr (ne_of_gt hw1), _⟩,
  rw zpow_coe_nat,
  exact (is_periodic_pt_mul_iff_pow_eq_one _).mp hw2,
end

open subgroup

@[to_additive mem_multiples_iff_mem_zmultiples]
lemma mem_powers_iff_mem_zpowers : y ∈ submonoid.powers x ↔ y ∈ zpowers x :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩,
λ ⟨i, hi⟩, ⟨(i % order_of x).nat_abs,
  by rwa [← zpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
    (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos x))),
    ← zpow_eq_mod_order_of]⟩⟩

@[to_additive multiples_eq_zmultiples]
lemma powers_eq_zpowers (x : G) : (submonoid.powers x : set G) = zpowers x :=
set.ext $ λ x, mem_powers_iff_mem_zpowers

@[to_additive mem_zmultiples_iff_mem_range_add_order_of]
lemma mem_zpowers_iff_mem_range_order_of [decidable_eq G] :
  y ∈ subgroup.zpowers x ↔ y ∈ (finset.range (order_of x)).image ((^) x : ℕ → G) :=
by rw [← mem_powers_iff_mem_zpowers, mem_powers_iff_mem_range_order_of]

@[to_additive decidable_zmultiples]
noncomputable instance decidable_zpowers [decidable_eq G] :
  decidable_pred (∈ subgroup.zpowers x) :=
begin
  simp_rw ←set_like.mem_coe,
  rw ← powers_eq_zpowers,
  exact decidable_powers,
end

/-- The equivalence between `fin (order_of x)` and `subgroup.zpowers x`, sending `i` to `x ^ i`. -/
@[to_additive fin_equiv_zmultiples
"The equivalence between `fin (add_order_of a)` and `subgroup.zmultiples a`, sending `i`
to `i • a`."]
noncomputable def fin_equiv_zpowers (x : G) :
  fin (order_of x) ≃ (subgroup.zpowers x : set G) :=
(fin_equiv_powers x).trans (equiv.set.of_eq (powers_eq_zpowers x))

@[simp, to_additive fin_equiv_zmultiples_apply]
lemma fin_equiv_zpowers_apply {n : fin (order_of x)} :
  fin_equiv_zpowers x n = ⟨x ^ (n : ℕ), n, zpow_coe_nat x n⟩ := rfl

@[simp, to_additive fin_equiv_zmultiples_symm_apply]
lemma fin_equiv_zpowers_symm_apply (x : G) (n : ℕ)
  {hn : ∃ (m : ℤ), x ^ m = x ^ n} :
  ((fin_equiv_zpowers x).symm ⟨x ^ n, hn⟩) = ⟨n % order_of x, nat.mod_lt _ (order_of_pos x)⟩ :=
by { rw [fin_equiv_zpowers, equiv.symm_trans_apply, equiv.set.of_eq_symm_apply],
  exact fin_equiv_powers_symm_apply x n }

/-- The equivalence between `subgroup.zpowers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive zmultiples_equiv_zmultiples
"The equivalence between `subgroup.zmultiples` of two elements `a, b` of the same additive order,
  mapping `i • a` to `i • b`."]
noncomputable def zpowers_equiv_zpowers (h : order_of x = order_of y) :
  (subgroup.zpowers x : set G) ≃ (subgroup.zpowers y : set G) :=
(fin_equiv_zpowers x).symm.trans ((fin.cast h).to_equiv.trans (fin_equiv_zpowers y))

@[simp, to_additive zmultiples_equiv_zmultiples_apply]
lemma zpowers_equiv_zpowers_apply (h : order_of x = order_of y)
  (n : ℕ) : zpowers_equiv_zpowers h ⟨x ^ n, n, zpow_coe_nat x n⟩ = ⟨y ^ n, n, zpow_coe_nat y n⟩ :=
begin
  rw [zpowers_equiv_zpowers, equiv.trans_apply, equiv.trans_apply,
    fin_equiv_zpowers_symm_apply, ← equiv.eq_symm_apply, fin_equiv_zpowers_symm_apply],
  simp [h]
end

@[to_additive add_order_eq_card_zmultiples]
lemma order_eq_card_zpowers [decidable_eq G] :
  order_of x = fintype.card (subgroup.zpowers x : set G) :=
(fintype.card_fin (order_of x)).symm.trans (fintype.card_eq.2 ⟨fin_equiv_zpowers x⟩)

open quotient_group

/- TODO: use cardinal theory, introduce `card : set G → ℕ`, or setup decidability for cosets -/
@[to_additive add_order_of_dvd_card_univ]
lemma order_of_dvd_card_univ : order_of x ∣ fintype.card G :=
begin
  classical,
  have ft_prod : fintype ((G ⧸ zpowers x) × zpowers x),
    from fintype.of_equiv G group_equiv_quotient_times_subgroup,
  have ft_s : fintype (zpowers x),
    from @fintype.prod_right _ _ _ ft_prod _,
  have ft_cosets : fintype (G ⧸ zpowers x),
    from @fintype.prod_left _ _ _ ft_prod ⟨⟨1, (zpowers x).one_mem⟩⟩,
  have eq₁ : fintype.card G = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
    from calc fintype.card G = @fintype.card _ ft_prod :
        @fintype.card_congr _ _ _ ft_prod group_equiv_quotient_times_subgroup
      ... = @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s) :
        congr_arg (@fintype.card _) $ subsingleton.elim _ _
      ... = @fintype.card _ ft_cosets * @fintype.card _ ft_s :
        @fintype.card_prod _ _ ft_cosets ft_s,
  have eq₂ : order_of x = @fintype.card _ ft_s,
    from calc order_of x = _ : order_eq_card_zpowers
      ... = _ : congr_arg (@fintype.card _) $ subsingleton.elim _ _,
  exact dvd.intro (@fintype.card (G ⧸ subgroup.zpowers x) ft_cosets)
          (by rw [eq₁, eq₂, mul_comm])
end

@[simp, to_additive card_nsmul_eq_zero] lemma pow_card_eq_one : x ^ fintype.card G = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ x _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]

@[to_additive nsmul_eq_mod_card] lemma pow_eq_mod_card (n : ℕ) :
  x ^ n = x ^ (n % fintype.card G) :=
by rw [pow_eq_mod_order_of, ←nat.mod_mod_of_dvd n order_of_dvd_card_univ,
  ← pow_eq_mod_order_of]

@[to_additive] lemma zpow_eq_mod_card (n : ℤ) :
  x ^ n = x ^ (n % fintype.card G) :=
by rw [zpow_eq_mod_order_of, ← int.mod_mod_of_dvd n (int.coe_nat_dvd.2 order_of_dvd_card_univ),
  ← zpow_eq_mod_order_of]

/-- If `gcd(|G|,n)=1` then the `n`th power map is a bijection -/
@[to_additive nsmul_coprime "If `gcd(|G|,n)=1` then the smul by `n` is a bijection", simps]
  def pow_coprime (h : nat.coprime (fintype.card G) n) : G ≃ G :=
{ to_fun := λ g, g ^ n,
  inv_fun := λ g, g ^ (nat.gcd_b (fintype.card G) n),
  left_inv := λ g, by
  { have key : g ^ _ = g ^ _ := congr_arg (λ n : ℤ, g ^ n) (nat.gcd_eq_gcd_ab (fintype.card G) n),
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_coe_nat, zpow_coe_nat, zpow_coe_nat,
      h.gcd_eq_one, pow_one, pow_card_eq_one, one_zpow, one_mul, eq_comm] at key },
  right_inv := λ g, by
  { have key : g ^ _ = g ^ _ := congr_arg (λ n : ℤ, g ^ n) (nat.gcd_eq_gcd_ab (fintype.card G) n),
    rwa [zpow_add, zpow_mul, zpow_mul', zpow_coe_nat, zpow_coe_nat, zpow_coe_nat,
      h.gcd_eq_one, pow_one, pow_card_eq_one, one_zpow, one_mul, eq_comm] at key } }

@[simp, to_additive] lemma pow_coprime_one (h : nat.coprime (fintype.card G) n) :
  pow_coprime h 1 = 1 := one_pow n

@[simp, to_additive] lemma pow_coprime_inv (h : nat.coprime (fintype.card G) n) {g : G} :
  pow_coprime h g⁻¹ = (pow_coprime h g)⁻¹ := inv_pow g n

@[to_additive add_inf_eq_bot_of_coprime]
lemma inf_eq_bot_of_coprime {G : Type*} [group G] {H K : subgroup G} [fintype H] [fintype K]
  (h : nat.coprime (fintype.card H) (fintype.card K)) : H ⊓ K = ⊥ :=
begin
  refine (H ⊓ K).eq_bot_iff_forall.mpr (λ x hx, _),
  rw [←order_of_eq_one_iff, ←nat.dvd_one, ←h.gcd_eq_one, nat.dvd_gcd_iff],
  exact ⟨(congr_arg (∣ fintype.card H) (order_of_subgroup ⟨x, hx.1⟩)).mpr order_of_dvd_card_univ,
    (congr_arg (∣ fintype.card K) (order_of_subgroup ⟨x, hx.2⟩)).mpr order_of_dvd_card_univ⟩,
end

variable (a)

/-- TODO: Generalise to `submonoid.powers`.-/
@[to_additive image_range_add_order_of]
lemma image_range_order_of [decidable_eq G] :
  finset.image (λ i, x ^ i) (finset.range (order_of x)) = (zpowers x : set G).to_finset :=
by { ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_zpowers_iff_mem_range_order_of] }

/-- TODO: Generalise to `finite_cancel_monoid`. -/
@[to_additive gcd_nsmul_card_eq_zero_iff]
lemma pow_gcd_card_eq_one_iff : x ^ n = 1 ↔ x ^ (gcd n (fintype.card G)) = 1 :=
⟨λ h, pow_gcd_eq_one _ h $ pow_card_eq_one,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card G) in
    by rw [hm, pow_mul, h, one_pow]⟩

end finite_group

end fintype

section pow_is_subgroup

/-- A nonempty idempotent subset of a finite cancellative monoid is a submonoid -/
@[to_additive "A nonempty idempotent subset of a finite cancellative add monoid is a submonoid"]
def submonoid_of_idempotent {M : Type*} [left_cancel_monoid M] [fintype M] (S : set M)
  (hS1 : S.nonempty) (hS2 : S * S = S) : submonoid M :=
have pow_mem : ∀ a : M, a ∈ S → ∀ n : ℕ, a ^ (n + 1) ∈ S :=
λ a ha, nat.rec (by rwa [zero_add, pow_one])
  (λ n ih, (congr_arg2 (∈) (pow_succ a (n + 1)).symm hS2).mp (set.mul_mem_mul ha ih)),
{ carrier := S,
  one_mem' := by
  { obtain ⟨a, ha⟩ := hS1,
    rw [←pow_order_of_eq_one a, ← tsub_add_cancel_of_le (succ_le_of_lt (order_of_pos a))],
    exact pow_mem a ha (order_of a - 1) },
  mul_mem' := λ a b ha hb, (congr_arg2 (∈) rfl hS2).mp (set.mul_mem_mul ha hb) }

/-- A nonempty idempotent subset of a finite group is a subgroup -/
@[to_additive "A nonempty idempotent subset of a finite add group is a subgroup"]
def subgroup_of_idempotent {G : Type*} [group G] [fintype G] (S : set G)
  (hS1 : S.nonempty) (hS2 : S * S = S) : subgroup G :=
{ carrier := S,
  inv_mem' := λ a ha, by
  { rw [←one_mul a⁻¹, ←pow_one a, ←pow_order_of_eq_one a, ←pow_sub a (order_of_pos a)],
    exact (submonoid_of_idempotent S hS1 hS2).pow_mem ha (order_of a - 1) },
  .. submonoid_of_idempotent S hS1 hS2 }

/-- If `S` is a nonempty subset of a finite group `G`, then `S ^ |G|` is a subgroup -/
@[to_additive smul_card_add_subgroup "If `S` is a nonempty subset of a finite add group `G`,
  then `|G| • S` is a subgroup -/", simps]
def pow_card_subgroup {G : Type*} [group G] [fintype G] (S : set G) (hS : S.nonempty) :
  subgroup G :=
have one_mem : (1 : G) ∈ (S ^ fintype.card G) := by
{ obtain ⟨a, ha⟩ := hS,
  rw ← pow_card_eq_one,
  exact set.pow_mem_pow ha (fintype.card G) },
subgroup_of_idempotent (S ^ (fintype.card G)) ⟨1, one_mem⟩ begin
  classical,
  refine (set.eq_of_subset_of_card_le
    (λ b hb, (congr_arg (∈ _) (one_mul b)).mp (set.mul_mem_mul one_mem hb)) (ge_of_eq _)).symm,
  change _ = fintype.card (_ * _ : set G),
  rw [←pow_add, group.card_pow_eq_card_pow_card_univ S (fintype.card G) le_rfl,
      group.card_pow_eq_card_pow_card_univ S (fintype.card G + fintype.card G) le_add_self],
end

end pow_is_subgroup

section linear_ordered_ring

variable [linear_ordered_ring G]

lemma order_of_abs_ne_one (h : |x| ≠ 1) : order_of x = 0 :=
begin
  rw order_of_eq_zero_iff',
  intros n hn hx,
  replace hx : |x| ^ n = 1 := by simpa only [abs_one, abs_pow] using congr_arg abs hx,
  cases h.lt_or_lt with h h,
  { exact ((pow_lt_one (abs_nonneg x) h hn.ne').ne hx).elim },
  { exact ((one_lt_pow h hn.ne').ne' hx).elim }
end

lemma linear_ordered_ring.order_of_le_two : order_of x ≤ 2 :=
begin
  cases ne_or_eq (|x|) 1 with h h,
  { simp [order_of_abs_ne_one h] },
  rcases eq_or_eq_neg_of_abs_eq h with rfl | rfl,
  { simp },
  apply order_of_le_of_pow_eq_one; norm_num
end

end linear_ordered_ring
