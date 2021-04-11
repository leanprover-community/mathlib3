/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
import algebra.big_operators.order
import group_theory.coset
import data.nat.totient
import data.int.gcd
import data.set.finite
import dynamics.periodic_pts
import algebra.iterate_hom

/-!
# Order of an element
This file defines the order of an element of a finite group. For a finite group `G` the order of
`g ∈ G` is the minimal `n ≥ 1` such that `g ^ n = 1`.
## Main definitions
* `order_of` defines the order of an element `a` of a group `G`, by convention its value is `0` if
  `a` has infinite order.
## Tags
order of an element
-/

open function nat

universes u v

-- Move somewhere else starting from here...
@[to_additive]
lemma one_mul_eq_id {M : Type u} [mul_one_class M] : ((*) (1 : M)) = id := funext one_mul

@[to_additive]
lemma mul_one_eq_id {M : Type u} [mul_one_class M] : (* (1 : M)) = id := funext mul_one

@[to_additive]
lemma semiconj_by.function_semiconj_mul_left {G : Type u} [monoid G] {a b c : G}
  (h : semiconj_by a b c) :
  function.semiconj ((*)a) ((*)b) ((*)c) :=
λ j, by rw [← mul_assoc, h.eq, mul_assoc]

@[to_additive]
lemma commute.function_commute_mul_left {G : Type u} [monoid G] {a b c : G} (h : commute a b) :
  function.commute ((*)a) ((*)b) :=
semiconj_by.function_semiconj_mul_left h

-- These two lemmas are no longer used in this PR and are never cited
-- (I would keep them anyway for completeness)
@[to_additive]
lemma semiconj_by.function_semiconj_mul_right_swap {G : Type u} [monoid G] {a b c : G}
  (h : semiconj_by a b c) :
  function.semiconj (*a) (*c) (*b) :=
λ j, by simp_rw [mul_assoc, ← h.eq]

@[to_additive]
lemma commute.function_commute_mul_right {G : Type u} [monoid G] {a b c : G} (h : commute a b) :
  function.commute (*a) (*b) :=
semiconj_by.function_semiconj_mul_right_swap h
-- ...until here

variables {G : Type u} {H : Type v} {x : H}
variables {a : G} {n m : ℕ}

section monoid_add_monoid

variables [monoid G] [add_monoid H]

section is_of_fin_order

lemma is_periodic_pt_add_iff_nsmul_eq_zero (x : H) :
  is_periodic_pt ((+) x) n 0 ↔ n •ℕ x = 0 :=
by rw [is_periodic_pt, is_fixed_pt, add_left_iterate, add_zero]

@[to_additive is_periodic_pt_add_iff_nsmul_eq_zero]
lemma is_periodic_pt_mul_iff_pow_eq_one (a : G) : is_periodic_pt ((*) a) n 1 ↔ a ^ n = 1 :=
by rw [is_periodic_pt, is_fixed_pt, mul_left_iterate, mul_one]

/-- `is_of_fin_add_order` is a predicate on an element `x` of an additive monoid to be of finite
order, i.e. there exists `n ≥ 1` such that `n •ℕ x = 0`.-/
def is_of_fin_add_order (x : H) : Prop :=
(0 : H) ∈ periodic_pts ((+) x)

/-- `is_of_fin_order` is a predicate on an element `a` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `a ^ n = 1`.-/
@[to_additive is_of_fin_add_order]
def is_of_fin_order (a : G) : Prop :=
(1 : G) ∈ periodic_pts ((*) a)

lemma is_of_fin_add_order_of_mul_iff :
is_of_fin_add_order (additive.of_mul a) ↔ is_of_fin_order a :=
by refl

lemma is_of_fin_order_of_add_iff :
is_of_fin_order (multiplicative.of_add x) ↔ is_of_fin_add_order x :=
by refl

lemma is_of_fin_add_order_iff_nsmul_eq_zero (x : H) :
  is_of_fin_add_order x ↔ ∃ n, 0 < n ∧ n •ℕ x = 0 :=
by { convert iff.rfl, simp only [exists_prop, is_periodic_pt_add_iff_nsmul_eq_zero] }

@[to_additive is_of_fin_add_order_iff_nsmul_eq_zero]
lemma is_of_fin_order_iff_pow_eq_one (a : G) :
  is_of_fin_order a ↔ ∃ n, 0 < n ∧ a ^ n = 1 :=
by { convert iff.rfl, simp [is_periodic_pt_mul_iff_pow_eq_one] }

end is_of_fin_order

/-- `add_order_of x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `n •ℕ x = 0` if it
exists. Otherwise, i.e. if `x` is of infinite order, then `add_order_of x` is `0` by convention.-/
noncomputable def add_order_of (x : H) : ℕ :=
minimal_period ((+) x) 0

/-- `order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `a ^ n = 1` if it exists.
Otherwise, i.e. if `a` is of infinite order, then `order_of a` is `0` by convention.-/
@[to_additive add_order_of]
noncomputable def order_of (a : G) : ℕ :=
minimal_period ((*) a) 1

attribute [to_additive add_order_of] order_of

@[to_additive]
lemma commute.order_of_mul_dvd_lcm {b : G} (h : commute a b) :
  order_of (a * b) ∣ nat.lcm (order_of a) (order_of b) :=
begin
  convert function.commute.minimal_period_of_comp_dvd_lcm h.function_commute_mul_left,
  rw [order_of, comp_mul_left],
  exact (1 : G)
end

@[simp] lemma add_order_of_of_mul_eq_order_of (a : G) :
  add_order_of (additive.of_mul a) = order_of a := rfl

@[simp] lemma order_of_of_add_eq_add_order_of (x : H) :
  order_of (multiplicative.of_add x) = add_order_of x := rfl

@[to_additive add_order_of_pos']
lemma order_of_pos' (h : is_of_fin_order a) : 0 < order_of a :=
minimal_period_pos_of_mem_periodic_pts h

lemma add_order_of_nsmul_eq_zero (x : H) : (add_order_of x) •ℕ x = 0 :=
begin
  convert is_periodic_pt_minimal_period ((+) x) _,
  rw [add_order_of, add_left_iterate, add_zero],
end

@[to_additive add_order_of_nsmul_eq_zero]
lemma pow_order_of_eq_one (a : G) : a ^ order_of a = 1 :=
begin
  convert is_periodic_pt_minimal_period ((*) a) _,
  rw [order_of, mul_left_iterate, mul_one],
end

@[to_additive add_order_of_eq_zero]
lemma order_of_eq_zero (h : ¬ is_of_fin_order a) : order_of a = 0 :=
by rwa [order_of, minimal_period, dif_neg]

lemma nsmul_ne_zero_of_lt_add_order_of' (n0 : n ≠ 0) (h : n < add_order_of x) :
  n •ℕ x ≠ 0 :=
λ j, not_is_periodic_pt_of_pos_of_lt_minimal_period n0 h
  ((is_periodic_pt_add_iff_nsmul_eq_zero x).mpr j)

@[to_additive nsmul_ne_zero_of_lt_add_order_of']
lemma pow_eq_one_of_lt_order_of' (n0 : n ≠ 0) (h : n < order_of a) : a ^ n ≠ 1 :=
λ j, not_is_periodic_pt_of_pos_of_lt_minimal_period n0 h
  ((is_periodic_pt_mul_iff_pow_eq_one a).mpr j)

lemma add_order_of_le_of_nsmul_eq_zero (hn : 0 < n) (h : n •ℕ x = 0) : add_order_of x ≤ n :=
is_periodic_pt.minimal_period_le hn (by rwa is_periodic_pt_add_iff_nsmul_eq_zero)

@[to_additive add_order_of_le_of_nsmul_eq_zero]
lemma order_of_le_of_pow_eq_one (hn : 0 < n) (h : a ^ n = 1) : order_of a ≤ n :=
is_periodic_pt.minimal_period_le hn (by rwa is_periodic_pt_mul_iff_pow_eq_one)

@[simp] lemma order_of_one : order_of (1 : G) = 1 :=
begin
  rw [order_of, one_mul_eq_id],
  exact minimal_period_id,
end

@[simp] lemma add_order_of_zero : add_order_of (0 : H) = 1 :=
by simp only [←order_of_of_add_eq_add_order_of, order_of_one, of_add_zero]

attribute [to_additive add_order_of_zero] order_of_one

@[simp] lemma order_of_eq_one_iff : order_of a = 1 ↔ a = 1 :=
by rw [order_of, is_fixed_point_iff_minimal_period_eq_one, is_fixed_pt, mul_one]

@[simp] lemma add_order_of_eq_one_iff : add_order_of x = 1 ↔ x = 0 :=
by simp [← order_of_of_add_eq_add_order_of]

attribute [to_additive add_order_of_eq_one_iff] order_of_eq_one_iff

lemma nsmul_eq_mod_add_order_of : n •ℕ x = (n % add_order_of x) •ℕ x :=
begin
  nth_rewrite 0 [← n.div_add_mod' (add_order_of x)],
  rw [add_nsmul, mul_nsmul, add_order_of_nsmul_eq_zero, nsmul_zero, zero_add],
end

@[to_additive nsmul_eq_mod_add_order_of]
lemma pow_eq_mod_order_of : a ^ n = a ^ (n % order_of a) :=
begin
  nth_rewrite 0 [← n.mod_add_div (order_of a)],
  rw [pow_add, pow_mul, pow_order_of_eq_one, one_pow, mul_one],
end

lemma add_order_of_dvd_of_nsmul_eq_zero (h : n •ℕ x = 0) : add_order_of x ∣ n :=
is_periodic_pt.minimal_period_dvd ((is_periodic_pt_add_iff_nsmul_eq_zero _).mpr h)

@[to_additive add_order_of_dvd_of_nsmul_eq_zero]
lemma order_of_dvd_of_pow_eq_one (h : a ^ n = 1) : order_of a ∣ n :=
is_periodic_pt.minimal_period_dvd ((is_periodic_pt_mul_iff_pow_eq_one _).mpr h)

lemma add_order_of_dvd_iff_nsmul_eq_zero : add_order_of x ∣ n ↔ n •ℕ x = 0 :=
by rw [← is_periodic_pt_add_iff_nsmul_eq_zero, is_periodic_pt_iff_minimal_period_dvd, add_order_of]

@[to_additive add_order_of_dvd_iff_nsmul_eq_zero]
lemma order_of_dvd_iff_pow_eq_one : order_of a ∣ n ↔ a ^ n = 1 :=
by rw [← is_periodic_pt_mul_iff_pow_eq_one, is_periodic_pt_iff_minimal_period_dvd, order_of]

lemma exists_pow_eq_self_of_coprime (h : n.coprime (order_of a)) :
  ∃ m : ℕ, (a ^ n) ^ m = a :=
begin
  by_cases h0 : order_of a = 0,
  { rw [h0, coprime_zero_right] at h,
    exact ⟨1, by rw [h, pow_one, pow_one]⟩ },
  by_cases h1 : order_of a = 1,
  { exact ⟨37, by rw [order_of_eq_one_iff.mp h1, one_pow, one_pow]⟩ },
  obtain ⟨m, hm⟩ :=
    exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩),
  exact ⟨m, by rw [←pow_mul, pow_eq_mod_order_of, hm, pow_one]⟩,
end

lemma add_order_of_eq_add_order_of_iff {A : Type*} [add_monoid A] {y : A} :
  add_order_of x = add_order_of y ↔ ∀ n : ℕ, n •ℕ x = 0 ↔ n •ℕ y = 0 :=
begin
  simp_rw ← add_order_of_dvd_iff_nsmul_eq_zero,
  exact ⟨λ h n, by rw h, λ h, nat.dvd_antisymm ((h _).mpr (dvd_refl _)) ((h _).mp (dvd_refl _))⟩,
end

@[to_additive add_order_of_eq_add_order_of_iff]
lemma order_of_eq_order_of_iff {β : Type*} [monoid β] {b : β} :
  order_of a = order_of b ↔ ∀ n : ℕ, a ^ n = 1 ↔ b ^ n = 1 :=
by simp_rw [← is_periodic_pt_mul_iff_pow_eq_one, ← minimal_period_eq_minimal_period_iff, order_of]

lemma add_order_of_injective {A B : Type*} [add_monoid A] [add_monoid B] (f : A →+ B)
  (hf : function.injective f) (x : A) : add_order_of (f x) = add_order_of x :=
by simp_rw [add_order_of_eq_add_order_of_iff, ←f.map_nsmul, ←f.map_zero, hf.eq_iff, iff_self,
            forall_const]

@[to_additive add_order_of_injective]
lemma order_of_injective {G H : Type*} [monoid G] [monoid H] (f : G →* H)
  (hf : function.injective f) (σ : G) : order_of (f σ) = order_of σ :=
by simp_rw [order_of_eq_order_of_iff, ←f.map_pow, ←f.map_one, hf.eq_iff, iff_self, forall_const]

@[simp, norm_cast, to_additive] lemma order_of_submonoid {G : Type*} [monoid G] {H : submonoid G}
  (σ : H) : order_of (σ : G) = order_of σ :=
order_of_injective H.subtype subtype.coe_injective σ

@[simp, norm_cast, to_additive] lemma order_of_subgroup {G : Type*} [group G] {H : subgroup G}
  (σ : H) : order_of (σ : G) = order_of σ :=
order_of_injective H.subtype subtype.coe_injective σ

variables (a)

lemma order_of_pow' (h : n ≠ 0) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
begin
  convert minimal_period_iterate_eq_div_gcd h,
  simp only [order_of, mul_left_iterate],
end

variables (x)

lemma add_order_of_nsmul' (h : n ≠ 0) :
  add_order_of (n •ℕ x) = add_order_of x / gcd (add_order_of x) n :=
by simpa [← order_of_of_add_eq_add_order_of, of_add_nsmul] using order_of_pow' _ h

attribute [to_additive add_order_of_nsmul'] order_of_pow'

variable (n)

lemma order_of_pow'' (h : is_of_fin_order a) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
begin
  convert minimal_period_iterate_eq_div_gcd' h,
  simp only [order_of, mul_left_iterate],
end

lemma add_order_of_nsmul'' (h : is_of_fin_add_order x) :
  add_order_of (n •ℕ x) = add_order_of x / gcd (add_order_of x) n :=
by simp [← order_of_of_add_eq_add_order_of, of_add_nsmul,
  order_of_pow'' _ n (is_of_fin_order_of_add_iff.mpr h)]

attribute [to_additive add_order_of_nsmul''] order_of_pow''

section p_prime

variables {a n} {p : ℕ} [hp : fact p.prime]
include hp

lemma add_order_of_eq_prime (hg : p •ℕ x = 0) (hg1 : x ≠ 0) : add_order_of x = p :=
minimal_period_eq_prime ((is_periodic_pt_add_iff_nsmul_eq_zero _).mpr hg)
  (by rwa [is_fixed_pt, add_zero])

@[to_additive add_order_of_eq_prime]
lemma order_of_eq_prime (hg : a ^ p = 1) (hg1 : a ≠ 1) : order_of a = p :=
minimal_period_eq_prime ((is_periodic_pt_mul_iff_pow_eq_one _).mpr hg)
  (by rwa [is_fixed_pt, mul_one])

lemma add_order_of_eq_prime_pow (hnot : ¬ (p ^ n) •ℕ x = 0) (hfin : (p ^ (n + 1)) •ℕ x = 0) :
  add_order_of x = p ^ (n + 1) :=
begin
  apply minimal_period_eq_prime_pow;
  rwa is_periodic_pt_add_iff_nsmul_eq_zero,
end

@[to_additive add_order_of_eq_prime_pow]
lemma order_of_eq_prime_pow (hnot : ¬ a ^ p ^ n = 1) (hfin : a ^ p ^ (n + 1) = 1) :
  order_of a = p ^ (n + 1) :=
begin
  apply minimal_period_eq_prime_pow;
  rwa is_periodic_pt_mul_iff_pow_eq_one,
end

omit hp
-- An example on how to determine the order of an element of a finite group.
example : order_of (-1 : units ℤ) = 2 :=
begin
  haveI : fact (prime 2) := ⟨prime_two⟩,
  exact order_of_eq_prime (int.units_mul_self _) dec_trivial,
end

end p_prime

end monoid_add_monoid

section cancel_monoid
variables [left_cancel_monoid G] (a)
variables [add_left_cancel_monoid H] (x)

lemma pow_injective_aux (h : n ≤ m)
  (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
by_contradiction $ assume ne : n ≠ m,
  have h₁ : m - n > 0, from nat.pos_of_ne_zero (by simp [nat.sub_eq_iff_eq_add h, ne.symm]),
  have h₂ : m = n + (m - n) := (nat.add_sub_of_le h).symm,
  have h₃ : a ^ (m - n) = 1,
    by { rw [h₂, pow_add] at eq, apply mul_left_cancel, convert eq.symm, exact mul_one (a ^ n) },
  have le : order_of a ≤ m - n, from order_of_le_of_pow_eq_one h₁ h₃,
  have lt : m - n < order_of a,
    from (nat.sub_lt_left_iff_lt_add h).mpr $ nat.lt_add_left _ _ _ hm,
  lt_irrefl _ (le.trans_lt lt)

-- TODO: This lemma was originally private, but this doesn't seem to work with `to_additive`,
-- therefore the private got removed.
lemma nsmul_injective_aux (h : n ≤ m)
  (hm : m < add_order_of x) (eq : n •ℕ x = m •ℕ x) : n = m :=
pow_injective_aux (multiplicative.of_add x) h hm eq

attribute [to_additive nsmul_injective_aux] pow_injective_aux

lemma nsmul_injective_of_lt_add_order_of
  (hn : n < add_order_of x) (hm : m < add_order_of x) (eq : n •ℕ x = m •ℕ x) : n = m :=
(le_total n m).elim
  (assume h, nsmul_injective_aux x h hm eq)
  (assume h, (nsmul_injective_aux x h hn eq.symm).symm)

@[to_additive nsmul_injective_of_lt_add_order_of]
lemma pow_injective_of_lt_order_of
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
(le_total n m).elim
  (assume h, pow_injective_aux a h hm eq)
  (assume h, (pow_injective_aux a h hn eq.symm).symm)

end cancel_monoid

section group
variables [group G] [add_group H] {x} {i : ℤ}

lemma gpow_eq_mod_order_of : a ^ i = a ^ (i % order_of a) :=
calc a ^ i = a ^ (i % order_of a + order_of a * (i / order_of a)) :
    by rw [int.mod_add_div]
       ... = a ^ (i % order_of a) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]

lemma gsmul_eq_mod_add_order_of : i •ℤ x = (i % add_order_of x) •ℤ x :=
begin
  apply multiplicative.of_add.injective,
  simp [of_add_gsmul, gpow_eq_mod_order_of],
end

attribute [to_additive gsmul_eq_mod_add_order_of] gpow_eq_mod_order_of

end group

section fintype
variables [fintype G] [fintype H]

section finite_monoid
variables [monoid G] [add_monoid H]
open_locale big_operators

lemma sum_card_add_order_of_eq_card_nsmul_eq_zero [decidable_eq H] (hn : 0 < n) :
  ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ x : H, add_order_of x = m)).card
  = (finset.univ.filter (λ x : H, n •ℕ x = 0)).card :=
calc ∑ m in (finset.range n.succ).filter (∣ n),
        (finset.univ.filter (λ x : H, add_order_of x = m)).card
    = _ : (finset.card_bUnion (by { intros, apply finset.disjoint_filter.2, cc })).symm
... = _ : congr_arg finset.card (finset.ext (begin
  assume x,
  suffices : add_order_of x ≤ n ∧ add_order_of x ∣ n ↔ n •ℕ x = 0,
  { simpa [nat.lt_succ_iff], },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in
                by rw [hm, mul_comm, mul_nsmul, add_order_of_nsmul_eq_zero, nsmul_zero],
    λ h, ⟨add_order_of_le_of_nsmul_eq_zero hn h, add_order_of_dvd_of_nsmul_eq_zero h⟩⟩
end))

@[to_additive sum_card_add_order_of_eq_card_nsmul_eq_zero]
lemma sum_card_order_of_eq_card_pow_eq_one [decidable_eq G] (hn : 0 < n) :
  ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ a : G, order_of a = m)).card
  = (finset.univ.filter (λ a : G, a ^ n = 1)).card :=
calc ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ a : G, order_of a = m)).card
    = _ : (finset.card_bUnion (by { intros, apply finset.disjoint_filter.2, cc })).symm
... = _ : congr_arg finset.card (finset.ext (begin
  assume a,
  suffices : order_of a ≤ n ∧ order_of a ∣ n ↔ a ^ n = 1,
  { simpa [nat.lt_succ_iff], },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in by rw [hm, pow_mul, pow_order_of_eq_one, one_pow],
    λ h, ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩
end))

end finite_monoid

section finite_cancel_monoid
-- TODO: Of course everything also works for right_cancel_monoids.
variables [left_cancel_monoid G] [add_left_cancel_monoid H]

-- TODO: Use this to show that a finite left cancellative monoid is a group.

lemma exists_pow_eq_one (a : G) : is_of_fin_order a :=
begin
  refine (is_of_fin_order_iff_pow_eq_one _).mpr _,
  obtain ⟨i, j, a_eq, ne⟩ : ∃(i j : ℕ), a ^ i = a ^ j ∧ i ≠ j :=
    by simpa only [not_forall, exists_prop] using (not_injective_infinite_fintype (λi:ℕ, a^i)),
  wlog h'' : j ≤ i,
  refine ⟨i - j, nat.sub_pos_of_lt (lt_of_le_of_ne h'' ne.symm), mul_right_injective (a ^j) _⟩,
  rw [mul_one, ← pow_add, ← a_eq, nat.add_sub_cancel' h''],
end

lemma exists_nsmul_eq_zero (x : H) : is_of_fin_add_order x :=
exists_pow_eq_one (multiplicative.of_add x)

attribute [to_additive exists_nsmul_eq_zero] exists_pow_eq_one

lemma add_order_of_le_card_univ : add_order_of x ≤ fintype.card H :=
finset.le_card_of_inj_on_range (•ℕ x)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, nsmul_injective_of_lt_add_order_of x hi hj)

@[to_additive add_order_of_le_card_univ]
lemma order_of_le_card_univ : order_of a ≤ fintype.card G :=
finset.le_card_of_inj_on_range ((^) a)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, pow_injective_of_lt_order_of a hi hj)

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
lemma order_of_pos (a : G) : 0 < order_of a := order_of_pos' (exists_pow_eq_one a)

/-- This is the same as `add_order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative additive monoid.-/
lemma add_order_of_pos (x : H) : 0 < add_order_of x :=
begin
  rw ← order_of_of_add_eq_add_order_of,
  exact order_of_pos _,
end

attribute [to_additive add_order_of_pos] order_of_pos

lemma exists_nsmul_eq_self_of_coprime {H : Type*} [add_monoid H] (x : H)
  (h : coprime n (add_order_of x)) : ∃ m : ℕ, m •ℕ (n •ℕ x) = x :=
begin
  change coprime n (order_of (multiplicative.of_add x)) at h,
  exact exists_pow_eq_self_of_coprime h,
end

attribute [to_additive exists_nsmul_eq_self_of_coprime] exists_pow_eq_self_of_coprime

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid.-/
lemma order_of_pow (a : G) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n := order_of_pow'' _ _ (exists_pow_eq_one _)

/-- This is the same as `add_order_of_nsmul'` and `add_order_of_nsmul` but with one assumption less
which is automatic in the case of a finite cancellative additive monoid. -/
lemma add_order_of_nsmul (x : H) :
  add_order_of (n •ℕ x) = add_order_of x / gcd (add_order_of x) n :=
begin
  rw [← order_of_of_add_eq_add_order_of, of_add_nsmul],
  exact order_of_pow _,
end

attribute [to_additive add_order_of_nsmul] order_of_pow

lemma mem_multiples_iff_mem_range_add_order_of [decidable_eq H] {x' : H} :
  x' ∈ add_submonoid.multiples x ↔
  x' ∈ (finset.range (add_order_of x)).image ((•ℕ x) : ℕ → H)  :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (add_order_of_pos x)
  (assume i, nsmul_eq_mod_add_order_of.symm)

@[to_additive mem_multiples_iff_mem_range_add_order_of]
lemma mem_powers_iff_mem_range_order_of [decidable_eq G] {a' : G} :
  a' ∈ submonoid.powers a ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → G) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos a)
  (assume i, pow_eq_mod_order_of.symm)

noncomputable instance decidable_multiples [decidable_eq H] :
  decidable_pred (add_submonoid.multiples x : set H) :=
begin
  assume x',
  apply decidable_of_iff' (x' ∈ (finset.range (add_order_of x)).image (•ℕ x)),
  exact mem_multiples_iff_mem_range_add_order_of,
end

@[to_additive decidable_multiples]
noncomputable instance decidable_powers [decidable_eq G] :
  decidable_pred (submonoid.powers a : set G) :=
begin
  assume a',
  apply decidable_of_iff'
    (a' ∈ (finset.range (order_of a)).image ((^) a)),
  exact mem_powers_iff_mem_range_order_of
end

lemma order_eq_card_powers [decidable_eq G] :
  order_of a = fintype.card (submonoid.powers a : set G) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨a ^ n, ⟨n, rfl⟩⟩ },
  { rintros ⟨_, i, rfl⟩ _,
    exact ⟨i % order_of a, mod_lt i (order_of_pos a), subtype.eq pow_eq_mod_order_of.symm⟩ },
  { exact λ _ _, finset.mem_univ _ },
  { exact λ i j hi hj eq, pow_injective_of_lt_order_of a hi hj (subtype.mk_eq_mk.mp eq) }
end

lemma add_order_of_eq_card_multiples [decidable_eq H] :
  add_order_of x = fintype.card (add_submonoid.multiples x : set H) :=
begin
  rw [← order_of_of_add_eq_add_order_of, order_eq_card_powers],
  apply fintype.card_congr,
  rw ←of_add_image_multiples_eq_powers_of_add,
  exact (equiv.set.image _ _ (equiv.injective _)).symm
end

attribute [to_additive add_order_of_eq_card_multiples] order_eq_card_powers

end finite_cancel_monoid

section finite_group
variables [group G] [add_group H]

lemma exists_gpow_eq_one (a : G) : ∃ i ≠ 0, a ^ (i : ℤ) = 1 :=
begin
  rcases exists_pow_eq_one a with ⟨w, hw1, hw2⟩,
  exact ⟨w, int.coe_nat_ne_zero.mpr (ne_of_gt hw1), (is_periodic_pt_mul_iff_pow_eq_one _).mp hw2⟩,
end

lemma exists_gsmul_eq_zero (x : H) : ∃ i ≠ 0, i •ℤ x = 0 :=
exists_gpow_eq_one (multiplicative.of_add x)

attribute [to_additive exists_gsmul_eq_zero] exists_gpow_eq_one

lemma mem_multiples_iff_mem_gmultiples {y : H} :
  y ∈ add_submonoid.multiples x ↔ y ∈ add_subgroup.gmultiples x :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩, λ ⟨i, hi⟩, ⟨(i % add_order_of x).nat_abs,
  by { convert hi,
       change (i % (add_order_of x)).nat_abs •ℕ x = (λ y, y •ℤ x) i,
       rwa [← gsmul_coe_nat,
          int.nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2
          (add_order_of_pos x))), ← gsmul_eq_mod_add_order_of] } ⟩⟩

open subgroup

@[to_additive mem_multiples_iff_mem_gmultiples]
lemma mem_powers_iff_mem_gpowers {x : G} : x ∈ submonoid.powers a ↔ x ∈ gpowers a :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩,
λ ⟨i, hi⟩, ⟨(i % order_of a).nat_abs,
  by rwa [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
    (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos a))),
    ← gpow_eq_mod_order_of]⟩⟩

lemma multiples_eq_gmultiples (x : H) :
  (add_submonoid.multiples x : set H) = add_subgroup.gmultiples x :=
set.ext $ λ y, mem_multiples_iff_mem_gmultiples

@[to_additive multiples_eq_gmultiples]
lemma powers_eq_gpowers (a : G) : (submonoid.powers a : set G) = gpowers a :=
set.ext $ λ x, mem_powers_iff_mem_gpowers

lemma mem_gmultiples_iff_mem_range_add_order_of [decidable_eq H] {x' : H} :
  x' ∈ add_subgroup.gmultiples x ↔ x' ∈ (finset.range (add_order_of x)).image (•ℕ x) :=
by rw [← mem_multiples_iff_mem_gmultiples, mem_multiples_iff_mem_range_add_order_of]

@[to_additive mem_gmultiples_iff_mem_range_add_order_of]
lemma mem_gpowers_iff_mem_range_order_of [decidable_eq G] {a' : G} :
  a' ∈ subgroup.gpowers a ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → G) :=
by rw [← mem_powers_iff_mem_gpowers, mem_powers_iff_mem_range_order_of]

noncomputable instance decidable_gmultiples [decidable_eq H] :
  decidable_pred (add_subgroup.gmultiples x : set H) :=
begin
  rw ← multiples_eq_gmultiples,
  exact decidable_multiples,
end

@[to_additive decidable_gmultiples]
noncomputable instance decidable_gpowers [decidable_eq G] :
  decidable_pred (subgroup.gpowers a : set G) :=
begin
  rw ← powers_eq_gpowers,
  exact decidable_powers,
end

lemma order_eq_card_gpowers [decidable_eq G] :
  order_of a = fintype.card (subgroup.gpowers a : set G) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨a ^ (n : ℤ), ⟨n, rfl⟩⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
    have pos : (0 : ℤ) < order_of a := int.coe_nat_lt.mpr $ order_of_pos a,
    have 0 ≤ i % (order_of a) := int.mod_nonneg _ $ ne_of_gt pos,
    ⟨int.to_nat (i % order_of a),
      by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
        exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { exact λ _ _, finset.mem_univ _ },
  { exact λ i j hi hj eq, pow_injective_of_lt_order_of a hi hj $ subtype.mk_eq_mk.mp eq }
end

lemma add_order_eq_card_gmultiples [decidable_eq H] :
  add_order_of x = fintype.card (add_subgroup.gmultiples x : set H) :=
begin
  rw [← order_of_of_add_eq_add_order_of, order_eq_card_gpowers],
  apply fintype.card_congr,
  rw ← of_add_image_gmultiples_eq_gpowers_of_add,
  exact (equiv.set.image _ _ (equiv.injective _)).symm
end

attribute [to_additive add_order_eq_card_gmultiples] order_eq_card_gpowers

open quotient_group

/- TODO: use cardinal theory, introduce `card : set G → ℕ`, or setup decidability for cosets -/
lemma order_of_dvd_card_univ : order_of a ∣ fintype.card G :=
begin
  classical,
  have ft_prod : fintype (quotient (gpowers a) × (gpowers a)),
    from fintype.of_equiv G group_equiv_quotient_times_subgroup,
  have ft_s : fintype (gpowers a),
    from @fintype.fintype_prod_right _ _ _ ft_prod _,
  have ft_cosets : fintype (quotient (gpowers a)),
    from @fintype.fintype_prod_left _ _ _ ft_prod ⟨⟨1, (gpowers a).one_mem⟩⟩,
  have eq₁ : fintype.card G = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
    from calc fintype.card G = @fintype.card _ ft_prod :
        @fintype.card_congr _ _ _ ft_prod group_equiv_quotient_times_subgroup
      ... = @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s) :
        congr_arg (@fintype.card _) $ subsingleton.elim _ _
      ... = @fintype.card _ ft_cosets * @fintype.card _ ft_s :
        @fintype.card_prod _ _ ft_cosets ft_s,
  have eq₂ : order_of a = @fintype.card _ ft_s,
    from calc order_of a = _ : order_eq_card_gpowers
      ... = _ : congr_arg (@fintype.card _) $ subsingleton.elim _ _,
  exact dvd.intro (@fintype.card (quotient (subgroup.gpowers a)) ft_cosets)
          (by rw [eq₁, eq₂, mul_comm])
end

lemma add_order_of_dvd_card_univ : add_order_of x ∣ fintype.card H :=
begin
  rw ← order_of_of_add_eq_add_order_of,
  exact order_of_dvd_card_univ,
end

attribute [to_additive add_order_of_dvd_card_univ] order_of_dvd_card_univ

@[simp] lemma pow_card_eq_one : a ^ fintype.card G = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ a _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]

@[simp] lemma card_nsmul_eq_zero {x : H} : fintype.card H •ℕ x = 0 :=
multiplicative.of_add.injective pow_card_eq_one

attribute [to_additive card_nsmul_eq_zero] pow_card_eq_one

variable (a)

lemma image_range_add_order_of [decidable_eq H] :
  finset.image (λ i, i •ℕ x) (finset.range (add_order_of x)) =
  (add_subgroup.gmultiples x : set H).to_finset :=
by {ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_gmultiples_iff_mem_range_add_order_of] }

/-- TODO: Generalise to `submonoid.powers`.-/
@[to_additive image_range_add_order_of]
lemma image_range_order_of [decidable_eq G] :
  finset.image (λ i, a ^ i) (finset.range (order_of a)) = (gpowers a : set G).to_finset :=
by { ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_gpowers_iff_mem_range_order_of] }

lemma gcd_nsmul_card_eq_zero_iff : n •ℕ x = 0 ↔ (gcd n (fintype.card H)) •ℕ x = 0 :=
⟨λ h, gcd_nsmul_eq_zero _ h $ card_nsmul_eq_zero,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card H) in
    by rw [hm, mul_comm, mul_nsmul, h, nsmul_zero]⟩

/-- TODO: Generalise to `finite_cancel_monoid`. -/
@[to_additive gcd_nsmul_card_eq_zero_iff]
lemma pow_gcd_card_eq_one_iff : a ^ n = 1 ↔ a ^ (gcd n (fintype.card G)) = 1 :=
⟨λ h, pow_gcd_eq_one _ h $ pow_card_eq_one,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card G) in
    by rw [hm, pow_mul, h, one_pow]⟩

end finite_group

end fintype
