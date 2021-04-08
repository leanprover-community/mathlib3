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

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`g ∈ G` is the minimal `n ≥ 1` such that `g ^ n = 1`.

## Main definitions

* `order_of` defines the order of an element `a` of a group `G`, by convention its value is `0` if
  `a` has infinite order.

## Tags

order of an element

## TODO

* Move the first declarations until the definition of order to other files.
* Yury's suggestion: Redefine `order_of x := minimal_period (* x) 1`, this should make `to_additive`
  easier.
-/

open function
open_locale big_operators

universe u

variables {α : Type u} {s : set α} {a a₁ a₂ b c: α}

section order_of

section monoid
variables {α} [monoid α]
variables {H : Type u} [add_monoid H] {x : H}

open_locale classical

/-- `add_order_of h` is the additive order of the element `x`, i.e. the `n ≥ 1`, s. t. `n •ℕ x = 0`
if it exists. Otherwise, i.e. if `x` is of infinite order, then `add_order_of x` is `0` by
convention.-/
noncomputable def add_order_of (x : H) : ℕ :=
if h : ∃ n, 0 < n ∧ n •ℕ x = 0 then nat.find h else 0

/-- `order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `a ^ n = 1` if it exists.
Otherwise, i.e. if `a` is of infinite order, then `order_of a` is `0` by convention.-/
noncomputable def order_of (a : α) : ℕ :=
if h : ∃ n, 0 < n ∧ a ^ n = 1 then nat.find h else 0

attribute [to_additive add_order_of] order_of

@[simp] lemma add_order_of_of_mul_eq_order_of (a : α) :
  add_order_of (additive.of_mul a) = order_of a :=
by simp [add_order_of, order_of, ← of_mul_pow]

@[simp] lemma order_of_of_add_eq_add_order_of (x : H) :
  order_of (multiplicative.of_add x) = add_order_of x :=
by simp [add_order_of, order_of, ← of_add_nsmul]

lemma add_order_of_pos' {x : H} (h : ∃ n, 0 < n ∧ n •ℕ x = 0) : 0 < add_order_of x :=
begin
  rw add_order_of,
  split_ifs,
  exact (nat.find_spec h).1
end

@[to_additive add_order_of_pos']
lemma order_of_pos' {a : α} (h : ∃ n, 0 < n ∧ a ^ n = 1) : 0 < order_of a :=
begin
  rw order_of,
  split_ifs,
  exact (nat.find_spec h).1
end

lemma pow_order_of_eq_one (a : α): a ^ order_of a = 1 :=
begin
  rw order_of,
  split_ifs with hfin,
  { exact (nat.find_spec hfin).2 },
  { exact pow_zero a }
end

lemma add_order_of_nsmul_eq_zero (x : H) : (add_order_of x) •ℕ x = 0 :=
begin
  apply multiplicative.of_add.injective,
  rw of_add_nsmul,
  exact pow_order_of_eq_one _,
end

attribute [to_additive add_order_of_nsmul_eq_zero] pow_order_of_eq_one

lemma add_order_of_eq_zero {a : H} (h : ∀n, 0 < n → n •ℕ a ≠ 0) : add_order_of a = 0 :=
begin
  rw add_order_of,
  split_ifs with hx,
  { exfalso,
    cases hx with n hn,
    exact (h n) hn.1 hn.2 },
  { refl }
end

@[to_additive add_order_of_eq_zero]
lemma order_of_eq_zero {a : α} (h : ∀n, 0 < n → a ^ n ≠ 1) : order_of a = 0 :=
begin
  rw order_of,
  split_ifs with hx,
  { exfalso,
    cases hx with n hn,
    exact (h n) hn.1 hn.2 },
  { refl }
end

lemma add_order_of_le_of_nsmul_eq_zero' {m : ℕ} (h : m < add_order_of x) : ¬ (0 < m ∧ m •ℕ x = 0) :=
begin
  rw add_order_of at h,
  split_ifs at h with hfin,
  { exact nat.find_min hfin h },
  { exact absurd h m.zero_le.not_lt }
end

@[to_additive add_order_of_le_of_nsmul_eq_zero']
lemma order_of_le_of_pow_eq_one' {m : ℕ} (h : m < order_of a) : ¬ (0 < m ∧ a ^ m = 1) :=
begin
  rw order_of at h,
  split_ifs at h with hfin,
  { exact nat.find_min hfin h },
  { exact absurd h m.zero_le.not_lt }
end

lemma add_order_of_le_of_nsmul_eq_zero {n : ℕ} (hn : 0 < n) (h : n •ℕ x = 0) : add_order_of x ≤ n :=
le_of_not_lt (mt add_order_of_le_of_nsmul_eq_zero' (by simp [hn, h]))

@[to_additive add_order_of_le_of_nsmul_eq_zero]
lemma order_of_le_of_pow_eq_one {n : ℕ} (hn : 0 < n) (h : a ^ n = 1) : order_of a ≤ n :=
le_of_not_lt (mt order_of_le_of_pow_eq_one' (by simp [hn, h]))

@[simp] lemma order_of_one : order_of (1 : α) = 1 :=
begin
  apply le_antisymm,
  { exact order_of_le_of_pow_eq_one (nat.one_pos) (pow_one 1) },
  { exact nat.succ_le_of_lt ( order_of_pos' ⟨1, ⟨nat.one_pos, pow_one 1⟩⟩) }
end

@[simp] lemma add_order_of_zero : add_order_of (0 : H) = 1 :=
by simp [← order_of_of_add_eq_add_order_of]

attribute [to_additive add_order_of_zero] order_of_one

@[simp] lemma order_of_eq_one_iff : order_of a = 1 ↔ a = 1 :=
⟨λ h, by conv_lhs { rw [← pow_one a, ← h, pow_order_of_eq_one] }, λ h, by simp [h]⟩

@[simp] lemma add_order_of_eq_one_iff : add_order_of x = 1 ↔ x = 0 :=
by simp [← order_of_of_add_eq_add_order_of]

attribute [to_additive add_order_of_eq_one_iff] order_of_eq_one_iff

lemma pow_eq_mod_order_of {n : ℕ} : a ^ n = a ^ (n % order_of a) :=
calc a ^ n = a ^ (n % order_of a + order_of a * (n / order_of a)) : by rw [nat.mod_add_div]
       ... = a ^ (n % order_of a) : by simp [pow_add, pow_mul, pow_order_of_eq_one]

lemma nsmul_eq_mod_add_order_of {n : ℕ} : n •ℕ x = (n % add_order_of x) •ℕ x :=
begin
  apply multiplicative.of_add.injective,
  rw [← order_of_of_add_eq_add_order_of, of_add_nsmul, of_add_nsmul, pow_eq_mod_order_of],
end

attribute [to_additive nsmul_eq_mod_add_order_of] pow_eq_mod_order_of

lemma order_of_dvd_of_pow_eq_one {n : ℕ} (h : a ^ n = 1) : order_of a ∣ n :=
begin
  rcases n.zero_le.eq_or_lt with rfl|h₁,
  { simp },
  { apply nat.dvd_of_mod_eq_zero,
    by_contradiction h₂,
    have h₃ : ¬ (0 < n % order_of a ∧ a ^ (n % order_of a) = 1) := order_of_le_of_pow_eq_one'
      ( nat.mod_lt _ ( order_of_pos' ⟨n, h₁, h⟩)),
    push_neg at h₃,
    specialize h₃ (nat.pos_of_ne_zero h₂),
    rw ← pow_eq_mod_order_of at h₃,
    exact h₃ h },
end

lemma add_order_of_dvd_of_nsmul_eq_zero {n : ℕ} (h : n •ℕ x = 0) : add_order_of x ∣ n :=
begin
  apply_fun multiplicative.of_add at h,
  rw ← order_of_of_add_eq_add_order_of,
  rw of_add_nsmul at h,
  exact order_of_dvd_of_pow_eq_one h,
end

attribute [to_additive add_order_of_dvd_of_nsmul_eq_zero] order_of_dvd_of_pow_eq_one

lemma add_order_of_dvd_iff_nsmul_eq_zero {n : ℕ} : add_order_of x ∣ n ↔ n •ℕ x = 0 :=
⟨λ h, by rw [nsmul_eq_mod_add_order_of, nat.mod_eq_zero_of_dvd h, zero_nsmul],
  add_order_of_dvd_of_nsmul_eq_zero⟩

@[to_additive add_order_of_dvd_iff_nsmul_eq_zero]
lemma order_of_dvd_iff_pow_eq_one {n : ℕ} : order_of a ∣ n ↔ a ^ n = 1 :=
⟨λ h, by rw [pow_eq_mod_order_of, nat.mod_eq_zero_of_dvd h, pow_zero], order_of_dvd_of_pow_eq_one⟩

lemma commute.order_of_mul_dvd_lcm (h : commute a b) :
  order_of (a * b) ∣ nat.lcm (order_of a) (order_of b) :=
by rw [order_of_dvd_iff_pow_eq_one, h.mul_pow, order_of_dvd_iff_pow_eq_one.mp
  (nat.dvd_lcm_left _ _), order_of_dvd_iff_pow_eq_one.mp (nat.dvd_lcm_right _ _), one_mul]

lemma add_order_of_eq_prime {p : ℕ} [hp : fact p.prime]
(hg : p •ℕ x = 0) (hg1 : x ≠ 0) : add_order_of x = p :=
(hp.out.2 _ (add_order_of_dvd_of_nsmul_eq_zero hg)).resolve_left (mt add_order_of_eq_one_iff.1 hg1)

@[to_additive add_order_of_eq_prime]
lemma order_of_eq_prime {p : ℕ} [hp : fact p.prime]
  (hg : a^p = 1) (hg1 : a ≠ 1) : order_of a = p :=
(hp.out.2 _ (order_of_dvd_of_pow_eq_one hg)).resolve_left (mt order_of_eq_one_iff.1 hg1)

open nat

-- An example on how to determine the order of an element of a finite group.
example : order_of (-1 : units ℤ) = 2 :=
begin
  haveI : fact (prime 2) := ⟨prime_two⟩,
  exact order_of_eq_prime (by { rw pow_two, simp }) (dec_trivial)
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
begin
  simp_rw ← order_of_dvd_iff_pow_eq_one,
  exact ⟨λ h n, by rw h, λ h, nat.dvd_antisymm ((h _).mpr (dvd_refl _)) ((h _).mp (dvd_refl _))⟩,
end

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

lemma add_order_of_eq_prime_pow {p k : ℕ} (hprime : prime p)
  (hnot : ¬ (p ^ k) •ℕ x = 0) (hfin : (p ^ (k + 1)) •ℕ x = 0) : add_order_of x = p ^ (k + 1) :=
begin
  apply nat.eq_prime_pow_of_dvd_least_prime_pow hprime;
  { rwa add_order_of_dvd_iff_nsmul_eq_zero }
end

@[to_additive add_order_of_eq_prime_pow]
lemma order_of_eq_prime_pow {p k : ℕ} (hprime : prime p)
  (hnot : ¬ a ^ p ^ k = 1) (hfin : a ^ p ^ (k + 1) = 1) : order_of a = p ^ (k + 1) :=
begin
  apply nat.eq_prime_pow_of_dvd_least_prime_pow hprime;
  { rwa order_of_dvd_iff_pow_eq_one }
end

variables (a) {n : ℕ}

lemma order_of_pow' (h : n ≠ 0) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
begin
  apply dvd_antisymm,
  { apply order_of_dvd_of_pow_eq_one,
    rw [← pow_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _), mul_comm,
        nat.mul_div_assoc _ (gcd_dvd_right _ _), pow_mul, pow_order_of_eq_one, one_pow] },
  { have gcd_pos : 0 < gcd (order_of a) n := gcd_pos_of_pos_right _ (nat.pos_of_ne_zero h),
    apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd gcd_pos),
    apply dvd_of_mul_dvd_mul_right gcd_pos,
    rw [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc, nat.div_mul_cancel (gcd_dvd_right _ _),
        mul_comm],
    apply order_of_dvd_of_pow_eq_one,
    rw [pow_mul, pow_order_of_eq_one] }
end

variables (x)

lemma add_order_of_nsmul' (h : n ≠ 0) :
  add_order_of (n •ℕ x) = add_order_of x / gcd (add_order_of x) n :=
by simpa [← order_of_of_add_eq_add_order_of, of_add_nsmul] using order_of_pow' _ h

attribute [to_additive add_order_of_nsmul'] order_of_pow'

variable (n)

lemma order_of_pow'' (h : ∃ n, 0 < n ∧ a ^ n = 1) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
begin
  apply dvd_antisymm,
  { apply order_of_dvd_of_pow_eq_one,
    rw [← pow_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _), mul_comm,
        nat.mul_div_assoc _ (gcd_dvd_right _ _), pow_mul, pow_order_of_eq_one, one_pow] },
  { have gcd_pos : 0 < gcd (order_of a) n := gcd_pos_of_pos_left n (order_of_pos' h),
    apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd gcd_pos),
    apply dvd_of_mul_dvd_mul_right gcd_pos,
    rw [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc,
            nat.div_mul_cancel (gcd_dvd_right _ _), mul_comm],
    apply order_of_dvd_of_pow_eq_one,
    rw [pow_mul, pow_order_of_eq_one] }
end

lemma add_order_of_nsmul'' (h : ∃n, 0 < n ∧ n •ℕ x = 0) :
  add_order_of (n •ℕ x) = add_order_of x / gcd (add_order_of x) n :=
begin
  repeat { rw ← order_of_of_add_eq_add_order_of },
  rwa [of_add_nsmul, order_of_pow''],
end

attribute [to_additive add_order_of_nsmul''] order_of_pow''

end monoid

section cancel_monoid
variables {α} [left_cancel_monoid α] (a)
variables {H : Type u} [add_left_cancel_monoid H] (x : H)

lemma pow_injective_aux {n m : ℕ} (h : n ≤ m)
  (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
by_contradiction $ assume ne : n ≠ m,
  have h₁ : m - n > 0, from nat.pos_of_ne_zero (by simp [nat.sub_eq_iff_eq_add h, ne.symm]),
  have h₂ : m = n + (m - n) := (nat.add_sub_of_le h).symm,
  have h₃ : a ^ (m - n) = 1,
    by { rw [h₂, pow_add] at eq, apply mul_left_cancel, convert eq.symm, exact mul_one (a ^ n) },
  have le : order_of a ≤ m - n, from order_of_le_of_pow_eq_one h₁ h₃,
  have lt : m - n < order_of a,
    from (nat.sub_lt_left_iff_lt_add h).mpr $ nat.lt_add_left _ _ _ hm,
  lt_irrefl _ (lt_of_le_of_lt le lt)

-- TODO: This lemma was originally private, but this doesn't seem to work with `to_additive`,
-- therefore the private got removed.
lemma nsmul_injective_aux {n m : ℕ} (h : n ≤ m)
  (hm : m < add_order_of x) (eq : n •ℕ x = m •ℕ x) : n = m :=
begin
  apply_fun multiplicative.of_add at eq,
  rw [of_add_nsmul, of_add_nsmul] at eq,
  rw ← order_of_of_add_eq_add_order_of at hm,
  exact pow_injective_aux (multiplicative.of_add x) h hm eq,
end

attribute [to_additive nsmul_injective_aux] pow_injective_aux

lemma nsmul_injective_of_lt_add_order_of {n m : ℕ}
  (hn : n < add_order_of x) (hm : m < add_order_of x) (eq : n •ℕ x = m •ℕ x) : n = m :=
(le_total n m).elim
  (assume h, nsmul_injective_aux x h hm eq)
  (assume h, (nsmul_injective_aux x h hn eq.symm).symm)

@[to_additive nsmul_injective_of_lt_add_order_of]
lemma pow_injective_of_lt_order_of {n m : ℕ}
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
(le_total n m).elim
  (assume h, pow_injective_aux a h hm eq)
  (assume h, (pow_injective_aux a h hn eq.symm).symm)

end cancel_monoid

section group
variables {α} [group α] {a}
variables {H : Type u} [add_group H] {x : H}


lemma gpow_eq_mod_order_of {i : ℤ} : a ^ i = a ^ (i % order_of a) :=
calc a ^ i = a ^ (i % order_of a + order_of a * (i / order_of a)) :
    by rw [int.mod_add_div]
       ... = a ^ (i % order_of a) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]

lemma gsmul_eq_mod_add_order_of {i : ℤ} : i •ℤ x = (i % add_order_of x) •ℤ x :=
begin
  apply multiplicative.of_add.injective,
  simp [of_add_gsmul, gpow_eq_mod_order_of],
end

attribute [to_additive gsmul_eq_mod_add_order_of] gpow_eq_mod_order_of

end group

section finite_monoid
variables {α} [fintype α] [monoid α]
variables {H : Type u} [fintype H] [add_monoid H]

lemma sum_card_add_order_of_eq_card_nsmul_eq_zero [decidable_eq H] {n : ℕ} (hn : 0 < n) :
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
lemma sum_card_order_of_eq_card_pow_eq_one [decidable_eq α] {n : ℕ} (hn : 0 < n) :
  ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ a : α, order_of a = m)).card
  = (finset.univ.filter (λ a : α, a ^ n = 1)).card :=
calc ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ a : α, order_of a = m)).card
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
/-- TODO: Of course everything also works for right_cancel_monoids. -/
variables {α} [fintype α] [left_cancel_monoid α]
variables {H : Type u} [fintype H] [add_left_cancel_monoid H]

/-- TODO: Use this to show that a finite left cancellative monoid is a group.-/
lemma exists_pow_eq_one (a : α) : ∃i, 0 < i ∧ a ^ i = 1 :=
begin
  have h : ¬ injective (λi:ℕ, a^i) := not_injective_infinite_fintype _,
  have h' : ∃(i j : ℕ), a ^ i = a ^ j ∧ i ≠ j,
  { rw injective at h,
    simp only [not_forall, exists_prop] at h,
    exact h },
  rcases h' with ⟨i, j, a_eq, ne⟩,
  wlog h'' : j ≤ i,
  have h''' : a ^ (i - j) = 1,
  { rw [(nat.add_sub_of_le h'').symm, pow_add, ← mul_one (a ^ j), mul_assoc] at a_eq,
    convert mul_left_cancel a_eq,
    rw one_mul },
  use (i - j),
  split,
  { apply lt_of_le_of_ne (zero_le (i - j)),
    by_contradiction,
    rw not_not at h,
    apply ne,
    rw [(nat.add_sub_of_le h'').symm, ← h, add_zero] },
  { exact h''' },
end

lemma exists_nsmul_eq_zero (x : H) : ∃ i, 0 < i ∧ i •ℕ x = 0 :=
begin
  rcases exists_pow_eq_one (multiplicative.of_add x) with ⟨i, hi1, hi2⟩,
  refine ⟨i, hi1, multiplicative.of_add.injective _⟩,
  rw [of_add_nsmul, hi2, of_add_zero],
end

attribute [to_additive exists_nsmul_eq_zero] exists_pow_eq_one

lemma add_order_of_le_card_univ {x : H} : add_order_of x ≤ fintype.card H :=
finset.le_card_of_inj_on_range (•ℕ x)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, nsmul_injective_of_lt_add_order_of x hi hj)

@[to_additive add_order_of_le_card_univ]
lemma order_of_le_card_univ {a : α} : order_of a ≤ fintype.card α :=
finset.le_card_of_inj_on_range ((^) a)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, pow_injective_of_lt_order_of a hi hj)

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
lemma order_of_pos (a : α) : 0 < order_of a := order_of_pos' (exists_pow_eq_one a)

/-- This is the same as `add_order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative additive monoid.-/
lemma add_order_of_pos (x : H) : 0 < add_order_of x :=
begin
  rw ← order_of_of_add_eq_add_order_of,
  exact order_of_pos _,
end

attribute [to_additive add_order_of_pos] order_of_pos

variables {n : ℕ}

open nat

lemma exists_pow_eq_self_of_coprime {α : Type*} [monoid α] {a : α} (h : coprime n (order_of a)) :
  ∃ m : ℕ, (a ^ n) ^ m = a :=
begin
  by_cases h0 : order_of a = 0,
  { rw [h0, coprime_zero_right] at h,
    exact ⟨1, by rw [h, pow_one, pow_one]⟩ },
  by_cases h1 : order_of a = 1,
  { rw order_of_eq_one_iff at h1,
    exact ⟨37, by rw [h1, one_pow, one_pow]⟩ },
  obtain ⟨m, hm⟩ :=
    exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩),
  exact ⟨m, by rw [←pow_mul, pow_eq_mod_order_of, hm, pow_one]⟩,
end

lemma exists_nsmul_eq_self_of_coprime {H : Type*} [add_monoid H] (x : H)
  (h : coprime n (add_order_of x)) : ∃ m : ℕ, m •ℕ (n •ℕ x) = x :=
begin
  have h' : coprime n (order_of (multiplicative.of_add x)),
  { simp_rw order_of_of_add_eq_add_order_of,
    exact h },
  cases exists_pow_eq_self_of_coprime h' with m hpow,
  use m,
  apply multiplicative.of_add.injective,
  simpa [of_add_nsmul],
end

attribute [to_additive exists_nsmul_eq_self_of_coprime] exists_pow_eq_self_of_coprime

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid.-/
lemma order_of_pow (a : α) :
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

lemma mem_multiples_iff_mem_range_add_order_of [decidable_eq H] {x x' : H} :
  x' ∈ add_submonoid.multiples x ↔
  x' ∈ (finset.range (add_order_of x)).image ((•ℕ x) : ℕ → H)  :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (add_order_of_pos x)
  (assume i, nsmul_eq_mod_add_order_of.symm)

@[to_additive mem_multiples_iff_mem_range_add_order_of]
lemma mem_powers_iff_mem_range_order_of [decidable_eq α] {a a' : α} :
  a' ∈ submonoid.powers a ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → α) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos a)
  (assume i, pow_eq_mod_order_of.symm)

noncomputable instance decidable_multiples [decidable_eq H] {x : H} :
  decidable_pred (add_submonoid.multiples x : set H) :=
begin
  assume x',
  apply decidable_of_iff' (x' ∈ (finset.range (add_order_of x)).image (•ℕ x)),
  exact mem_multiples_iff_mem_range_add_order_of,
end

@[to_additive decidable_multiples]
noncomputable instance decidable_powers [decidable_eq α] :
  decidable_pred (submonoid.powers a : set α) :=
begin
  assume a',
  apply decidable_of_iff'
    (a' ∈ (finset.range (order_of a)).image ((^) a)),
  exact mem_powers_iff_mem_range_order_of
end

lemma order_eq_card_powers [decidable_eq α] {a : α} :
  order_of a = fintype.card (submonoid.powers a : set α) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨a ^ n, ⟨n, rfl⟩⟩ },
  { rintros ⟨_, i, rfl⟩ _,
    exact ⟨i % order_of a, mod_lt i (order_of_pos a), subtype.eq pow_eq_mod_order_of.symm⟩ },
  { intros, exact finset.mem_univ _ },
  { intros i j hi hj eq,
    exact pow_injective_of_lt_order_of a hi hj ( by simpa using eq ) }
end

lemma add_order_of_eq_card_multiples [decidable_eq H] {x : H} :
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
variables {α} [fintype α] [group α]
variables {H : Type u} [fintype H] [add_group H]

lemma exists_gpow_eq_one (a : α) : ∃ i ≠ 0, a ^ (i : ℤ) = 1 :=
begin
  rcases exists_pow_eq_one a with ⟨w, hw1, hw2⟩,
  use w,
  split,
  { exact_mod_cast ne_of_gt hw1 },
  { exact_mod_cast hw2 }
end

lemma exists_gsmul_eq_zero (x : H) : ∃ i ≠ 0, i •ℤ x = 0 :=
begin
  rcases exists_gpow_eq_one (multiplicative.of_add x) with ⟨i, hi1, hi2⟩,
  refine ⟨i, hi1, multiplicative.of_add.injective _⟩,
  { rw [of_add_gsmul, hi2, of_add_zero] }
end

attribute [to_additive exists_gsmul_eq_zero] exists_gpow_eq_one

lemma mem_multiples_iff_mem_gmultiples {x y : H} :
  y ∈ add_submonoid.multiples x ↔ y ∈ add_subgroup.gmultiples x :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩, λ ⟨i, hi⟩, ⟨(i % add_order_of x).nat_abs,
  by { simp only at hi ⊢,
       rwa  [← gsmul_coe_nat,
       int.nat_abs_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.2
          (add_order_of_pos x))), ← gsmul_eq_mod_add_order_of] } ⟩⟩

open subgroup

@[to_additive mem_multiples_iff_mem_gmultiples]
lemma mem_powers_iff_mem_gpowers {a x : α} : x ∈ submonoid.powers a ↔ x ∈ gpowers a :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩,
λ ⟨i, hi⟩, ⟨(i % order_of a).nat_abs,
  by rwa [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
    (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos a))),
    ← gpow_eq_mod_order_of]⟩⟩

lemma multiples_eq_gmultiples (x : H) :
  (add_submonoid.multiples x : set H) = add_subgroup.gmultiples x :=
set.ext $ λ y, mem_multiples_iff_mem_gmultiples

@[to_additive multiples_eq_gmultiples]
lemma powers_eq_gpowers (a : α) : (submonoid.powers a : set α) = gpowers a :=
set.ext $ λ x, mem_powers_iff_mem_gpowers

lemma mem_gmultiples_iff_mem_range_add_order_of [decidable_eq H] {x x' : H} :
  x' ∈ add_subgroup.gmultiples x ↔ x' ∈ (finset.range (add_order_of x)).image (•ℕ x) :=
by rw [← mem_multiples_iff_mem_gmultiples, mem_multiples_iff_mem_range_add_order_of]

@[to_additive mem_gmultiples_iff_mem_range_add_order_of]
lemma mem_gpowers_iff_mem_range_order_of [decidable_eq α] {a a' : α} :
  a' ∈ subgroup.gpowers a ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → α) :=
by rw [← mem_powers_iff_mem_gpowers, mem_powers_iff_mem_range_order_of]

noncomputable instance decidable_gmultiples [decidable_eq H] {x : H}:
  decidable_pred (add_subgroup.gmultiples x : set H) :=
begin
  rw ← multiples_eq_gmultiples,
  exact decidable_multiples,
end

@[to_additive decidable_gmultiples]
noncomputable instance decidable_gpowers [decidable_eq α] :
  decidable_pred (subgroup.gpowers a : set α) :=
begin
  rw ← powers_eq_gpowers,
  exact decidable_powers,
end

lemma order_eq_card_gpowers [decidable_eq α] {a : α} :
  order_of a = fintype.card (subgroup.gpowers a : set α) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨a ^ (n : ℤ), ⟨n, rfl⟩⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
    have pos : (0 : ℤ) < order_of a := int.coe_nat_lt.mpr $ order_of_pos a,
    have 0 ≤ i % (order_of a) := int.mod_nonneg _ $ ne_of_gt pos,
    ⟨int.to_nat (i % order_of a),
      by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
        exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { intros, exact finset.mem_univ _ },
  { exact assume i j hi hj eq, pow_injective_of_lt_order_of a hi hj $ by simpa using eq }
end

lemma add_order_eq_card_gmultiples [decidable_eq H] {x : H} :
  add_order_of x = fintype.card (add_subgroup.gmultiples x : set H) :=
begin
  rw [← order_of_of_add_eq_add_order_of, order_eq_card_gpowers],
  apply fintype.card_congr,
  rw ← of_add_image_gmultiples_eq_gpowers_of_add,
  exact (equiv.set.image _ _ (equiv.injective _)).symm
end

attribute [to_additive add_order_eq_card_gmultiples] order_eq_card_gpowers

open quotient_group subgroup

/- TODO: use cardinal theory, introduce `card : set α → ℕ`, or setup decidability for cosets -/
lemma order_of_dvd_card_univ : order_of a ∣ fintype.card α :=
begin
  classical,
  have ft_prod : fintype (quotient (gpowers a) × (gpowers a)),
    from fintype.of_equiv α group_equiv_quotient_times_subgroup,
  have ft_s : fintype (gpowers a),
    from @fintype.fintype_prod_right _ _ _ ft_prod _,
  have ft_cosets : fintype (quotient (gpowers a)),
    from @fintype.fintype_prod_left _ _ _ ft_prod ⟨⟨1, (gpowers a).one_mem⟩⟩,
  have eq₁ : fintype.card α = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
    from calc fintype.card α = @fintype.card _ ft_prod :
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

lemma add_order_of_dvd_card_univ {x : H} : add_order_of x ∣ fintype.card H :=
begin
  rw ← order_of_of_add_eq_add_order_of,
  exact order_of_dvd_card_univ,
end

attribute [to_additive add_order_of_dvd_card_univ] order_of_dvd_card_univ

@[simp] lemma pow_card_eq_one {a : α} : a ^ fintype.card α = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ a _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]

@[simp] lemma card_nsmul_eq_zero {x : H} : fintype.card H •ℕ x = 0 :=
begin
  apply multiplicative.of_add.injective,
  rw [of_add_nsmul, of_add_zero],
  exact pow_card_eq_one,
end

attribute [to_additive card_nsmul_eq_zero] pow_card_eq_one

variable (a)

lemma image_range_add_order_of [decidable_eq H] {x : H} :
  finset.image (λ i, i •ℕ x) (finset.range (add_order_of x)) =
  (add_subgroup.gmultiples x : set H).to_finset :=
by {ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_gmultiples_iff_mem_range_add_order_of] }

/-- TODO: Generalise to `submonoid.powers`.-/
@[to_additive image_range_add_order_of]
lemma image_range_order_of [decidable_eq α] :
  finset.image (λ i, a ^ i) (finset.range (order_of a)) = (gpowers a : set α).to_finset :=
by { ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_gpowers_iff_mem_range_order_of] }

open nat

lemma gcd_nsmul_card_eq_zero_iff {x : H} {n : ℕ} :
  n •ℕ x = 0 ↔ (gcd n (fintype.card H)) •ℕ x = 0 :=
⟨λ h, gcd_nsmul_eq_zero _ h $ card_nsmul_eq_zero,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card H) in
    by rw [hm, mul_comm, mul_nsmul, h, nsmul_zero]⟩

/-- TODO: Generalise to `finite_cancel_monoid`. -/
@[to_additive gcd_nsmul_card_eq_zero_iff]
lemma pow_gcd_card_eq_one_iff {n : ℕ} :
  a ^ n = 1 ↔ a ^ (gcd n (fintype.card α)) = 1 :=
⟨λ h, pow_gcd_eq_one _ h $ pow_card_eq_one,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card α) in
    by rw [hm, pow_mul, h, one_pow]⟩

end finite_group

end order_of
