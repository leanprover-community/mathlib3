/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.char_p.basic
import tactic.interval_cases

/-!
# Lemmas about rings of characteristic two

This file contains results about `char_p R 2`, in the `char_two` namespace.
-/

variables {R ι : Type*}

namespace char_two

lemma two_eq_zero [semiring R] [char_p R 2] : (2 : R) = 0 :=
by rw [← nat.cast_two, char_p.cast_eq_zero]

lemma bit0_eq_zero [semiring R] [char_p R 2] (x : R) : (bit0 x : R) = 0 :=
by rw [bit0, ←two_smul R x, two_eq_zero, zero_smul]

lemma neg_eq [ring R] [char_p R 2] (x : R) : -x = x :=
by rw [neg_eq_iff_add_eq_zero, ←two_smul R x, two_eq_zero, zero_smul]

lemma one_eq_neg_iff {R} [ring R] [nontrivial R] : ring_char R = 2 ↔ (-1 : R) = 1 :=
begin
  refine ⟨λ h, @@neg_eq _ (ring_char.of_eq h) 1, λ h, _⟩,
  rw [eq_comm, ←sub_eq_zero, sub_neg_eq_add, show (1 + 1 : R) = (1 + 1 : ℕ), by norm_cast] at h,
  have := nat.le_of_dvd zero_lt_two (ring_char.dvd h),
  interval_cases (ring_char R) with hrc,
  { haveI := ring_char.eq_iff.mp hrc,
    haveI := char_p.char_p_to_char_zero R,
    apply false.elim (@two_ne_zero' R _ _ _ _),
    exact_mod_cast h },
  { have := @char_p.ring_char_ne_one R _ _, contradiction },
  { assumption }
end

lemma nat.fact_prime_two : fact (nat.prime 2) := ⟨nat.prime_two⟩

local attribute [instance] nat.fact_prime_two

@[simp] lemma order_of_neg_one {R} [ring R] [nontrivial R] :
  order_of (-1 : R) = if ring_char R = 2 then 1 else 2 :=
begin
  split_ifs,
  { simpa [one_eq_neg_iff] using h },
  apply order_of_eq_prime,
  { simp },
  simpa [one_eq_neg_iff] using h
end

lemma sub_eq_add [ring R] [char_p R 2] (x y : R) : x - y = x + y :=
by rw [sub_eq_add_neg, neg_eq]

lemma sub_eq_add' [ring R] [char_p R 2] : has_sub.sub = ((+) : R → R → R) :=
funext $ λ x, funext $ λ y, sub_eq_add x y

lemma add_sq [comm_semiring R] [char_p R 2] (x y : R) :
  (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
begin
  letI := fact.mk nat.prime_two,
  exact add_pow_char _ _ _
end

lemma add_mul_self [comm_semiring R] [char_p R 2] (x y : R) :
  (x + y) * (x + y) = x * x + y * y :=
by rw [←pow_two, ←pow_two, ←pow_two, add_sq]

open_locale big_operators

lemma sum_sq [comm_semiring R] [char_p R 2] (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 :=
begin
  letI := fact.mk nat.prime_two,
  exact sum_pow_char _ _ _
end

lemma sum_mul_self [comm_semiring R] [char_p R 2] (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) * (∑ i in s, f i) = ∑ i in s, f i * f i :=
by simp_rw [←pow_two, sum_sq]

end char_two
