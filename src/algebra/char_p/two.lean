/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.char_p.basic

/-!
# Lemmas about rings of characteristic two

This file contains results about `char_p R 2`, in the `char_two` namespace.
-/

variables {R ι : Type*}

local attribute [fact] nat.fact_prime_two

namespace char_two

lemma two_eq_zero [semiring R] [char_p R 2] : (2 : R) = 0 :=
by rw [← nat.cast_two, char_p.cast_eq_zero]

lemma bit0_eq_zero [semiring R] [char_p R 2] (x : R) : (bit0 x : R) = 0 :=
by rw [bit0, ←two_smul R x, two_eq_zero, zero_smul]

lemma neg_eq [ring R] [char_p R 2] (x : R) : -x = x :=
by rw [neg_eq_iff_add_eq_zero, ←two_smul R x, two_eq_zero, zero_smul]

lemma sub_eq_add [ring R] [char_p R 2] (x y : R) : x - y = x + y :=
by rw [sub_eq_add_neg, neg_eq]

lemma sub_eq_add' [ring R] [char_p R 2] : has_sub.sub = ((+) : R → R → R) :=
funext $ λ x, funext $ λ y, sub_eq_add x y

lemma add_sq [comm_semiring R] [char_p R 2] (x y : R) :
  (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
add_pow_char _ _ _

lemma add_mul_self [comm_semiring R] [char_p R 2] (x y : R) :
  (x + y) * (x + y) = x * x + y * y :=
by rw [←pow_two, ←pow_two, ←pow_two, add_sq]

open_locale big_operators

lemma sum_sq [comm_semiring R] [char_p R 2] (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 :=
sum_pow_char _ _ _

lemma sum_mul_self [comm_semiring R] [char_p R 2] (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) * (∑ i in s, f i) = ∑ i in s, f i * f i :=
by simp_rw [←pow_two, sum_sq]

end char_two
