/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.char_p.basic

variables {R ι : Type*}

/-!
# Lemmas about rings of characteristic two

-/

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

lemma add_mul_self [comm_semiring R] [char_p R 2] (x y : R) :
  (x + y) * (x + y) = x * x + y * y :=
by rw [add_mul_self_eq, two_eq_zero, zero_mul, zero_mul, add_zero]

open_locale big_operators

lemma sum_mul_self [fintype ι] [comm_semiring R] [char_p R 2] (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) * (∑ i in s, f i) = ∑ i in s, f i * f i :=
begin
  classical,
  induction s using finset.induction with i s hs ih,
  { simp, },
  { rw [finset.sum_insert hs, finset.sum_insert hs, add_mul_self, ←ih] }
end

end char_two
