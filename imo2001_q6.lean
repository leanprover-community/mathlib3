/-
Copyright (c) 2021 Sara Díaz Real. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sara Díaz Real
-/
import data.int.basic
import tactic
import algebra.associated

/-!
# IMO 2001 Q6
Let a, b, c, d be integers with a > b > c > d > 0. Suppose that

$$
a*c + b*d = (b*d + a*c) * (b*d + a*c).
$$

Prove that a*b + c*d is not prime.
-/

/-
The main idea of this formalization is using the negation
introduction, that is, we are going to suppose that the number
a*b+c*d  is prime.

However, firstly we have to prove some auxiliar results that
will be used in the final theorem.
-/



variables {a b c d : ℤ}


/-!
## Intermediate lemmas
-/

lemma equivalent_sums
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : b^2 + b*d + d^2 = a^2 - a*c + c^2 :=
begin
  have h1: (a + b - c + d) * (-a + b + c + d) =
           -a^2  + b^2  + a*c - c^2 + b*d + d^2 + a*c + b*d,
    by ring,
  by nlinarith,
end

lemma equivalent_products
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : (a*c + b*d) * (b^2 + b*d + d^2) = (a*b + c*d) * (a*d + b*c) :=
begin
  have h1: (a*c + b*d) * (b^2 + b*d + d^2) =
           a*c * (b^2 + b*d + d^2) + b*d * (b^2 + b*d + d^2),
    by ring,
  have h2: a*c * (b^2 + b*d + d^2) + b*d * (b^2 + b*d + d^2) =
           a*c * (b^2 + b*d + d^2) + b*d * (a^2 - a*c + c^2),
    by rw equivalent_sums h,
  by nlinarith,
end

lemma auxiliar_inequality1
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : a*c + b*d < a*b + c*d:=
by nlinarith

lemma auxiliar_inequality2
  (hba : b < a)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c + d)*(-a + b + c + d))
  : a*d + b*c < a*c + b*d:=
by nlinarith

lemma auxiliar_split
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : a*c + b*d ∣ (a*b+c*d) * (a*d+b*c):=
by exact ⟨b^2 + b*d +d^2, by nlinarith [equivalent_products h]⟩

/-!
## The question
-/


theorem imo2001_q6
  (hd  : 0 < d)
  (hdc : d < c)
  (hcb : c < b)
  (hba : b < a)
  (h : a*c + b*d = (a + b - c + d)*(-a + b + c + d))
  : ¬ prime (a*b + c*d) :=
begin
  intro h1,
  have ha : 0 < a, by linarith,
  have hb : 0 < b, by linarith,
  have hc : 0 < c, by linarith,
  have h2 : (a*c + b*d) * (b^2 + b*d + d^2) =
            (a*b + c*d) * (a*d + b*c),
    from equivalent_products h,
  have h3 : a*c + b*d ∣ (a*b + c*d) * (a*d + b*c),
    from auxiliar_split h,
  have h4: (a*b + c*d ∣ a*c + b*d) ∨ (a*c + b*d  ∣ a*d + b*c),
    from left_dvd_or_dvd_right_of_dvd_prime_mul h1 h3,
  cases h4 with hj hk,
  { have hj1: a*b + c*d > a*c + b*d,
      from auxiliar_inequality1 hba hcb hdc h,
    have hpj: 0 < a*c + b*d,
      from add_pos (mul_pos ha hc) (mul_pos hb hd),
    have hj2: a*b + c*d ≤ a*c + b*d,
      from int.le_of_dvd hpj hj,
    have hj3: ¬ (a*b + c*d ≤ a*c + b*d),
      from not_le.mpr hj1,
    exact hj3 hj2, },
  { have hk1: a*c + b*d > a*d + b*c,
      from auxiliar_inequality2 hba hdc h,
    have hpk: 0 < a*d + b*c,
      from add_pos (mul_pos ha hd) (mul_pos hb hc),
    have hk2: a*c + b*d ≤ a*d + b*c,
      from int.le_of_dvd hpk hk,
    have hk3: ¬ (a*c+b*d ≤  a*d+b*c),
      from not_le.mpr hk1,
    exact hk3 hk2, },
end
