/-
Copyright (c) 2021 Sara Díaz Real. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sara Díaz Real
-/
import data.int.basic
import tactic.linarith
import tactic.ring
import algebra.associated

/-!
# IMO 2001 Q6
Let $a$, $b$, $c$, $d$ be integers with $a > b > c > d > 0$. Suppose that

$$ a*c + b*d = (b*d + a*c) * (b*d + a*c). $$

Prove that $a*b + c*d$ is not prime.

## Strategy

The main idea of this formalization is by contradiction,
that is, we are going to suppose that the number
$a*b+c*d$  is prime.

However, firstly we have to prove an auxiliary results that
will be used in the final theorem.
-/

variables {a b c d : ℤ}

lemma auxiliary_split (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d)) :
  a*c + b*d ∣ (a*b+c*d) * (a*d+b*c) :=
begin
  use b^2 + b*d + d^2,
  have equivalent_sums : a^2 - a*c + c^2 = b^2 + b*d + d^2,
  { ring_nf at h, nlinarith, },
  calc  (a * b + c * d) * (a * d + b * c)
      = a*c * (b^2 + b*d + d^2) + b*d * (a^2 - a*c + c^2) : by ring
  ... = a*c * (b^2 + b*d + d^2) + b*d * (b^2 + b*d + d^2) : by rw equivalent_sums
  ... = (a * c + b * d) * (b ^ 2 + b * d + d ^ 2)         : by ring,
end

theorem imo2001_q6 (hd : 0 < d) (hdc : d < c) (hcb : c < b) (hba : b < a)
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d)) :
  ¬ prime (a*b + c*d) :=
begin
  assume h1 : prime (a*b + c*d),
  have ha : 0 < a, by linarith,
  have hb : 0 < b, by linarith,
  have hc : 0 < c, by linarith,
  have h3 : a*c + b*d ∣ (a*b + c*d) * (a*d + b*c), from auxiliary_split h,
  obtain (hj|hk) : (a*b + c*d ∣ a*c + b*d) ∨ (a*c + b*d ∣ a*d + b*c),
    from left_dvd_or_dvd_right_of_dvd_prime_mul h1 h3,
  { have hj1 : a*b + c*d > a*c + b*d, by nlinarith only [hba, hcb, hdc, h],
    have hpj : 0 < a*c + b*d,         by nlinarith only [ha, hb, hc, hd],
    have hj2 : a*b + c*d ≤ a*c + b*d, from int.le_of_dvd hpj hj,
    linarith, },
  { have hk1 : a*c + b*d > a*d + b*c, by nlinarith only [hba, hdc, h],
    have hpk : 0 < a*d + b*c,         by nlinarith only [ha, hb, hc, hd],
    have hk2 : a*c + b*d ≤ a*d + b*c, from int.le_of_dvd hpk hk,
    linarith, },
end
