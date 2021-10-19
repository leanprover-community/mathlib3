/-
Copyright (c) 2021 Sara Díaz Real. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sara Díaz Real
-/
import data.int.basic
import algebra.associated
import tactic.linarith
import tactic.ring

/-!
# IMO 2001 Q6
Let $a$, $b$, $c$, $d$ be integers with $a > b > c > d > 0$. Suppose that

$$ a*c + b*d = (a + b - c + d) * (-a + b + c + d). $$

Prove that $a*b + c*d$ is not prime.

-/

variables {a b c d : ℤ}

theorem imo2001_q6 (hd : 0 < d) (hdc : d < c) (hcb : c < b) (hba : b < a)
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d)) :
  ¬ prime (a*b + c*d) :=
begin
  assume h0 : prime (a*b + c*d),
  have ha : 0 < a, { linarith },
  have hb : 0 < b, { linarith },
  have hc : 0 < c, { linarith },
  -- the key step is to show that `a*c + b*d` divides the product `(a*b + c*d) * (a*d + b*c)`
  have dvd_mul : a*c + b*d ∣ (a*b + c*d) * (a*d + b*c),
  { use b^2 + b*d + d^2,
    have equivalent_sums : a^2 - a*c + c^2 = b^2 + b*d + d^2,
    { ring_nf at h, nlinarith only [h], },
    calc  (a * b + c * d) * (a * d + b * c)
        = a*c * (b^2 + b*d + d^2) + b*d * (a^2 - a*c + c^2) : by ring
    ... = a*c * (b^2 + b*d + d^2) + b*d * (b^2 + b*d + d^2) : by rw equivalent_sums
    ... = (a * c + b * d) * (b ^ 2 + b * d + d ^ 2)         : by ring, },
  -- since `a*b + c*d` is prime (by assumption), it must divide `a*c + b*d` or `a*d + b*c`
  obtain (h1 : a*b + c*d ∣ a*c + b*d) | (h2 : a*c + b*d ∣ a*d + b*c) :=
    h0.left_dvd_or_dvd_right_of_dvd_mul dvd_mul,
  -- in both cases, we derive a contradiction
  { have aux : 0 < a*c + b*d,         { nlinarith only [ha, hb, hc, hd] },
    have : a*b + c*d ≤ a*c + b*d,     { from int.le_of_dvd aux h1 },
    have : ¬ (a*b + c*d ≤ a*c + b*d), { nlinarith only [hba, hcb, hdc, h] },
    contradiction, },
  { have aux : 0 < a*d + b*c,         { nlinarith only [ha, hb, hc, hd] },
    have : a*c + b*d ≤ a*d + b*c,     { from int.le_of_dvd aux h2 },
    have : ¬ (a*c + b*d ≤ a*d + b*c), { nlinarith only [hba, hdc, h] },
    contradiction, },
end
