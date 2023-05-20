/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import number_theory.zsqrtd.gaussian_int
import tactic.linear_combination

/-!
# Sums of two squares

Proof of Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares.

# Todo

Fully characterize the natural numbers that are the sum of two squares: those such that for every
prime p congruent to 3 mod 4, the largest power of p dividing them is even.
-/

section Fermat

open gaussian_int

/-- **Fermat's theorem on the sum of two squares**. Every prime not congruent to 3 mod 4 is the sum
of two squares. Also known as **Fermat's Christmas theorem**. -/
theorem nat.prime.sq_add_sq {p : ℕ} [pp : fact (nat.prime p)] (hp : p % 4 ≠ 3) :
  ∃ (a b : ℕ), a ^ 2 + b ^ 2 = p :=
begin
  unfreezingI {rcases pp.1.eq_two_or_odd with rfl | h},
  { exact ⟨1, 1, rfl⟩, },
  { apply sq_add_sq_of_nat_prime_of_not_irreducible p,
    rwa [principal_ideal_ring.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p], }
end

end Fermat

/-!
### Generalities on sums of two squares
-/

section general

/-- The set of sums of two squares is closed under multiplication in any commutative ring.
See also `sq_add_sq_mul_sq_add_sq`. -/
lemma sq_add_sq_mul {R} [comm_ring R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
  (hb : b = u ^ 2 + v ^ 2) : ∃ r s : R, a * b = r ^ 2 + s ^ 2 :=
⟨x * u - y * v, x * v + y * u, by {rw [ha, hb], ring}⟩

/-- The set of naturals numbers that are sums of two squqares is closed under multiplication. -/
lemma nat.sq_add_sq_mul {a b x y u v : ℕ} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
  ∃ r s : ℕ, a * b = r ^ 2 + s ^ 2 :=
begin
  zify at ha hb ⊢,
  obtain ⟨r, s, h⟩ := sq_add_sq_mul ha hb,
  refine ⟨r.nat_abs, s.nat_abs, _⟩,
  simpa only [int.coe_nat_abs, sq_abs],
end

end general

/-!
### Results on when -1 is a square modulo a natural number
-/

section neg_one_square

/-- If `-1` is a square modulo `n` and `m` divides `n`, then `-1` is also a square modulo `m`. -/
-- This could be formulated for a general integer `a` in place of `-1`,
-- but it would not directly specialize to `-1`,
-- because `((-1 : ℤ) : zmod n)` is not the same as `(-1 : zmod n)`.
lemma zmod.is_square_cast_neg_one {m n : ℕ} (hd : m ∣ n) (hs : is_square (-1 : zmod n)) :
  is_square (-1 : zmod m) :=
begin
  let f : zmod n →+* zmod m := zmod.cast_hom hd _,
  rw [← ring_hom.map_one f, ← ring_hom.map_neg],
  exact hs.map f,
end

/-- If `-1` is a square modulo coprime natural numbers `m` and `n`, then `-1` is also
a square modulo `m*n`. -/
-- A similar comment applies here.
lemma zmod.is_square_neg_one_mul {m n : ℕ} (hc : m.coprime n) (hm : is_square (-1 : zmod m))
  (hn : is_square (-1 : zmod n)) : is_square (-1 : zmod (m * n)) :=
begin
  have : is_square (-1 : (zmod m) × (zmod n)),
  { rw show (-1 : (zmod m) × (zmod n)) = ((-1 : zmod m), (-1 : zmod n)), from rfl,
    obtain ⟨x, hx⟩ := hm,
    obtain ⟨y, hy⟩ := hn,
    rw [hx, hy],
    exact ⟨(x, y), rfl⟩, },
  simpa only [ring_equiv.map_neg_one] using this.map (zmod.chinese_remainder hc).symm,
end

/-- If a prime `p` divides `n` such that `-1` is a square modulo `n`, then `p % 4 ≠ 3`. -/
lemma nat.prime.mod_four_ne_three_of_dvd_is_square_neg_one {p n : ℕ} (hpp: p.prime) (hp : p ∣ n)
  (hs : is_square (-1 : zmod n)) : p % 4 ≠ 3 :=
begin
  obtain ⟨y, h⟩ := zmod.is_square_cast_neg_one hp hs,
  rw [← sq, eq_comm, show (-1 : zmod p) = -1 ^ 2, from by ring] at h,
  haveI : fact p.prime := ⟨hpp⟩,
  exact zmod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero h,
end

/-- If `n` is a squarefree natural number, then `-1` is a square modulo `n` if and only if
`n` is not divisible by a prime `q` such that `q % 4 = 3`. -/
lemma zmod.is_square_neg_one_iff {n : ℕ} (hn : squarefree n) :
  is_square (-1 : zmod n) ↔ ∀ q : ℕ, q.prime → q ∣ n → q % 4 ≠ 3 :=
begin
  refine ⟨λ H q hqp hqd, hqp.mod_four_ne_three_of_dvd_is_square_neg_one hqd H, λ H, _⟩,
  induction n using induction_on_primes with p n hpp ih,
  { exact false.elim (hn.ne_zero rfl), },
  { exact ⟨0, by simp only [fin.zero_mul, neg_eq_zero, fin.one_eq_zero_iff]⟩, },
  { haveI : fact p.prime := ⟨hpp⟩,
    have hcp : p.coprime n,
    { by_contra hc,
      exact hpp.not_unit (hn p $ mul_dvd_mul_left p $ hpp.dvd_iff_not_coprime.mpr hc), },
    have hp₁ := zmod.exists_sq_eq_neg_one_iff.mpr (H p hpp (dvd_mul_right p n)),
    exact zmod.is_square_neg_one_mul hcp hp₁
      (ih (squarefree.of_mul_right hn) (λ q hqp hqd, H q hqp $ dvd_mul_of_dvd_right hqd _)), }
end

/-!
### Relation to sums of two squares
-/

/-- If `-1` is a square modulo the natural number `n`, then `n` is a sum of two squares. -/
lemma nat.eq_sq_add_sq_of_is_square_mod_neg_one {n : ℕ} (h : is_square (-1 : zmod n)) :
  ∃ x y : ℕ, n = x ^ 2 + y ^ 2 :=
begin
  induction n using induction_on_primes with p n hpp ih,
  { exact ⟨0, 0, rfl⟩, },
  { exact ⟨0, 1, rfl⟩, },
  { haveI : fact p.prime := ⟨hpp⟩,
    have hp : is_square (-1 : zmod p) := zmod.is_square_cast_neg_one ⟨n, rfl⟩ h,
    obtain ⟨u, v, huv⟩ := nat.prime.sq_add_sq' (zmod.exists_sq_eq_neg_one_iff.mp hp),
    obtain ⟨x, y, hxy⟩ := ih (zmod.is_square_cast_neg_one ⟨p, mul_comm _ _⟩ h),
    exact nat.sq_add_sq_mul huv.symm hxy, }
end

/-- If the integer `n` is a sum of two squares of coprime integers,
then `-1` is a square modulo `n`. -/
lemma zmod.is_square_neg_one_of_eq_sq_add_sq_of_is_coprime {n x y : ℤ} (h : n = x ^ 2 + y ^ 2)
  (hc : is_coprime x y) : is_square (-1 : zmod n.nat_abs) :=
begin
  obtain ⟨u, v, huv⟩ : is_coprime x n,
  { have hc2 : is_coprime (x ^ 2) (y ^ 2) := hc.pow,
    rw show y ^ 2 = n + (-1) * x ^ 2, from by {rw h, ring} at hc2,
    exact (is_coprime.pow_left_iff zero_lt_two).mp (is_coprime.of_add_mul_right_right hc2), },
  have H : (u * y) * (u * y) - (-1) = n * (-v ^ 2 * n + u ^ 2 + 2 * v) :=
    by linear_combination -u ^ 2 * h + (n * v - u * x - 1) * huv,
  refine ⟨u * y, _⟩,
  norm_cast,
  rw (by push_cast : (-1 : zmod n.nat_abs) = (-1 : ℤ)),
  exact (zmod.int_coe_eq_int_coe_iff_dvd_sub _ _ _).mpr (int.nat_abs_dvd.mpr ⟨_, H⟩),
end

/-- If the natural number `n` is a sum of two squares of coprime natural numbers, then
`-1` is a square modulo `n`. -/
lemma zmod.is_square_neg_one_of_eq_sq_add_sq_of_coprime {n x y : ℕ} (h : n = x ^ 2 + y ^ 2)
  (hc : x.coprime y) : is_square (-1 : zmod n) :=
begin
  zify at *,
  exact zmod.is_square_neg_one_of_eq_sq_add_sq_of_is_coprime h hc.is_coprime,
end

/-- A natural number `n` is a sum of two squares if and only if `n = a^2 * b` with natural
numbers `a` and `b` such that `-1` is a square modulo `b`. -/
lemma nat.eq_sq_add_sq_iff_eq_sq_mul {n : ℕ} :
  (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∃ a b : ℕ, n = a ^ 2 * b ∧ is_square (-1 : zmod b) :=
begin
  split; intro H,
  { obtain ⟨x, y, h⟩ := H,
    by_cases hxy : x = 0 ∧ y = 0,
    { exact ⟨0, 1, by rw [h, hxy.1, hxy.2, zero_pow zero_lt_two, add_zero, zero_mul],
             ⟨0, by rw [zero_mul, neg_eq_zero, fin.one_eq_zero_iff]⟩⟩, },
    have hg := nat.pos_of_ne_zero (mt nat.gcd_eq_zero_iff.mp hxy),
    obtain ⟨g, x₁, y₁, h₁, h₂, h₃, h₄⟩ := nat.exists_coprime' hg,
    exact ⟨g, x₁ ^ 2 + y₁ ^ 2, by {rw [h, h₃, h₄], ring},
           zmod.is_square_neg_one_of_eq_sq_add_sq_of_coprime rfl h₂⟩, },
  { obtain ⟨a, b, h₁, h₂⟩ := H,
    obtain ⟨x', y', h⟩ := nat.eq_sq_add_sq_of_is_square_mod_neg_one h₂,
    exact ⟨a * x', a * y', by {rw [h₁, h], ring}⟩, }
end

end neg_one_square
