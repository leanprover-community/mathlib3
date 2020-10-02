/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov.
-/
import data.real.basic
import data.rat.sqrt
import algebra.gcd_monoid
import ring_theory.multiplicity
import data.polynomial.eval
import data.polynomial.degree
import tactic.interval_cases
/-!
# Irrational real numbers

In this file we define a predicate `irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `sqrt q` is irrational if and only if
`rat.sqrt q * rat.sqrt q ≠ q ∧ 0 ≤ q`.

We also provide dot-style constructors like `irrational.add_rat`, `irrational.rat_sub` etc.
-/

open rat real multiplicity

/-- A real number is irrational if it is not equal to any rational number. -/
def irrational (x : ℝ) := x ∉ set.range (coe : ℚ → ℝ)

lemma irrational_iff_ne_rational (x : ℝ) : irrational x ↔ ∀ a b : ℤ, x ≠ a / b :=
by simp only [irrational, rat.forall, cast_mk, not_exists, set.mem_range, cast_coe_int, cast_div,
  eq_comm]

/-!
### Irrationality of roots of integer and rational numbers
-/

/-- If `x^n`, `n > 0`, is integer and is not the `n`-th power of an integer, then
`x` is irrational. -/
theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ)
  (hxr : x ^ n = m) (hv : ¬ ∃ y : ℤ, x = y) (hnpos : 0 < n) :
  irrational x :=
begin
  rintros ⟨⟨N, D, P, C⟩, rfl⟩,
  rw [← cast_pow] at hxr,
  have c1 : ((D : ℤ) : ℝ) ≠ 0,
  { rw [int.cast_ne_zero, int.coe_nat_ne_zero], exact ne_of_gt P },
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1,
  rw [num_denom', cast_pow, cast_mk, div_pow, div_eq_iff_mul_eq c2,
      ← int.cast_pow, ← int.cast_pow, ← int.cast_mul, int.cast_inj] at hxr,
  have hdivn : ↑D ^ n ∣ N ^ n := dvd.intro_left m hxr,
  rw [← int.dvd_nat_abs, ← int.coe_nat_pow, int.coe_nat_dvd, int.nat_abs_pow,
    nat.pow_dvd_pow_iff hnpos] at hdivn,
  have hD : D = 1 := by rw [← nat.gcd_eq_right hdivn, C.gcd_eq_one],
  subst D,
  refine hv ⟨N, _⟩,
  rw [num_denom', int.coe_nat_one, mk_eq_div, int.cast_one, div_one, cast_coe_int]
end

/-- If `x^n = m` is an integer and `n` does not divide the `multiplicity p m`, then `x`
is irrational. -/
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : ℝ} (n : ℕ) {m : ℤ} (hm : m ≠ 0) (p : ℕ)
  [hp : fact p.prime] (hxr : x ^ n = m)
  (hv : (multiplicity (p : ℤ) m).get (finite_int_iff.2 ⟨hp.ne_one, hm⟩) % n ≠ 0) :
  irrational x :=
begin
  rcases nat.eq_zero_or_pos n with rfl | hnpos,
  { rw [eq_comm, pow_zero, ← int.cast_one, int.cast_inj] at hxr,
    simpa [hxr, multiplicity.one_right (mt is_unit_iff_dvd_one.1
      (mt int.coe_nat_dvd.1 hp.not_dvd_one)), nat.zero_mod] using hv },
  refine irrational_nrt_of_notint_nrt _ _ hxr _ hnpos,
  rintro ⟨y, rfl⟩,
  rw [← int.cast_pow, int.cast_inj] at hxr, subst m,
  have : y ≠ 0, { rintro rfl, rw zero_pow hnpos at hm, exact hm rfl },
  erw [multiplicity.pow' (nat.prime_iff_prime_int.1 hp)
    (finite_int_iff.2 ⟨hp.ne_one, this⟩), nat.mul_mod_right] at hv,
  exact hv rfl
end

theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m)
  (p : ℕ) [hp : fact p.prime]
  (Hpv : (multiplicity (p : ℤ) m).get (finite_int_iff.2 ⟨hp.ne_one, (ne_of_lt hm).symm⟩) % 2 = 1) :
  irrational (sqrt m) :=
@irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (ne.symm (ne_of_lt hm)) p hp
  (sqr_sqrt (int.cast_nonneg.2 $ le_of_lt hm))
  (by rw Hpv; exact one_ne_zero)

theorem nat.prime.irrational_sqrt {p : ℕ} (hp : nat.prime p) : irrational (sqrt p) :=
@irrational_sqrt_of_multiplicity_odd p (int.coe_nat_pos.2 hp.pos) p hp $
by simp [multiplicity_self (mt is_unit_iff_dvd_one.1 (mt int.coe_nat_dvd.1 hp.not_dvd_one) : _)];
  refl

theorem irrational_sqrt_two : irrational (sqrt 2) :=
by simpa using nat.prime_two.irrational_sqrt

theorem irrational_sqrt_rat_iff (q : ℚ) : irrational (sqrt q) ↔
  rat.sqrt q * rat.sqrt q ≠ q ∧ 0 ≤ q :=
if H1 : rat.sqrt q * rat.sqrt q = q
then iff_of_false (not_not_intro ⟨rat.sqrt q,
  by rw [← H1, cast_mul, sqrt_mul_self (cast_nonneg.2 $ rat.sqrt_nonneg q),
         sqrt_eq, abs_of_nonneg (rat.sqrt_nonneg q)]⟩) (λ h, h.1 H1)
else if H2 : 0 ≤ q
then iff_of_true (λ ⟨r, hr⟩, H1 $ (exists_mul_self _).1 ⟨r,
  by rwa [eq_comm, sqrt_eq_iff_mul_self_eq (cast_nonneg.2 H2), ← cast_mul, cast_inj] at hr;
  rw [← hr]; exact real.sqrt_nonneg _⟩) ⟨H1, H2⟩
else iff_of_false (not_not_intro ⟨0,
  by rw cast_zero; exact (sqrt_eq_zero_of_nonpos (rat.cast_nonpos.2 $ le_of_not_le H2)).symm⟩)
  (λ h, H2 h.2)

instance (q : ℚ) : decidable (irrational (sqrt q)) :=
decidable_of_iff' _ (irrational_sqrt_rat_iff q)

/-!
### Adding/subtracting/multiplying by rational numbers
-/

lemma rat.not_irrational (q : ℚ) : ¬irrational q := λ h, h ⟨q, rfl⟩

namespace irrational

variables (q : ℚ) {x y : ℝ}

open_locale classical

theorem add_cases : irrational (x + y) → irrational x ∨ irrational y :=
begin
  delta irrational,
  contrapose!,
  rintros ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩,
  exact ⟨rx + ry, cast_add rx ry⟩
end

theorem of_rat_add (h : irrational (q + x)) : irrational x :=
h.add_cases.elim (λ h, absurd h q.not_irrational) id

theorem rat_add (h : irrational x) : irrational (q + x) :=
of_rat_add (-q) $ by rwa [cast_neg, neg_add_cancel_left]

theorem of_add_rat : irrational (x + q) → irrational x :=
add_comm ↑q x ▸ of_rat_add q

theorem add_rat (h : irrational x) : irrational (x + q) :=
add_comm ↑q x ▸ h.rat_add q

theorem of_neg (h : irrational (-x)) : irrational x :=
λ ⟨q, hx⟩, h ⟨-q, by rw [cast_neg, hx]⟩

protected theorem neg (h : irrational x) : irrational (-x) :=
of_neg $ by rwa neg_neg

theorem sub_rat (h : irrational x) : irrational (x - q) :=
by simpa only [cast_neg] using h.add_rat (-q)

theorem rat_sub (h : irrational x) : irrational (q - x) :=
h.neg.rat_add q

theorem of_sub_rat (h : irrational (x - q)) : irrational x :=
of_add_rat (-q) $ by simpa only [cast_neg]

theorem of_rat_sub (h : irrational (q - x)) : irrational x :=
(h.of_rat_add _).of_neg

theorem mul_cases : irrational (x * y) → irrational x ∨ irrational y :=
begin
  delta irrational,
  contrapose!,
  rintros ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩,
  exact ⟨rx * ry, cast_mul rx ry⟩
end

theorem of_mul_rat (h : irrational (x * q)) : irrational x :=
h.mul_cases.elim id (λ h, absurd h q.not_irrational)

theorem mul_rat (h : irrational x) {q : ℚ} (hq : q ≠ 0) : irrational (x * q) :=
of_mul_rat q⁻¹ $ by rwa [mul_assoc, ← cast_mul, mul_inv_cancel hq, cast_one, mul_one]

theorem of_rat_mul : irrational (q * x) → irrational x :=
mul_comm x q ▸ of_mul_rat q

theorem rat_mul (h : irrational x) {q : ℚ} (hq : q ≠ 0) : irrational (q * x) :=
mul_comm x q ▸ h.mul_rat hq

theorem of_mul_self (h : irrational (x * x)) : irrational x :=
h.mul_cases.elim id id

theorem of_inv (h : irrational x⁻¹) : irrational x :=
λ ⟨q, hq⟩, h $ hq ▸ ⟨q⁻¹, q.cast_inv⟩

protected theorem inv (h : irrational x) : irrational x⁻¹ :=
of_inv $ by rwa inv_inv'

theorem div_cases (h : irrational (x / y)) : irrational x ∨ irrational y :=
h.mul_cases.imp id of_inv

theorem of_rat_div (h : irrational (q / x)) : irrational x :=
(h.of_rat_mul q).of_inv

theorem of_one_div (h : irrational (1 / x)) : irrational x :=
of_rat_div 1 $ by rwa [cast_one]

theorem of_pow : ∀ n : ℕ, irrational (x^n) → irrational x
| 0 := λ h, (h ⟨1, cast_one⟩).elim
| (n+1) := λ h, h.mul_cases.elim id (of_pow n)

theorem of_fpow : ∀ m : ℤ, irrational (x^m) → irrational x
| (n:ℕ) := of_pow n
| -[1+n] := λ h, by { rw fpow_neg_succ_of_nat at h, exact h.of_inv.of_pow _ }

end irrational

section polynomial

open polynomial
variables (x : ℝ) (p : polynomial ℤ)

lemma nat_degree_gt_one_of_irrational_root (hx : irrational x) (p_nonzero : p ≠ 0)
  (x_is_root : (p.map (algebra_map ℤ ℝ)).is_root x) : 1 < p.nat_degree :=
begin
  have degree_eq : p.nat_degree = (p.map (algebra_map ℤ ℝ)).nat_degree,
  { rw nat_degree_map', exact int.cast_injective },
  by_contra rid,
  push_neg at rid,
  interval_cases p.nat_degree with h_degree,
  { have hp := eq_C_of_nat_degree_eq_zero h_degree,
    have hpx := x_is_root,
    rw [hp, is_root.def, eval_map, eval₂_C, ring_hom.eq_int_cast, int.cast_eq_zero] at hpx,
    rw [hpx, C_0] at hp,
    exact p_nonzero hp },
  { rw irrational_iff_ne_rational at hx,
    apply hx (-(p.coeff 0)) (p.coeff 1),
    rw [as_sum_range p] at x_is_root,
    simp only [is_root.def, h_degree, eval_map, finset.sum_range_succ, finset.sum_range_one,
      eval₂_mul, eval₂_add, eval₂_X, eval₂_C, eval₂_one, pow_one, pow_zero, mul_one] at x_is_root,
    simp only [ring_hom.eq_int_cast, add_eq_zero_iff_eq_neg] at x_is_root,
    suffices : (p.coeff 1 : ℝ) ≠ 0,
    { rw [eq_div_iff this, mul_comm, x_is_root, int.cast_neg] },
    norm_cast,
    rwa [← h_degree, ← leading_coeff, leading_coeff_eq_zero] }
end

end polynomial

section
variables {q : ℚ} {x : ℝ}

open irrational

@[simp] theorem irrational_rat_add_iff : irrational (q + x) ↔ irrational x :=
⟨of_rat_add q, rat_add q⟩

@[simp] theorem irrational_add_rat_iff : irrational (x + q) ↔ irrational x :=
⟨of_add_rat q, add_rat q⟩

@[simp] theorem irrational_rat_sub_iff : irrational (q - x) ↔ irrational x :=
⟨of_rat_sub q, rat_sub q⟩

@[simp] theorem irrational_sub_rat_iff : irrational (x - q) ↔ irrational x :=
⟨of_sub_rat q, sub_rat q⟩

@[simp] theorem irrational_neg_iff : irrational (-x) ↔ irrational x :=
⟨of_neg, irrational.neg⟩

@[simp] theorem irrational_inv_iff : irrational x⁻¹ ↔ irrational x :=
⟨of_inv, irrational.inv⟩

end
