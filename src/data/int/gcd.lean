/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro, Aaron Anderson
-/

import data.int.xgcd
import ring_theory.multiplicity
import ring_theory.principal_ideal_domain
import ring_theory.unique_factorization_domain
import ring_theory.euclidean_domain

/-!
# Divisibility over ℤ

## Main definitions

* `lcm (i j : ℤ)` is the ℤ specific version of least common multiple.

## Main statements

* ℤ is a `normalization_monoid`
* ℤ is a `gcd_monoid`
* Many results for greatest common divisors and least common multiples in ℤ
-/

/-! ### Divisibility over ℤ -/
namespace int

theorem nat_abs_div (a b : ℤ) (H : b ∣ a) : nat_abs (a / b) = (nat_abs a) / (nat_abs b) :=
begin
  cases (nat.eq_zero_or_pos (nat_abs b)),
  {rw eq_zero_of_nat_abs_eq_zero h, simp [int.div_zero]},
  calc
  nat_abs (a / b) = nat_abs (a / b) * 1 : by rw mul_one
    ... = nat_abs (a / b) * (nat_abs b / nat_abs b) : by rw nat.div_self h
    ... = nat_abs (a / b) * nat_abs b / nat_abs b : by rw (nat.mul_div_assoc _ (dvd_refl _))
    ... = nat_abs (a / b * b) / nat_abs b : by rw (nat_abs_mul (a / b) b)
    ... = nat_abs a / nat_abs b : by rw int.div_mul_cancel H,
end

theorem nat_abs_dvd_abs_iff {i j : ℤ} : i.nat_abs ∣ j.nat_abs ↔ i ∣ j :=
⟨assume (H : i.nat_abs ∣ j.nat_abs), dvd_nat_abs.mp (nat_abs_dvd.mp (coe_nat_dvd.mpr H)),
assume H : (i ∣ j), coe_nat_dvd.mp (dvd_nat_abs.mpr (nat_abs_dvd.mpr H))⟩

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : nat.prime p) {m n : ℤ} {k l : ℕ}
      (hpm : ↑(p ^ k) ∣ m)
      (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k+l+1)) ∣ m*n) : ↑(p ^ (k+1)) ∣ m ∨ ↑(p ^ (l+1)) ∣ n :=
have hpm' : p ^ k ∣ m.nat_abs, from int.coe_nat_dvd.1 $ int.dvd_nat_abs.2 hpm,
have hpn' : p ^ l ∣ n.nat_abs, from int.coe_nat_dvd.1 $ int.dvd_nat_abs.2 hpn,
have hpmn' : (p ^ (k+l+1)) ∣ m.nat_abs*n.nat_abs,
  by rw ←int.nat_abs_mul; apply (int.coe_nat_dvd.1 $ int.dvd_nat_abs.2 hpmn),
let hsd := nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn' in
hsd.elim
  (λ hsd1, or.inl begin apply int.dvd_nat_abs.1, apply int.coe_nat_dvd.2 hsd1 end)
  (λ hsd2, or.inr begin apply int.dvd_nat_abs.1, apply int.coe_nat_dvd.2 hsd2 end)

theorem dvd_of_mul_dvd_mul_left {i j k : ℤ} (k_non_zero : k ≠ 0) (H : k * i ∣ k * j) : i ∣ j :=
dvd.elim H (λl H1, by rw mul_assoc at H1; exact ⟨_, mul_left_cancel' k_non_zero H1⟩)

theorem dvd_of_mul_dvd_mul_right {i j k : ℤ} (k_non_zero : k ≠ 0) (H : i * k ∣ j * k) : i ∣ j :=
by rw [mul_comm i k, mul_comm j k] at H; exact dvd_of_mul_dvd_mul_left k_non_zero H

lemma prime.dvd_nat_abs_of_coe_dvd_pow_two {p : ℕ} (hp : p.prime) (k : ℤ) (h : ↑p ∣ k ^ 2) :
  p ∣ k.nat_abs :=
begin
  apply @nat.prime.dvd_of_dvd_pow _ _ 2 hp,
  rwa [pow_two, ← nat_abs_mul, ← coe_nat_dvd_left, ← pow_two]
end

end int

theorem nat.is_coprime_iff_coprime {m n : ℕ} : is_coprime (m : ℤ) n ↔ nat.coprime m n :=
⟨λ ⟨a, b, H⟩, nat.eq_one_of_dvd_one $ int.coe_nat_dvd.1 $ by { rw [int.coe_nat_one, ← H],
  exact dvd_add (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_left m n) _)
    (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_right m n) _) },
λ H, ⟨nat.gcd_a m n, nat.gcd_b m n, by rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ),
    ← nat.gcd_eq_gcd_ab, show _ = _, from H, int.coe_nat_one]⟩⟩

instance nat.unique_units : unique (units ℕ) :=
{ default := 1, uniq := nat.units_eq_one }

namespace int

section normalization_monoid

instance : normalization_monoid ℤ :=
{ norm_unit      := λa:ℤ, if 0 ≤ a then 1 else -1,
  norm_unit_zero := if_pos (le_refl _),
  norm_unit_mul  := assume a b hna hnb,
  begin
    cases hna.lt_or_lt with ha ha; cases hnb.lt_or_lt with hb hb;
      simp [mul_nonneg_iff, ha.le, ha.not_le, hb.le, hb.not_le]
  end,
  norm_unit_coe_units := assume u, (units_eq_one_or u).elim
    (assume eq, eq.symm ▸ if_pos zero_le_one)
    (assume eq, eq.symm ▸ if_neg (not_le_of_gt $ show (-1:ℤ) < 0, by simp [@neg_lt ℤ _ 1 0])), }

lemma normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z :=
show z * ↑(ite _ _ _) = z, by rw [if_pos h, units.coe_one, mul_one]

lemma normalize_of_neg {z : ℤ} (h : z < 0) : normalize z = -z :=
show z * ↑(ite _ _ _) = -z, by rw [if_neg (not_le_of_gt h), units.coe_neg, units.coe_one, mul_neg_one]

lemma normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
normalize_of_nonneg (coe_nat_le_coe_nat_of_le $ nat.zero_le n)

theorem coe_nat_abs_eq_normalize (z : ℤ) : (z.nat_abs : ℤ) = normalize z :=
begin
  by_cases 0 ≤ z,
  { simp [nat_abs_of_nonneg h, normalize_of_nonneg h] },
  { simp [of_nat_nat_abs_of_nonpos (le_of_not_ge h), normalize_of_neg (lt_of_not_ge h)] }
end

end normalization_monoid

/-- ℤ specific version of least common multiple. -/
def lcm (i j : ℤ) : ℕ := nat.lcm (nat_abs i) (nat_abs j)

theorem lcm_def (i j : ℤ) : lcm i j = nat.lcm (nat_abs i) (nat_abs j) := rfl

section gcd_monoid

theorem gcd_dvd_left (i j : ℤ) : (gcd i j : ℤ) ∣ i :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_left _ _

theorem gcd_dvd_right (i j : ℤ) : (gcd i j : ℤ) ∣ j :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_right _ _

theorem dvd_gcd {i j k : ℤ} (h1 : k ∣ i) (h2 : k ∣ j) : k ∣ gcd i j :=
nat_abs_dvd.1 $ coe_nat_dvd.2 $ nat.dvd_gcd (nat_abs_dvd_abs_iff.2 h1) (nat_abs_dvd_abs_iff.2 h2)

theorem gcd_mul_lcm (i j : ℤ) : gcd i j * lcm i j = nat_abs (i * j) :=
by rw [int.gcd, int.lcm, nat.gcd_mul_lcm, nat_abs_mul]

instance : gcd_monoid ℤ :=
{ gcd            := λa b, int.gcd a b,
  lcm            := λa b, int.lcm a b,
  gcd_dvd_left   := assume a b, int.gcd_dvd_left _ _,
  gcd_dvd_right  := assume a b, int.gcd_dvd_right _ _,
  dvd_gcd        := assume a b c, dvd_gcd,
  normalize_gcd  := assume a b, normalize_coe_nat _,
  gcd_mul_lcm    := by intros; rw [← int.coe_nat_mul, gcd_mul_lcm, coe_nat_abs_eq_normalize],
  lcm_zero_left  := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_left _,
  lcm_zero_right := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_right _,
  .. int.normalization_monoid }

lemma coe_gcd (i j : ℤ) : ↑(int.gcd i j) = gcd_monoid.gcd i j := rfl
lemma coe_lcm (i j : ℤ) : ↑(int.lcm i j) = gcd_monoid.lcm i j := rfl

lemma nat_abs_gcd (i j : ℤ) : nat_abs (gcd_monoid.gcd i j) = int.gcd i j := rfl
lemma nat_abs_lcm (i j : ℤ) : nat_abs (gcd_monoid.lcm i j) = int.lcm i j := rfl

end gcd_monoid

theorem gcd_comm (i j : ℤ) : gcd i j = gcd j i := nat.gcd_comm _ _

theorem gcd_assoc (i j k : ℤ) : gcd (gcd i j) k = gcd i (gcd j k) := nat.gcd_assoc _ _ _

@[simp] theorem gcd_self (i : ℤ) : gcd i i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_left (i : ℤ) : gcd 0 i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_right (i : ℤ) : gcd i 0 = nat_abs i := by simp [gcd]

@[simp] theorem gcd_one_left (i : ℤ) : gcd 1 i = 1 := nat.gcd_one_left _

@[simp] theorem gcd_one_right (i : ℤ) : gcd i 1 = 1 := nat.gcd_one_right _

theorem gcd_mul_left (i j k : ℤ) : gcd (i * j) (i * k) = nat_abs i * gcd j k :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_gcd, coe_nat_abs_eq_normalize]

theorem gcd_mul_right (i j k : ℤ) : gcd (i * j) (k * j) = gcd i k * nat_abs j :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_gcd, coe_nat_abs_eq_normalize]

theorem gcd_pos_of_non_zero_left {i : ℤ} (j : ℤ) (i_non_zero : i ≠ 0) : 0 < gcd i j :=
nat.gcd_pos_of_pos_left (nat_abs j) (nat_abs_pos_of_ne_zero i_non_zero)

theorem gcd_pos_of_non_zero_right (i : ℤ) {j : ℤ} (j_non_zero : j ≠ 0) : 0 < gcd i j :=
nat.gcd_pos_of_pos_right (nat_abs i) (nat_abs_pos_of_ne_zero j_non_zero)

theorem gcd_eq_zero_iff {i j : ℤ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
by rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_zero, coe_gcd, gcd_eq_zero_iff]

theorem gcd_div {i j k : ℤ} (H1 : k ∣ i) (H2 : k ∣ j) :
  gcd (i / k) (j / k) = gcd i j / nat_abs k :=
by rw [gcd, nat_abs_div i k H1, nat_abs_div j k H2];
exact nat.gcd_div (nat_abs_dvd_abs_iff.mpr H1) (nat_abs_dvd_abs_iff.mpr H2)

theorem gcd_div_gcd_div_gcd {i j : ℤ} (H : 0 < gcd i j) :
  gcd (i / gcd i j) (j / gcd i j) = 1 :=
begin
  rw [gcd_div (gcd_dvd_left i j) (gcd_dvd_right i j)],
  rw [nat_abs_of_nat, nat.div_self H]
end

theorem gcd_dvd_gcd_of_dvd_left {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd i j ∣ gcd k j :=
int.coe_nat_dvd.1 $ dvd_gcd (dvd.trans (gcd_dvd_left i j) H) (gcd_dvd_right i j)

theorem gcd_dvd_gcd_of_dvd_right {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd j i ∣ gcd j k :=
int.coe_nat_dvd.1 $ dvd_gcd (gcd_dvd_left j i) (dvd.trans (gcd_dvd_right j i) H)

theorem gcd_dvd_gcd_mul_left (i j k : ℤ) : gcd i j ∣ gcd (k * i) j :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (i j k : ℤ) : gcd i j ∣ gcd (i * k) j :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (i j k : ℤ) : gcd i j ∣ gcd i (k * j) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (i j k : ℤ) : gcd i j ∣ gcd i (j * k) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)

theorem gcd_eq_left {i j : ℤ} (H : i ∣ j) : gcd i j = nat_abs i :=
nat.dvd_antisymm (by unfold gcd; exact nat.gcd_dvd_left _ _)
                 (by unfold gcd; exact nat.dvd_gcd (dvd_refl _) (nat_abs_dvd_abs_iff.mpr H))

theorem gcd_eq_right {i j : ℤ} (H : j ∣ i) : gcd i j = nat_abs j :=
by rw [gcd_comm, gcd_eq_left H]

theorem ne_zero_of_gcd {x y : ℤ}
  (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 :=
begin
  contrapose! hc,
  rw [hc.left, hc.right, gcd_zero_right, nat_abs_zero]
end

theorem exists_gcd_one {m n : ℤ} (H : 0 < gcd m n) :
  ∃ (m' n' : ℤ), gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
⟨_, _, gcd_div_gcd_div_gcd H,
  (int.div_mul_cancel (gcd_dvd_left m n)).symm,
  (int.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
  ∃ (g : ℕ) (m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
let ⟨m', n', h⟩ := exists_gcd_one H in ⟨_, m', n', H, h⟩

theorem pow_dvd_pow_iff {m n : ℤ} {k : ℕ} (k0 : 0 < k) : m ^ k ∣ n ^ k ↔ m ∣ n :=
begin
  refine ⟨λ h, _, λ h, pow_dvd_pow_of_dvd h _⟩,
  apply int.nat_abs_dvd_abs_iff.mp,
  apply (nat.pow_dvd_pow_iff k0).mp,
  rw [← int.nat_abs_pow, ← int.nat_abs_pow],
  exact int.nat_abs_dvd_abs_iff.mpr h
end

/- lcm -/

theorem lcm_comm (i j : ℤ) : lcm i j = lcm j i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, lcm_comm]

theorem lcm_assoc (i j k : ℤ) : lcm (lcm i j) k = lcm i (lcm j k) :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, lcm_assoc]

@[simp] theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm]

@[simp] theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm]

@[simp] theorem lcm_one_left (i : ℤ) : lcm 1 i = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_normalize]

@[simp] theorem lcm_one_right (i : ℤ) : lcm i 1 = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_normalize]

@[simp] theorem lcm_self (i : ℤ) : lcm i i = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_normalize]

theorem dvd_lcm_left (i j : ℤ) : i ∣ lcm i j :=
by rw [coe_lcm]; exact dvd_lcm_left _ _

theorem dvd_lcm_right (i j : ℤ) : j ∣ lcm i j :=
by rw [coe_lcm]; exact dvd_lcm_right _ _

theorem lcm_dvd {i j k : ℤ}  : i ∣ k → j ∣ k → (lcm i j : ℤ) ∣ k :=
by rw [coe_lcm]; exact lcm_dvd

end int

theorem irreducible_iff_nat_prime : ∀(a : ℕ), irreducible a ↔ nat.prime a
| 0 := by simp [nat.not_prime_zero]
| 1 := by simp [nat.prime, one_lt_two]
| (n + 2) :=
  have h₁ : ¬n + 2 = 1, from dec_trivial,
  begin
    simp [h₁, nat.prime, irreducible, (≥), nat.le_add_left 2 n, (∣)],
    refine forall_congr (assume a, forall_congr $ assume b, forall_congr $ assume hab, _),
    by_cases a = 1; simp [h],
    split,
    { assume hb, simpa [hb] using hab.symm },
    { assume ha, subst ha,
      have : n + 2 > 0, from dec_trivial,
      refine nat.eq_of_mul_eq_mul_left this _,
      rw [← hab, mul_one] }
  end

lemma nat.prime_iff_prime {p : ℕ} : p.prime ↔ _root_.prime (p : ℕ) :=
⟨λ hp, ⟨nat.pos_iff_ne_zero.1 hp.pos, mt is_unit_iff_dvd_one.1 hp.not_dvd_one,
    λ a b, hp.dvd_mul.1⟩,
  λ hp, ⟨nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hp.1, λ h1, hp.2.1 $ h1.symm ▸ is_unit_one⟩,
    λ a h, let ⟨b, hab⟩ := h in
      (hp.2.2 a b (hab ▸ dvd_refl _)).elim
        (λ ha, or.inr (nat.dvd_antisymm h ha))
        (λ hb, or.inl (have hpb : p = b, from nat.dvd_antisymm hb
            (hab.symm ▸ dvd_mul_left _ _),
          (nat.mul_right_inj (show 0 < p, from
              nat.pos_of_ne_zero hp.1)).1 $
            by rw [hpb, mul_comm, ← hab, hpb, mul_one]))⟩⟩

lemma nat.prime_iff_prime_int {p : ℕ} : p.prime ↔ _root_.prime (p : ℤ) :=
⟨λ hp, ⟨int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt is_unit_int.1 hp.ne_one,
  λ a b h, by rw [← int.dvd_nat_abs, int.coe_nat_dvd, int.nat_abs_mul, hp.dvd_mul] at h;
    rwa [← int.dvd_nat_abs, int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd]⟩,
  λ hp, nat.prime_iff_prime.2 ⟨int.coe_nat_ne_zero.1 hp.1,
      mt nat.is_unit_iff.1 $ λ h, by simpa [h, not_prime_one] using hp,
    λ a b, by simpa only [int.coe_nat_dvd, (int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associates_int_equiv_nat : associates ℤ ≃ ℕ :=
begin
  refine ⟨λz, z.out.nat_abs, λn, associates.mk n, _, _⟩,
  { refine (assume a, quotient.induction_on' a $ assume a,
      associates.mk_eq_mk_iff_associated.2 $ associated.symm $ ⟨norm_unit a, _⟩),
    show normalize a = int.nat_abs (normalize a),
    rw [int.coe_nat_abs_eq_normalize, normalize_idem] },
  { intro n, dsimp, rw [associates.out_mk ↑n,
    ← int.coe_nat_abs_eq_normalize, int.nat_abs_of_nat, int.nat_abs_of_nat] }
end

lemma int.prime.dvd_mul {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : p ∣ m.nat_abs ∨ p ∣ n.nat_abs :=
begin
  apply (nat.prime.dvd_mul hp).mp,
  rw ← int.nat_abs_mul,
  exact int.coe_nat_dvd_left.mp h
end

lemma int.prime.dvd_mul' {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
begin
  rw [int.coe_nat_dvd_left, int.coe_nat_dvd_left],
  exact int.prime.dvd_mul hp h
end

lemma prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ 2 * m ^ 2) : p = 2 ∨ p ∣ int.nat_abs m :=
begin
  cases int.prime.dvd_mul hp h with hp2 hpp,
  { apply or.intro_left,
    exact le_antisymm (nat.le_of_dvd zero_lt_two hp2) (nat.prime.two_le hp) },
  { apply or.intro_right,
    rw [pow_two, int.nat_abs_mul] at hpp,
    exact (or_self _).mp ((nat.prime.dvd_mul hp).mp hpp)}
end

namespace multiplicity

lemma finite_int_iff_nat_abs_finite {a b : ℤ} : finite a b ↔ finite a.nat_abs b.nat_abs :=
begin
  rw [finite_def, finite_def],
  conv in (a ^ _ ∣ b)
    { rw [← int.nat_abs_dvd_abs_iff, int.nat_abs_pow] }
end

lemma finite_int_iff {a b : ℤ} : finite a b ↔ (a.nat_abs ≠ 1 ∧ b ≠ 0) :=
begin
  have := int.nat_abs_eq a,
  have := @int.nat_abs_ne_zero_of_ne_zero b,
  rw [finite_int_iff_nat_abs_finite, finite_nat_iff, nat.pos_iff_ne_zero],
  split; finish
end

instance decidable_nat : decidable_rel (λ a b : ℕ, (multiplicity a b).dom) :=
λ a b, decidable_of_iff _ finite_nat_iff.symm

instance decidable_int : decidable_rel (λ a b : ℤ, (multiplicity a b).dom) :=
λ a b, decidable_of_iff _ finite_int_iff.symm

end multiplicity
