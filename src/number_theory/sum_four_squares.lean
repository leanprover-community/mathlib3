/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

The main result in this file is `sum_four_squares`,
  a proof that every natural number is the sum of four square numbers.
-/
import data.zmod.basic field_theory.finite group_theory.perm.sign
import data.int.parity

open finset polynomial finite_field equiv

namespace int

lemma sum_two_squares_of_two_mul_sum_two_squares {m x y : ℤ} (h : 2 * m =  x^2 + y^2) :
  m = ((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2 :=
have (x^2 + y^2).even, by simp [h.symm, even_mul],
have hxaddy : (x + y).even, by simpa [pow_two] with parity_simps,
have hxsuby : (x - y).even, by simpa [pow_two] with parity_simps,
have (x^2 + y^2) % 2 = 0, by simp [h.symm],
(domain.mul_left_inj (show (2*2 : ℤ) ≠ 0, from dec_trivial)).1 $
calc 2 * 2 * m = (x - y)^2 + (x + y)^2 : by rw [mul_assoc, h]; ring
... = (2 * ((x - y) / 2))^2 + (2 * ((x + y) / 2))^2 :
  by rw [int.mul_div_cancel' hxsuby, int.mul_div_cancel' hxaddy]
... = 2 * 2 * (((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2) :
  by simp [mul_add, _root_.pow_succ, mul_comm, mul_assoc, mul_left_comm]

lemma exists_sum_two_squares_add_one_eq_k {p : ℕ} (hp : p.prime) :
  ∃ (a b : ℤ) (k : ℕ), a^2 + b^2 + 1 = k * p ∧ k < p :=
hp.eq_two_or_odd.elim (λ hp2, hp2.symm ▸ ⟨1, 0, 1, rfl, dec_trivial⟩) $ λ hp1,
let ⟨a, b, hab⟩ := zmodp.sum_two_squares hp (-1) in
have hab' : (p : ℤ) ∣ a.val_min_abs ^ 2 + b.val_min_abs ^ 2 + 1,
  from (zmodp.eq_zero_iff_dvd_int hp _).1 $ by simpa [eq_neg_iff_add_eq_zero] using hab,
let ⟨k, hk⟩ := hab' in
have hk0 : 0 ≤ k, from nonneg_of_mul_nonneg_left
  (by rw ← hk; exact (add_nonneg (add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)) zero_le_one))
  (int.coe_nat_pos.2 hp.pos),
⟨a.val_min_abs, b.val_min_abs, k.nat_abs,
    by rw [hk, int.nat_abs_of_nonneg hk0, mul_comm],
  lt_of_mul_lt_mul_left
    (calc p * k.nat_abs = a.val_min_abs.nat_abs ^ 2 + b.val_min_abs.nat_abs ^ 2 + 1 :
        by rw [← int.coe_nat_inj', int.coe_nat_add, int.coe_nat_add, nat.pow_two, nat.pow_two,
          int.nat_abs_mul_self, int.nat_abs_mul_self, ← _root_.pow_two, ← _root_.pow_two,
          int.coe_nat_one, hk, int.coe_nat_mul, int.nat_abs_of_nonneg hk0]
      ... ≤ (p / 2) ^ 2 + (p / 2)^2 + 1 :
        add_le_add
          (add_le_add
            (nat.pow_le_pow_of_le_left (zmodp.nat_abs_val_min_abs_le _) _)
            (nat.pow_le_pow_of_le_left (zmodp.nat_abs_val_min_abs_le _) _))
          (le_refl _)
      ... < (p / 2) ^ 2 + (p / 2)^ 2 + (p % 2)^2 + ((2 * (p / 2)^2 + (4 * (p / 2) * (p % 2)))) :
        by rw [hp1, nat.one_pow, mul_one];
          exact (lt_add_iff_pos_right _).2
            (add_pos_of_nonneg_of_pos (nat.zero_le _) (mul_pos dec_trivial
              (nat.div_pos hp.two_le dec_trivial)))
      ... = p * p : begin
        conv_rhs { rw [← nat.mod_add_div p 2] },
        simp only [nat.pow_two],
        rw [← int.coe_nat_inj'],
        simp only [nat.pow_two, int.coe_nat_add, int.coe_nat_mul, int.coe_nat_bit0, int.coe_nat_one,
          two_mul, mul_add, add_mul],
        ring,
      end)
    (show 0 ≤ p, from nat.zero_le _)⟩

end int

namespace nat

open int

open_locale classical

private lemma sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ}
  (h : a^2 + b^2 + c^2 + d^2 = 2 * m) : ∃ w x y z, w^2 + x^2 + y^2 + z^2 = m :=
have ∀ f : fin 4 → zmod 2, (f 0)^2 + (f 1)^2 + (f 2)^2 + (f 3)^2 = 0 →
    ∃ i : (fin 4), (f i)^2 + f (swap i 0 1)^2 = 0 ∧ f (swap i 0 2)^2 + f (swap i 0 3)^2 = 0,
  from dec_trivial,
let f : fin 4 → ℤ := vector.nth (a::b::c::d::vector.nil) in
let ⟨i, hσ⟩ := this (coe ∘ f) (by rw [← @zero_mul (zmod 2) _ m, ← show ((2 : ℤ) : zmod 2) = 0, from rfl,
  ← int.cast_mul, ← h]; simp only [int.cast_add, int.cast_pow]; refl) in
let σ := swap i 0 in
have h01 : 2 ∣ f (σ 0) ^ 2 + f (σ 1) ^ 2,
  from (@zmod.eq_zero_iff_dvd_int 2 _).1 $ by simpa [σ] using hσ.1,
have h23 : 2 ∣ f (σ 2) ^ 2 + f (σ 3) ^ 2,
  from (@zmod.eq_zero_iff_dvd_int 2 _).1 $ by simpa using hσ.2,
let ⟨x, hx⟩ := h01 in let ⟨y, hy⟩ := h23 in
⟨(f (σ 0) - f (σ 1)) / 2, (f (σ 0) + f (σ 1)) / 2, (f (σ 2) - f (σ 3)) / 2, (f (σ 2) + f (σ 3)) / 2,
  begin
    rw [← int.sum_two_squares_of_two_mul_sum_two_squares hx.symm, add_assoc,
      ← int.sum_two_squares_of_two_mul_sum_two_squares hy.symm,
      ← domain.mul_left_inj (show (2 : ℤ) ≠ 0, from dec_trivial), ← h, mul_add, ← hx, ← hy],
    have : univ.sum (λ x, f (σ x)^2) = univ.sum (λ x, f x^2),
    { conv_rhs { rw finset.sum_univ_perm σ } },
    have fin4univ : (univ : finset (fin 4)).1 = 0::1::2::3::0, from dec_trivial,
    simpa [finset.sum_eq_multiset_sum, fin4univ, multiset.sum_cons, f]
  end⟩

private lemma prime_sum_four_squares {p : ℕ} (hp : p.prime) :
  ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = p :=
have hm : ∃ m < p, 0 < m ∧ ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = m * p,
  from let ⟨a, b, k, hk⟩ := exists_sum_two_squares_add_one_eq_k hp in
  ⟨k, hk.2, nat.pos_of_ne_zero $
    (λ hk0, by rw [hk0, int.coe_nat_zero, zero_mul] at hk;
      exact ne_of_gt (show a^2 + b^2 + 1 > 0, from add_pos_of_nonneg_of_pos
        (add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)) zero_lt_one) hk.1),
    a, b, 1, 0, by simpa [_root_.pow_two] using hk.1⟩,
let m := nat.find hm in
let ⟨a, b, c, d, (habcd : a^2 + b^2 + c^2 + d^2 = m * p)⟩ := (nat.find_spec hm).snd.2 in
have hm0 : 0 < m, from (nat.find_spec hm).snd.1,
have hmp : m < p, from (nat.find_spec hm).fst,
m.mod_two_eq_zero_or_one.elim
  (λ hm2 : m % 2 = 0,
    let ⟨k, hk⟩ := (nat.dvd_iff_mod_eq_zero _ _).2 hm2 in
    have hk0 : 0 < k, from nat.pos_of_ne_zero $ λ _, by simp [*, lt_irrefl] at *,
    have hkm : k < m, by rw [hk, two_mul]; exact (lt_add_iff_pos_left _).2 hk0,
    false.elim $ nat.find_min hm hkm ⟨lt_trans hkm hmp, hk0,
      sum_four_squares_of_two_mul_sum_four_squares
        (show a^2 + b^2 + c^2 + d^2 = 2 * (k * p),
          by rw [habcd, hk, int.coe_nat_mul, mul_assoc]; simp)⟩)
  (λ hm2 : m % 2 = 1,
    if hm1 : m = 1 then ⟨a, b, c, d, by simp only [hm1, habcd, int.coe_nat_one, one_mul]⟩
    else --have hm1 : 1 < m, from lt_of_le_of_ne hm0 (ne.symm hm1),
      let mp : ℕ+ := ⟨m, hm0⟩ in
      let w := (a : zmod mp).val_min_abs, x := (b : zmod mp).val_min_abs,
          y := (c : zmod mp).val_min_abs, z := (d : zmod mp).val_min_abs in
      have hnat_abs : w^2 + x^2 + y^2 + z^2 =
          (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs ^2 + z.nat_abs ^ 2 : ℕ),
        by simp [_root_.pow_two],
      have hwxyzlt : w^2 + x^2 + y^2 + z^2 < m^2,
        from calc w^2 + x^2 + y^2 + z^2
            = (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs ^2 + z.nat_abs ^ 2 : ℕ) : hnat_abs
        ... ≤ ((m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 + (m / 2) ^ 2 : ℕ) :
          int.coe_nat_le.2 $ add_le_add (add_le_add (add_le_add
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
            (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)
        ... = 4 * (m / 2 : ℕ) ^ 2 : by simp [_root_.pow_two, bit0, bit1, mul_add, add_mul]
        ... < 4 * (m / 2 : ℕ) ^ 2 + ((4 * (m / 2) : ℕ) * (m % 2 : ℕ) + (m % 2 : ℕ)^2) :
          (lt_add_iff_pos_right _).2 (by rw [hm2, int.coe_nat_one, _root_.one_pow, mul_one];
            exact add_pos_of_nonneg_of_pos (int.coe_nat_nonneg _) zero_lt_one)
        ... = m ^ 2 : by conv_rhs {rw [← nat.mod_add_div m 2]};
          simp [-nat.mod_add_div, mul_add, add_mul, bit0, bit1, mul_comm, mul_assoc, mul_left_comm,
            _root_.pow_add],
      have hwxyzabcd : ((w^2 + x^2 + y^2 + z^2 : ℤ) : zmod mp) =
          ((a^2 + b^2 + c^2 + d^2 : ℤ) : zmod mp),
        by simp [w, x, y, z, pow_two],
      have hwxyz0 : ((w^2 + x^2 + y^2 + z^2 : ℤ) : zmod mp) = 0,
        by rw [hwxyzabcd, habcd, int.cast_mul, show ((m : ℤ) : zmod mp) = (mp : zmod mp), from rfl,
          int.cast_coe_nat, coe_coe, zmod.cast_self_eq_zero]; simp,
      let ⟨n, hn⟩ := (zmod.eq_zero_iff_dvd_int.1 hwxyz0) in
      have hn0 : 0 < n.nat_abs, from int.nat_abs_pos_of_ne_zero (λ hn0,
        have hwxyz0 : (w.nat_abs^2 + x.nat_abs^2 + y.nat_abs^2 + z.nat_abs^2 : ℕ) = 0,
          by rw [← int.coe_nat_eq_zero, ← hnat_abs]; rwa [hn0, mul_zero] at hn,
        have habcd0 : (m : ℤ) ∣ a ∧ (m : ℤ) ∣ b ∧ (m : ℤ) ∣ c ∧ (m : ℤ) ∣ d,
          by simpa [add_eq_zero_iff_eq_zero_of_nonneg (pow_two_nonneg _) (pow_two_nonneg _),
            nat.pow_two, w, x, y, z, zmod.eq_zero_iff_dvd_int] using hwxyz0,
        let ⟨ma, hma⟩ := habcd0.1,     ⟨mb, hmb⟩ := habcd0.2.1,
            ⟨mc, hmc⟩ := habcd0.2.2.1, ⟨md, hmd⟩ := habcd0.2.2.2 in
        have hmdvdp : m ∣ p,
          from int.coe_nat_dvd.1 ⟨ma^2 + mb^2 + mc^2 + md^2,
            (domain.mul_left_inj (show (m : ℤ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 hm0)).1 $
              by rw [← habcd, hma, hmb, hmc, hmd]; ring⟩,
        (hp.2 _ hmdvdp).elim hm1 (λ hmeqp, by simpa [lt_irrefl, hmeqp] using hmp)),
      have hawbxcydz : ((mp : ℕ) : ℤ) ∣ a * w + b * x + c * y + d * z,
        from zmod.eq_zero_iff_dvd_int.1 $ by rw [← hwxyz0]; simp; ring,
      have haxbwczdy : ((mp : ℕ) : ℤ) ∣ a * x - b * w - c * z + d * y,
        from zmod.eq_zero_iff_dvd_int.1 $ by simp; ring,
      have haybzcwdx : ((mp : ℕ) : ℤ) ∣ a * y + b * z - c * w - d * x,
        from zmod.eq_zero_iff_dvd_int.1 $ by simp; ring,
      have hazbycxdw : ((mp : ℕ) : ℤ) ∣ a * z - b * y + c * x - d * w,
        from zmod.eq_zero_iff_dvd_int.1 $ by simp; ring,
      let ⟨s, hs⟩ := hawbxcydz, ⟨t, ht⟩ := haxbwczdy, ⟨u, hu⟩ := haybzcwdx, ⟨v, hv⟩ := hazbycxdw in
      have hn_nonneg : 0 ≤ n,
        from nonneg_of_mul_nonneg_left
          (by erw [← hn]; repeat {try {refine add_nonneg _ _}, try {exact pow_two_nonneg _}})
          (int.coe_nat_pos.2 hm0),
      have hnm : n.nat_abs < mp,
        from int.coe_nat_lt.1 (lt_of_mul_lt_mul_left
          (by rw [int.nat_abs_of_nonneg hn_nonneg, ← hn, ← _root_.pow_two]; exact hwxyzlt)
          (int.coe_nat_nonneg mp)),
      have hstuv : s^2 + t^2 + u^2 + v^2 = n.nat_abs * p,
        from (domain.mul_left_inj (show (m^2 : ℤ) ≠ 0, from pow_ne_zero 2
            (int.coe_nat_ne_zero_iff_pos.2 hm0))).1 $
          calc (m : ℤ)^2 * (s^2 + t^2 + u^2 + v^2) = ((mp : ℕ) * s)^2 + ((mp : ℕ) * t)^2 +
              ((mp : ℕ) * u)^2 + ((mp : ℕ) * v)^2 :
            by simp [mp]; ring
          ... = (w^2 + x^2 + y^2 + z^2) * (a^2 + b^2 + c^2 + d^2) :
            by simp only [hs.symm, ht.symm, hu.symm, hv.symm]; ring
          ... = _ : by rw [hn, habcd, int.nat_abs_of_nonneg hn_nonneg]; dsimp [mp]; ring,
      false.elim $ nat.find_min hm hnm ⟨lt_trans hnm hmp, hn0, s, t, u, v, hstuv⟩)

lemma sum_four_squares : ∀ n : ℕ, ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = n
| 0 := ⟨0, 0, 0, 0, rfl⟩
| 1 := ⟨1, 0, 0, 0, rfl⟩
| n@(k+2) :=
have hm : (min_fac n).prime := min_fac_prime dec_trivial,
have n / min_fac n < n := factors_lemma,
let ⟨a, b, c, d, h₁⟩ := show ∃ a b c d : ℤ, a^2 + b^2 + c^2 + d^2 = min_fac n,
  from prime_sum_four_squares hm in
let ⟨w, x, y, z, h₂⟩ := sum_four_squares (n / min_fac n) in
⟨(a * x - b * w - c * z + d * y).nat_abs,
 (a * y + b * z - c * w - d * x).nat_abs,
 (a * z - b * y + c * x - d * w).nat_abs,
 (a * w + b * x + c * y + d * z).nat_abs,
  begin
    rw [← int.coe_nat_inj', ← nat.mul_div_cancel' (min_fac_dvd (k+2)), int.coe_nat_mul, ← h₁, ← h₂],
    simp [nat.pow_two, int.coe_nat_add, int.nat_abs_mul_self'],
    ring,
  end⟩

end nat
