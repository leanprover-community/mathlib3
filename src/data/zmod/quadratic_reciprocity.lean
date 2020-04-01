/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import field_theory.finite data.zmod.basic data.nat.parity

/-!
# Quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_pow_two_eq_prime_iff_of_mod_four_eq_one`, and
`exists_pow_two_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`exists_pow_two_eq_neg_one_iff_mod_four_ne_three` and
`exists_pow_two_eq_two_iff`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/


open function finset nat finite_field zmodp

namespace zmodp

variables {p q : ℕ} (hp : nat.prime p) (hq : nat.prime q)

@[simp] lemma card_units_zmodp : fintype.card (units (zmodp p hp)) = p - 1 :=
by rw [card_units, card_zmodp]

theorem fermat_little {p : ℕ} (hp : nat.prime p) {a : zmodp p hp} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
by rw [← units.mk0_val ha, ← @units.coe_one (zmodp p hp), ← units.coe_pow, ← units.ext_iff,
    ← card_units_zmodp hp, pow_card_eq_one]

lemma euler_criterion_units {x : units (zmodp p hp)} :
  (∃ y : units (zmodp p hp), y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
hp.eq_two_or_odd.elim
  (λ h, by resetI; subst h; exact iff_of_true ⟨1, subsingleton.elim _ _⟩ (subsingleton.elim _ _))
  (λ hp1, let ⟨g, hg⟩ := is_cyclic.exists_generator (units (zmodp p hp)) in
    let ⟨n, hn⟩ := show x ∈ powers g, from (powers_eq_gpowers g).symm ▸ hg x in
    ⟨λ ⟨y, hy⟩, by rw [← hy, ← pow_mul, two_mul_odd_div_two hp1,
        ← card_units_zmodp hp, pow_card_eq_one],
    λ hx, have 2 * (p / 2) ∣ n * (p / 2),
        by rw [two_mul_odd_div_two hp1, ← card_units_zmodp hp, ← order_of_eq_card_of_forall_mem_gpowers hg];
        exact order_of_dvd_of_pow_eq_one (by rwa [pow_mul, hn]),
      let ⟨m, hm⟩ := dvd_of_mul_dvd_mul_right (nat.div_pos hp.two_le dec_trivial) this in
      ⟨g ^ m, by rwa [← pow_mul, mul_comm, ← hm]⟩⟩)

lemma euler_criterion {a : zmodp p hp} (ha : a ≠ 0) :
  (∃ y : zmodp p hp, y ^ 2 = a) ↔ a ^ (p / 2) = 1 :=
⟨λ ⟨y, hy⟩,
  have hy0 : y ≠ 0, from λ h, by simp [h, _root_.zero_pow (succ_pos 1)] at hy; cc,
  by simpa using (units.ext_iff.1 $ (euler_criterion_units hp).1 ⟨units.mk0 _ hy0, show _ = units.mk0 _ ha,
    by rw [units.ext_iff]; simpa⟩),
λ h, let ⟨y, hy⟩ := (euler_criterion_units hp).2 (show units.mk0 _ ha ^ (p / 2) = 1, by simpa [units.ext_iff]) in
  ⟨y, by simpa [units.ext_iff] using hy⟩⟩

lemma exists_pow_two_eq_neg_one_iff_mod_four_ne_three :
  (∃ y : zmodp p hp, y ^ 2 = -1) ↔ p % 4 ≠ 3 :=
have (-1 : zmodp p hp) ≠ 0, from mt neg_eq_zero.1 one_ne_zero,
hp.eq_two_or_odd.elim (λ hp, by resetI; subst hp; exact dec_trivial)
  (λ hp1, (mod_two_eq_zero_or_one (p / 2)).elim
    (λ hp2, begin
      rw [euler_criterion hp this, neg_one_pow_eq_pow_mod_two, hp2, _root_.pow_zero,
        eq_self_iff_true, true_iff],
      assume h,
      rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl, h] at hp2,
      exact absurd hp2 dec_trivial,
    end)
    (λ hp2, begin
      rw [euler_criterion hp this, neg_one_pow_eq_pow_mod_two, hp2, _root_.pow_one,
        iff_false_intro (zmodp.ne_neg_self hp hp1 one_ne_zero).symm, false_iff,
        not_not],
      rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl] at hp2,
      rw [← nat.mod_mul_left_mod _ 2, show 2 * 2 = 4, from rfl] at hp1,
      have hp4 : p % 4 < 4, from nat.mod_lt _ dec_trivial,
      revert hp1 hp2, revert hp4,
      generalize : p % 4 = k,
      revert k, exact dec_trivial
    end))

lemma pow_div_two_eq_neg_one_or_one {a : zmodp p hp} (ha : a ≠ 0) : a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
hp.eq_two_or_odd.elim
  (λ h, by revert a ha; resetI; subst h; exact dec_trivial)
  (λ hp1, by rw [← mul_self_eq_one_iff, ← _root_.pow_add, ← two_mul, two_mul_odd_div_two hp1];
    exact fermat_little hp ha)

@[simp] lemma wilsons_lemma {p : ℕ} (hp : nat.prime p) : (fact (p - 1) : zmodp p hp) = -1 :=
begin
  rw [← finset.prod_Ico_id_eq_fact, ← @units.coe_one (zmodp p hp), ← units.coe_neg,
    ← @prod_univ_units_id_eq_neg_one (zmodp p hp),
    ← prod_hom _ (coe : units (zmodp p hp) → zmodp p hp),
    prod_nat_cast],
  exact eq.symm (prod_bij
    (λ a _, (a : zmodp p hp).1)
    (λ a ha, Ico.mem.2 ⟨nat.pos_of_ne_zero
        (λ h, units.coe_ne_zero a (fin.eq_of_veq h)),
      by rw [← succ_sub hp.pos, succ_sub_one]; exact (a : zmodp p hp).2⟩)
    (λ a _, by simp) (λ _ _ _ _, units.ext_iff.2 ∘ fin.eq_of_veq)
    (λ b hb,
      have b ≠ 0 ∧ b < p, by rwa [Ico.mem, nat.succ_le_iff, ← succ_sub hp.pos,
        succ_sub_one, nat.pos_iff_ne_zero] at hb,
      ⟨units.mk0 _ (show (b : zmodp p hp) ≠ 0, from fin.ne_of_vne $
        by rw [zmod.val_cast_nat, ← @nat.cast_zero (zmodp p hp), zmod.val_cast_nat];
        simp [mod_eq_of_lt this.2, this.1]), mem_univ _,
      by simp [val_cast_of_lt hp this.2]⟩))
end

@[simp] lemma prod_Ico_one_prime {p : ℕ} (hp : nat.prime p) :
  (Ico 1 p).prod (λ x, (x : zmodp p hp)) = -1 :=
by conv in (Ico 1 p) { rw [← succ_sub_one p, succ_sub hp.pos] };
  rw [← prod_nat_cast, finset.prod_Ico_id_eq_fact, wilsons_lemma]

end zmodp

/-- The image of the map sending a non zero natural number `x ≤ p / 2` to the absolute value
  of the element of interger in the interval `(-p/2, p/2]` congruent to `a * x` mod p is the set
  of non zero natural numbers `x` such that `x ≤ p / 2` -/
lemma Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
  {p : ℕ} (hp : p.prime) (a : zmodp p hp) (hpa : a ≠ 0) :
  (Ico 1 (p / 2).succ).1.map (λ x, (a * x).val_min_abs.nat_abs) =
  (Ico 1 (p / 2).succ).1.map (λ a, a) :=
have he : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x ≠ 0 ∧ x ≤ p / 2,
  by simp [nat.lt_succ_iff, nat.succ_le_iff, nat.pos_iff_ne_zero] {contextual := tt},
have hep : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x < p,
  from λ x hx, lt_of_le_of_lt (he hx).2 (nat.div_lt_self hp.pos dec_trivial),
have hpe : ∀ {x}, x ∈ Ico 1 (p / 2).succ → ¬ p ∣ x,
  from λ x hx hpx, not_lt_of_ge (le_of_dvd (nat.pos_of_ne_zero (he hx).1) hpx) (hep hx),
have hsurj : ∀ b : ℕ , b ∈ Ico 1 (p / 2).succ →
    ∃ x ∈ Ico 1 (p / 2).succ,
      b = (a * x : zmodp p hp).val_min_abs.nat_abs,
  from λ b hb, ⟨(b / a : zmodp p hp).val_min_abs.nat_abs,
    Ico.mem.2 ⟨nat.pos_of_ne_zero $
        by simp [div_eq_mul_inv, hpa, zmodp.eq_zero_iff_dvd_nat hp b, hpe hb],
      nat.lt_succ_of_le $ zmodp.nat_abs_val_min_abs_le _⟩,
    begin
      rw [zmodp.cast_nat_abs_val_min_abs],
      split_ifs,
      { erw [mul_div_cancel' _ hpa, zmodp.val_min_abs, zmod.val_min_abs,
          zmodp.val_cast_of_lt hp (hep hb), if_pos (le_of_lt_succ (Ico.mem.1 hb).2),
          int.nat_abs_of_nat], },
      { erw [mul_neg_eq_neg_mul_symm, mul_div_cancel' _ hpa, zmod.nat_abs_val_min_abs_neg,
          zmod.val_min_abs, zmodp.val_cast_of_lt hp (hep hb),
          if_pos (le_of_lt_succ (Ico.mem.1 hb).2), int.nat_abs_of_nat] },
    end⟩,
  have hmem : ∀ x : ℕ, x ∈ Ico 1 (p / 2).succ →
    (a * x : zmodp p hp).val_min_abs.nat_abs ∈ Ico 1 (p / 2).succ,
  from λ x hx, by simp [hpa, zmodp.eq_zero_iff_dvd_nat hp x, hpe hx, lt_succ_iff, succ_le_iff,
        nat.pos_iff_ne_zero, zmodp.nat_abs_val_min_abs_le _],
multiset.map_eq_map_of_bij_of_nodup _ _ (finset.nodup _) (finset.nodup _)
  (λ x _, (a * x : zmodp p hp).val_min_abs.nat_abs) hmem (λ _ _, rfl)
  (inj_on_of_surj_on_of_card_le _ hmem hsurj (le_refl _)) hsurj

private lemma gauss_lemma_aux₁ {p : ℕ} (hp : p.prime) (hp2 : p % 2 = 1) {a : ℕ}
  (hpa : (a : zmodp p hp) ≠ 0) :
  (a^(p / 2) * (p / 2).fact : zmodp p hp) =
  (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, ¬(a * x : zmodp p hp).val ≤ p / 2)).card * (p / 2).fact :=
calc (a ^ (p / 2) * (p / 2).fact : zmodp p hp) =
    (Ico 1 (p / 2).succ).prod (λ x, a * x) :
  by rw [prod_mul_distrib, ← prod_nat_cast, ← prod_nat_cast, prod_Ico_id_eq_fact,
      prod_const, Ico.card, succ_sub_one]; simp
... = (Ico 1 (p / 2).succ).prod (λ x, (a * x : zmodp p hp).val) : by simp
... = (Ico 1 (p / 2).succ).prod
    (λ x, (if (a * x : zmodp p hp).val ≤ p / 2 then 1 else -1) *
      (a * x : zmodp p hp).val_min_abs.nat_abs) :
  prod_congr rfl $ λ _ _, begin
    simp only [zmodp.cast_nat_abs_val_min_abs],
    split_ifs; simp
  end
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmodp p hp).val ≤ p / 2)).card *
    (Ico 1 (p / 2).succ).prod (λ x, (a * x : zmodp p hp).val_min_abs.nat_abs) :
  have (Ico 1 (p / 2).succ).prod
        (λ x, if (a * x : zmodp p hp).val ≤ p / 2 then (1 : zmodp p hp) else -1) =
      ((Ico 1 (p / 2).succ).filter
        (λ x : ℕ, ¬(a * x : zmodp p hp).val ≤ p / 2)).prod (λ _, -1),
    from prod_bij_ne_one (λ x _ _, x)
      (λ x, by split_ifs; simp * at * {contextual := tt})
      (λ _ _ _ _ _ _, id)
      (λ b h _, ⟨b, by simp [-not_le, *] at *⟩)
      (by intros; split_ifs at *; simp * at *),
  by rw [prod_mul_distrib, this]; simp
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmodp p hp).val ≤ p / 2)).card * (p / 2).fact :
  by rw [← prod_nat_cast, finset.prod_eq_multiset_prod,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id hp a hpa,
      ← finset.prod_eq_multiset_prod, prod_Ico_id_eq_fact]

private lemma gauss_lemma_aux₂ {p : ℕ} (hp : p.prime) (hp2 : p % 2 = 1) {a : ℕ}
  (hpa : (a : zmodp p hp) ≠ 0) :
  (a^(p / 2) : zmodp p hp) = (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmodp p hp).val)).card :=
(domain.mul_right_inj
    (show ((p / 2).fact : zmodp p hp) ≠ 0,
      by rw [ne.def, zmodp.eq_zero_iff_dvd_nat, hp.dvd_fact, not_le];
          exact nat.div_lt_self hp.pos dec_trivial)).1 $
  by simpa using gauss_lemma_aux₁ _ hp2 hpa

private lemma eisenstein_lemma_aux₁ {p : ℕ} (hp : p.prime) (hp2 : p % 2 = 1) {a : ℕ}
  (hap : (a : zmodp p hp) ≠ 0) :
  (((Ico 1 (p / 2).succ).sum (λ x, a * x) : ℕ) : zmod 2) =
    ((Ico 1 (p / 2).succ).filter
      ((λ x : ℕ, p / 2 < (a * x : zmodp p hp).val))).card +
      (Ico 1 (p / 2).succ).sum (λ x, x)
    + ((Ico 1 (p / 2).succ).sum (λ x, (a * x) / p) : ℕ) :=
have hp2 : (p : zmod 2) = (1 : ℕ), from zmod.eq_iff_modeq_nat.2 hp2,
calc (((Ico 1 (p / 2).succ).sum (λ x, a * x) : ℕ) : zmod 2)
    = (((Ico 1 (p / 2).succ).sum (λ x, (a * x) % p + p * ((a * x) / p)) : ℕ) : zmod 2) :
  by simp only [mod_add_div]
... = ((Ico 1 (p / 2).succ).sum (λ x, ((a * x : ℕ) : zmodp p hp).val) : ℕ) +
    ((Ico 1 (p / 2).succ).sum (λ x, (a * x) / p) : ℕ) :
  by simp only [zmodp.val_cast_nat];
    simp [sum_add_distrib, mul_sum.symm, nat.cast_add, nat.cast_mul, sum_nat_cast, hp2]
... = _ : congr_arg2 (+)
  (calc (((Ico 1 (p / 2).succ).sum (λ x, ((a * x : ℕ) : zmodp p hp).val) : ℕ) : zmod 2)
      = (Ico 1 (p / 2).succ).sum
          (λ x, ((((a * x : zmodp p hp).val_min_abs +
            (if (a * x : zmodp p hp).val ≤ p / 2 then 0 else p)) : ℤ) : zmod 2)) :
        by simp only [(zmodp.val_eq_ite_val_min_abs _).symm]; simp [sum_nat_cast]
  ... = ((Ico 1 (p / 2).succ).filter
        (λ x : ℕ, p / 2 < (a * x : zmodp p hp).val)).card +
      (((Ico 1 (p / 2).succ).sum (λ x, (a * x : zmodp p hp).val_min_abs.nat_abs)) : ℕ) :
    by simp [ite_cast, add_comm, sum_add_distrib, finset.sum_ite, hp2, sum_nat_cast]
  ... = _ : by rw [finset.sum_eq_multiset_sum,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id hp _ hap,
      ← finset.sum_eq_multiset_sum];
    simp [sum_nat_cast]) rfl

private lemma eisenstein_lemma_aux₂ {p : ℕ} (hp : p.prime) (hp2 : p % 2 = 1) {a : ℕ} (ha2 : a % 2 = 1)
  (hap : (a : zmodp p hp) ≠ 0) :
  ((Ico 1 (p / 2).succ).filter
    ((λ x : ℕ, p / 2 < (a * x : zmodp p hp).val))).card
  ≡ (Ico 1 (p / 2).succ).sum (λ x, (x * a) / p) [MOD 2] :=
have ha2 : (a : zmod 2) = (1 : ℕ), from zmod.eq_iff_modeq_nat.2 ha2,
(@zmod.eq_iff_modeq_nat 2 _ _).1 $ sub_eq_zero.1 $
  by simpa [add_left_comm, sub_eq_add_neg, finset.mul_sum.symm, mul_comm, ha2, sum_nat_cast,
            add_neg_eq_iff_eq_add.symm, zmod.neg_eq_self_mod_two]
    using eq.symm (eisenstein_lemma_aux₁ hp hp2 hap)

lemma div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) : a / b =
  ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :=
calc a / b = (Ico 1 (a / b).succ).card : by simp
... = ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :
  congr_arg _$ finset.ext.2 $ λ x,
    have x * b ≤ a → x ≤ c,
      from λ h, le_trans (by rwa [le_div_iff_mul_le _ _ hb0]) hc,
    by simp [lt_succ_iff, le_div_iff_mul_le _ _ hb0]; tauto

/-- The given sum is the number of integers point in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`  -/
private lemma sum_Ico_eq_card_lt {p q : ℕ} :
  (Ico 1 (p / 2).succ).sum (λ a, (a * q) / p) =
  (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
  (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q)).card :=
if hp0 : p = 0 then by simp [hp0, finset.ext]
else
  calc (Ico 1 (p / 2).succ).sum (λ a, (a * q) / p) =
    (Ico 1 (p / 2).succ).sum (λ a,
      ((Ico 1 (q / 2).succ).filter (λ x, x * p ≤ a * q)).card) :
    finset.sum_congr rfl $ λ x hx,
      div_eq_filter_card (nat.pos_of_ne_zero hp0)
        (calc x * q / p ≤ (p / 2) * q / p :
            nat.div_le_div_right (mul_le_mul_of_nonneg_right
              (le_of_lt_succ $ by finish)
              (nat.zero_le _))
          ... ≤ _ : nat.div_mul_div_le_div _ _ _)
  ... = _ : by rw [← card_sigma];
    exact card_congr (λ a _, ⟨a.1, a.2⟩)
      (by simp {contextual := tt})
      (λ ⟨_, _⟩ ⟨_, _⟩, by simp {contextual := tt})
      (λ ⟨b₁, b₂⟩ h, ⟨⟨b₁, b₂⟩,
        by revert h; simp {contextual := tt}⟩)

/-- Each of the sums in this lemma is the cardinality of the set integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
private lemma sum_mul_div_add_sum_mul_div_eq_mul {p q : ℕ} (hp : p.prime)
  (hq0 : (q : zmodp p hp) ≠ 0) :
  (Ico 1 (p / 2).succ).sum (λ a, (a * q) / p) +
  (Ico 1 (q / 2).succ).sum (λ a, (a * p) / q) =
  (p / 2) * (q / 2) :=
have hswap : (((Ico 1 (q / 2).succ).product (Ico 1 (p / 2).succ)).filter
    (λ x : ℕ × ℕ, x.2 * q ≤ x.1 * p)).card =
  (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
    (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p)).card :=
  card_congr (λ x _, prod.swap x)
    (λ ⟨_, _⟩, by simp {contextual := tt})
    (λ ⟨_, _⟩ ⟨_, _⟩, by simp {contextual := tt})
    (λ ⟨x₁, x₂⟩ h, ⟨⟨x₂, x₁⟩, by revert h; simp {contextual := tt}⟩),
have hdisj : disjoint
    (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q))
    (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p)),
  from disjoint_filter.2 $ λ x hx hpq hqp,
  have hxp : x.1 < p, from lt_of_le_of_lt
    (show x.1 ≤ p / 2, by simp [*, nat.lt_succ_iff] at *; tauto)
    (nat.div_lt_self hp.pos dec_trivial),
  begin
    have : (x.1 : zmodp p hp) = 0,
    { simpa [hq0] using congr_arg (coe : ℕ → zmodp p hp) (le_antisymm hpq hqp) },
    rw [fin.eq_iff_veq, zmodp.val_cast_of_lt hp hxp, zmodp.zero_val] at this,
    simp * at *
  end,
have hunion : ((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q) ∪
    ((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter
      (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p) =
    ((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)),
  from finset.ext.2 $ λ x, by have := le_total (x.2 * p) (x.1 * q); simp; tauto,
by rw [sum_Ico_eq_card_lt, sum_Ico_eq_card_lt, hswap, ← card_disjoint_union hdisj, hunion,
    card_product];
  simp

variables {p q : ℕ} (hp : nat.prime p) (hq : nat.prime q)

namespace zmodp

def legendre_sym (a p : ℕ) (hp : nat.prime p) : ℤ :=
if (a : zmodp p hp) = 0 then 0 else if ∃ b : zmodp p hp, b ^ 2 = a then 1 else -1

lemma legendre_sym_eq_pow (a p : ℕ) (hp : nat.prime p) :
  (legendre_sym a p hp : zmodp p hp) = (a ^ (p / 2)) :=
if ha : (a : zmodp p hp) = 0 then by simp [*, legendre_sym, _root_.zero_pow (nat.div_pos hp.two_le (succ_pos 1))]
else
(nat.prime.eq_two_or_odd hp).elim
  (λ hp2, begin resetI; subst hp2,
    suffices : ∀ a : zmodp 2 nat.prime_two,
      (((ite (a = 0) 0 (ite (∃ (b : zmodp 2 hp), b ^ 2 = a) 1 (-1))) : ℤ) : zmodp 2 nat.prime_two) = a ^ (2 / 2),
    { exact this a },
    exact dec_trivial,
   end)
  (λ hp1, have _ := euler_criterion hp ha,
    have (-1 : zmodp p hp) ≠ 1, from (ne_neg_self hp hp1 zero_ne_one.symm).symm,
    by cases zmodp.pow_div_two_eq_neg_one_or_one hp ha; simp [legendre_sym, *] at *)

lemma legendre_sym_eq_one_or_neg_one (a : ℕ) (hp : nat.prime p) (ha : (a : zmodp p hp) ≠ 0) :
  legendre_sym a p hp = -1 ∨ legendre_sym a p hp = 1 :=
by unfold legendre_sym; split_ifs; simp * at *

/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
lemma gauss_lemma {a : ℕ} (hp1 : p % 2 = 1) (ha0 : (a : zmodp p hp) ≠ 0) :
  legendre_sym a p hp = (-1) ^ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmodp p hp).val)).card :=
have (legendre_sym a p hp : zmodp p hp) = (((-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmodp p hp).val)).card : ℤ) : zmodp p hp),
  by rw [legendre_sym_eq_pow, gauss_lemma_aux₂ hp hp1 ha0]; simp,
begin
  cases legendre_sym_eq_one_or_neg_one a hp ha0;
  cases @neg_one_pow_eq_or ℤ _  ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmodp p hp).val)).card;
  simp [*, zmodp.ne_neg_self hp hp1 one_ne_zero,
    (zmodp.ne_neg_self hp hp1 one_ne_zero).symm] at *
end

lemma legendre_sym_eq_one_iff {a : ℕ} (ha0 : (a : zmodp p hp) ≠ 0) :
  legendre_sym a p hp = 1 ↔ (∃ b : zmodp p hp, b ^ 2 = a) :=
by rw [legendre_sym]; split_ifs; finish

lemma eisenstein_lemma (hp1 : p % 2 = 1) {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : zmodp p hp) ≠ 0) :
  legendre_sym a p hp = (-1)^(Ico 1 (p / 2).succ).sum (λ x, (x * a) / p) :=
by rw [neg_one_pow_eq_pow_mod_two, gauss_lemma hp hp1 ha0, neg_one_pow_eq_pow_mod_two,
    show _ = _, from eisenstein_lemma_aux₂ hp hp1 ha1 ha0]

theorem quadratic_reciprocity (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  legendre_sym p q hq * legendre_sym q p hp = (-1) ^ ((p / 2) * (q / 2)) :=
have hpq0 : (p : zmodp q hq) ≠ 0, from zmodp.prime_ne_zero _ hp hpq.symm,
have hqp0 : (q : zmodp p hp) ≠ 0, from zmodp.prime_ne_zero _ hq hpq,
by rw [eisenstein_lemma _ hq1 hp1 hpq0, eisenstein_lemma _ hp1 hq1 hqp0,
  ← _root_.pow_add, sum_mul_div_add_sum_mul_div_eq_mul _ hpq0, mul_comm]

lemma legendre_sym_two (hp1 : p % 2 = 1) : legendre_sym 2 p hp = (-1) ^ (p / 4 + p / 2) :=
have hp2 : p ≠ 2, from mt (congr_arg (% 2)) (by simp [hp1]),
have hp22 : p / 2 / 2 = _ := div_eq_filter_card (show 0 < 2, from dec_trivial)
  (nat.div_le_self (p / 2) 2),
have hcard : (Ico 1 (p / 2).succ).card = p / 2, by simp,
have hx2 : ∀ x ∈ Ico 1 (p / 2).succ, (2 * x : zmodp p hp).val = 2 * x,
  from λ x hx, have h2xp : 2 * x < p,
      from calc 2 * x ≤ 2 * (p / 2) : mul_le_mul_of_nonneg_left
        (le_of_lt_succ $ by finish) dec_trivial
      ... < _ : by conv_rhs {rw [← mod_add_div p 2, add_comm, hp1]}; exact lt_succ_self _,
    by rw [← nat.cast_two, ← nat.cast_mul, zmodp.val_cast_of_lt _ h2xp],
have hdisj : disjoint
    ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmodp p hp).val))
    ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)),
  from disjoint_filter.2 (λ x hx, by simp [hx2 _ hx, mul_comm]),
have hunion :
    ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmodp p hp).val)) ∪
    ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)) =
    Ico 1 (p / 2).succ,
  begin
    rw [filter_union_right],
    conv_rhs {rw [← @filter_true _ (Ico 1 (p / 2).succ)]},
    exact filter_congr (λ x hx, by simp [hx2 _ hx, lt_or_le, mul_comm])
  end,
begin
  rw [gauss_lemma _ hp1 (prime_ne_zero hp prime_two hp2),
    neg_one_pow_eq_pow_mod_two, @neg_one_pow_eq_pow_mod_two _ _ (p / 4 + p / 2)],
  refine congr_arg2 _ rfl ((@zmod.eq_iff_modeq_nat 2 _ _).1 _),
  rw [show 4 = 2 * 2, from rfl, ← nat.div_div_eq_div_mul, hp22, nat.cast_add,
    ← sub_eq_iff_eq_add', sub_eq_add_neg, zmod.neg_eq_self_mod_two,
    ← nat.cast_add, ← card_disjoint_union hdisj, hunion, hcard]
end

lemma exists_pow_two_eq_two_iff (hp1 : p % 2 = 1) :
  (∃ a : zmodp p hp, a ^ 2 = 2) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
have hp2 : ((2 : ℕ) : zmodp p hp) ≠ 0,
  from zmodp.prime_ne_zero hp prime_two (λ h, by simp * at *),
have hpm4 : p % 4 = p % 8 % 4, from (nat.mod_mul_left_mod p 2 4).symm,
have hpm2 : p % 2 = p % 8 % 2, from (nat.mod_mul_left_mod p 4 2).symm,
begin
  rw [show (2 : zmodp p hp) = (2 : ℕ), by simp, ← legendre_sym_eq_one_iff hp hp2,
    legendre_sym_two hp hp1, neg_one_pow_eq_one_iff_even (show (-1 : ℤ) ≠ 1, from dec_trivial),
    even_add, even_div, even_div],
  have := nat.mod_lt p (show 0 < 8, from dec_trivial),
  revert this hp1,
  erw [hpm4, hpm2],
  generalize hm : p % 8 = m,
  clear hm,
  revert m,
  exact dec_trivial
end

lemma exists_pow_two_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q % 2 = 1) :
  (∃ a : zmodp p hp, a ^ 2 = q) ↔ ∃ b : zmodp q hq, b ^ 2 = p :=
if hpq : p = q then by resetI; subst hpq else
have h1 : ((p / 2) * (q / 2)) % 2 = 0,
  from (dvd_iff_mod_eq_zero _ _).1
    (dvd_mul_of_dvd_left ((dvd_iff_mod_eq_zero _ _).2 $
    by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp1]; refl) _),
begin
  have := quadratic_reciprocity hp hq (odd_of_mod_four_eq_one hp1) hq1 hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym,
    if_neg (zmodp.prime_ne_zero hp hq hpq),
    if_neg (zmodp.prime_ne_zero hq hp (ne.symm hpq))] at this,
  split_ifs at this; simp *; contradiction
end

lemma exists_pow_two_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3)
  (hq3 : q % 4 = 3) (hpq : p ≠ q) : (∃ a : zmodp p hp, a ^ 2 = q) ↔ ¬∃ b : zmodp q hq, b ^ 2 = p :=
have h1 : ((p / 2) * (q / 2)) % 2 = 1,
  from nat.odd_mul_odd
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp3]; refl)
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hq3]; refl),
begin
  have := quadratic_reciprocity hp hq (odd_of_mod_four_eq_three hp3)
    (odd_of_mod_four_eq_three hq3) hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym,
    if_neg (zmodp.prime_ne_zero hp hq hpq),
    if_neg (zmodp.prime_ne_zero hq hp hpq.symm)] at this,
  split_ifs at this; simp *; contradiction
end

end zmodp
