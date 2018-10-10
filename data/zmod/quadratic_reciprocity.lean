/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import field_theory.finite data.zmod.basic algebra.pi_instances

open function finset nat finite_field zmodp

namespace zmodp

variables {p q : ℕ} (hp : prime p) (hq : prime q)

@[simp] lemma card_units_zmodp : fintype.card (units (zmodp p hp)) = p - 1 :=
by rw [card_units, card_zmodp]

theorem fermat_little {p : ℕ} (hp : prime p) {a : zmodp p hp} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
by rw [← units.mk0_val ha, ← @units.coe_one (zmodp p hp), ← units.coe_pow, ← units.ext_iff,
    ← card_units_zmodp hp, pow_card_eq_one]

lemma euler_criterion_units {x : units (zmodp p hp)} :
  (∃ y : units (zmodp p hp), y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
hp.eq_two_or_odd.elim
  (λ h, by subst h; revert x; exact dec_trivial)
  (λ hp1, let ⟨g, hg⟩ := is_cyclic.exists_generator (units (zmodp p hp)) in
    let ⟨n, hn⟩ := show x ∈ powers g, from (powers_eq_gpowers g).symm ▸ hg x in
    ⟨λ ⟨y, hy⟩, by rw [← hy, ← pow_mul, two_mul_odd_div_two hp1,
        ← card_units_zmodp hp, pow_card_eq_one],
    λ hx, have 2 * (p / 2) ∣ n * (p / 2),
        by rw [two_mul_odd_div_two hp1, ← card_units_zmodp hp, ← order_of_eq_card_of_forall_mem_gppowers hg];
        exact order_of_dvd_of_pow_eq_one (by rwa [pow_mul, hn]),
      let ⟨m, hm⟩ := dvd_of_mul_dvd_mul_right (nat.div_pos hp.ge_two dec_trivial) this in
      ⟨g ^ m, by rwa [← pow_mul, mul_comm, ← hm]⟩⟩)

lemma euler_criterion {a : zmodp p hp} (ha : a ≠ 0) :
  (∃ y : zmodp p hp, y ^ 2 = a) ↔ a ^ (p / 2) = 1 :=
⟨λ ⟨y, hy⟩,
  have hy0 : y ≠ 0, from by rintro rfl; rw [← hy, _root_.zero_pow (dec_trivial:0<2)] at ha; exact ha rfl,
  by simpa only [units.coe_pow, units.coe_one, units.mk0_val] using
    (units.ext_iff.1 $ (euler_criterion_units hp).1 ⟨units.mk0 _ hy0, show _ = units.mk0 _ ha,
    from units.ext_iff.2 $ by simpa only [units.coe_pow, units.mk0_val]⟩),
λ h, let ⟨y, hy⟩ := (euler_criterion_units hp).2 (show units.mk0 _ ha ^ (p / 2) = 1,
    by simpa only [units.ext_iff, units.coe_pow, units.mk0_val]) in
  ⟨y, by simpa only [units.ext_iff, units.coe_pow, units.mk0_val] using hy⟩⟩

lemma pow_div_two_eq_neg_one_or_one {a : zmodp p hp} (ha : a ≠ 0) : a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
hp.eq_two_or_odd.elim
  (λ h, by revert a ha; subst h; exact dec_trivial)
  (λ hp1, by rw [← mul_self_eq_one_iff, ← _root_.pow_add, ← two_mul, two_mul_odd_div_two hp1];
    exact fermat_little hp ha)

@[simp] lemma wilsons_lemma {p : ℕ} (hp : prime p) : (fact (p - 1) : zmodp p hp) = -1 :=
begin
  rw [← finset.prod_range_id_eq_fact, ← @units.coe_one (zmodp p hp), ← units.coe_neg,
    ← @prod_univ_units_id_eq_neg_one (zmodp p hp),
    ← prod_hom (coe : units (zmodp p hp) → zmodp p hp) units.coe_one units.coe_mul,
    ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul],
  exact eq.symm (prod_bij
    (λ a _, (a : zmodp p hp).1) (λ a ha, mem_erase.2
      ⟨λ h, units.coe_ne_zero a $ fin.eq_of_veq h,
      by rw [mem_range, ← succ_sub hp.pos, succ_sub_one]; exact a.1.2⟩)
    (λ a _, (zmodp.cast_val _ _).symm) (λ _ _ _ _, units.ext_iff.2 ∘ fin.eq_of_veq)
    (λ b hb,
      have b ≠ 0 ∧ b < p, by rwa [mem_erase, mem_range, ← succ_sub hp.pos, succ_sub_one] at hb,
      ⟨units.mk0 _ (show (b : zmodp p hp) ≠ 0, from fin.ne_of_vne $
        by rw [zmod.val_cast_nat, ← @nat.cast_zero (zmodp p hp), zmod.val_cast_nat];
        simp only [pnat.mk_coe, zero_mod, mod_eq_of_lt this.2]; exact this.1), mem_univ _,
      by simp only [units.mk0_val, val_cast_of_lt hp this.2]⟩))
end

@[simp] lemma prod_range_prime_erase_zero {p : ℕ} (hp : prime p) :
  ((range p).erase 0).prod (λ x, (x : zmodp p hp)) = -1 :=
have _ := wilsons_lemma hp,
by rwa [← finset.prod_range_id_eq_fact, ← succ_sub hp.pos, succ_sub_one,
  ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul] at this

end zmodp

namespace quadratic_reciprocity_aux

variables {p q : ℕ} (hp : prime p) (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1)
  (hpq : p ≠ q)

include hp hq hp1 hq1 hpq

lemma filter_range_p_mul_q_div_two_eq :
  (range ((p * q) / 2).succ).filter (coprime p) =
  (range (q / 2)).bind (λ x, (erase (range p) 0).image (+ p * x))
  ∪ (erase (range (succ (p / 2))) 0).image (+ q / 2 * p) :=
finset.ext.2 $ λ x,
⟨λ h, have hxp0 : x % p ≠ 0, by rw [ne.def, ← dvd_iff_mod_eq_zero, ← hp.coprime_iff_not_dvd];
    exact (mem_filter.1 h).2,
  mem_union.2 $ or_iff_not_imp_right.2 (λ h₁, mem_bind.2
  ⟨x / p, mem_range.2 $ nat.div_lt_of_lt_mul (by_contradiction
    (λ h₂,
      let ⟨c, hc⟩ := le_iff_exists_add.1 (le_of_not_gt h₂) in
      have hcp : c ≤ p / 2, from @nat.le_of_add_le_add_left (p * (q / 2)) _ _
        (by rw [← hc, ← odd_mul_odd_div_two hp1 hq1]; exact le_of_lt_succ (mem_range.1 (mem_filter.1 h).1)),
      h₁ $ mem_image.2 ⟨c, mem_erase.2 ⟨λ h, hxp0 $ by simp only [h, hc, add_zero, mul_mod_right],
            mem_range.2 $ lt_succ_of_le $ hcp⟩, by rw [hc, mul_comm, add_comm]⟩)),
    mem_image.2 ⟨x % p, mem_erase.2 $
      by rw [ne.def, ← dvd_iff_mod_eq_zero, ← hp.coprime_iff_not_dvd, mem_range];
      exact ⟨(mem_filter.1 h).2, mod_lt _ hp.pos⟩, nat.mod_add_div _ _⟩⟩),
λ h, mem_filter.2 $
  (mem_union.1 h).elim
  (λ h, let ⟨m, hm₁, hm₂⟩ := mem_bind.1 h in
    let ⟨k, hk₁, hk₂⟩ := mem_image.1 hm₂ in
    ⟨mem_range.2 $ hk₂ ▸ (mul_lt_mul_left (show 0 < 2, from dec_trivial)).1 begin
      rw [mul_succ, two_mul_odd_div_two (nat.odd_mul_odd hp1 hq1), mul_add],
      clear _let_match _let_match,
      exact calc 2 * k + 2 * (p * m) < 2 * p + 2 * (p * m) :
        add_lt_add_right ((mul_lt_mul_left dec_trivial).2 (mem_range.1 $ mem_of_mem_erase hk₁)) _
      ... = 2 * (p * (m + 1)) : by rw [mul_add, mul_add, mul_one, add_comm]
      ... ≤ 2 * (p * (q / 2)) : (mul_le_mul_left (show 0 < 2, from dec_trivial)).2
        ((mul_le_mul_left hp.pos).2 $ succ_le_of_lt $ mem_range.1 hm₁)
      ... ≤ _ : by rw [mul_left_comm, two_mul_odd_div_two hq1, nat.mul_sub_left_distrib,
            ← nat.sub_add_comm (mul_pos hp.pos hq.pos), add_succ, succ_eq_add_one, nat.add_sub_cancel];
          exact le_trans (nat.sub_le_self _ _) (nat.le_add_right _ _),
    end,
  by rw [prime.coprime_iff_not_dvd hp, ← hk₂, ← nat.dvd_add_iff_left (dvd_mul_right _ _),
       dvd_iff_mod_eq_zero, mod_eq_of_lt (mem_range.1 $ mem_of_mem_erase hk₁)]; exact ne_of_mem_erase hk₁⟩)
  (λ h, let ⟨m, hm₁, hm₂⟩ := mem_image.1 h in ⟨mem_range.2 $ hm₂ ▸ begin
    refine (mul_lt_mul_left (show 0 < 2, from  dec_trivial)).1 _,
    rw [mul_succ, two_mul_odd_div_two (nat.odd_mul_odd hp1 hq1), mul_add, ← mul_assoc 2, two_mul_odd_div_two hq1],
    exact calc 2 * m + (q - 1) * p ≤ 2 * (p / 2) + (q - 1) * p :
      add_le_add_right ((mul_le_mul_left dec_trivial).2 (le_of_lt_succ (mem_range.1 (mem_of_mem_erase hm₁)))) _
    ... < _ : begin rw [two_mul_odd_div_two hp1, nat.mul_sub_right_distrib, one_mul],
        rw [← nat.sub_add_comm hp.pos, nat.add_sub_cancel' (le_mul_of_ge_one_left' (nat.zero_le _) hq.pos), mul_comm],
        exact lt_add_of_pos_right _ dec_trivial
      end,
  end,
  by rw [hp.coprime_iff_not_dvd, dvd_iff_mod_eq_zero, ← hm₂, nat.add_mul_mod_self_right, mod_eq_of_lt
      (lt_of_lt_of_le (mem_range.1 (mem_of_mem_erase hm₁)) (nat.div_lt_self hp.pos (show 1 < 2, from dec_trivial)))];
     exact ne_of_mem_erase hm₁⟩)⟩

lemma prod_filter_range_p_mul_q_div_two_eq :
  (range (q / 2)).prod (λ n, ((range p).erase 0).prod (+ p * n)) *
  ((range (p / 2).succ).erase 0).prod (+ (q / 2) * p) =
  ((range ((p * q) / 2).succ).filter (coprime p)).prod (λ x, x) :=
calc (range (q / 2)).prod (λ n, ((range p).erase 0).prod (+ p * n)) *
  ((range (p / 2).succ).erase 0).prod (+ (q / 2) * p)
    = (range (q / 2)).prod (λ n, (((range p).erase 0).image (+ p * n)).prod (λ x, x)) *
  (((range (p / 2).succ).erase 0).image (+ (q / 2) * p)).prod (λ x, x) :
  by simp only [prod_image (λ _ _ _ _ h, add_right_cancel h)]; refl
... = ((range (q / 2)).bind (λ x, (erase (range p) 0).image (+ p * x))
         ∪ (erase (range (succ (p / 2))) 0).image (+ q / 2 * p)).prod (λ x, x) :
  have h₁ : finset.bind (range (q / 2)) (λ x, ((range p).erase 0).image (+ p * x)) ∩
      image (+ q / 2 * p) (erase (range (succ (p / 2))) 0) = ∅ :=
    eq_empty_iff_forall_not_mem.2 $ λ x, begin
      suffices : ∀ a, a ≠ 0 → a ≤ p / 2 → a + q / 2 * p = x → ∀ b, b < q / 2 →
        ∀ c, c ≠ 0 → c < p → ¬c + p * b = x,
      { rw inter_comm,
        simpa only [mem_inter, mem_bind, mem_image, mem_range, mem_erase,
          not_and, not_exists, lt_succ_iff, exists_imp_distrib, and_imp] },
      assume a ha0 hap ha b hbq c hc0 hcp hc,
      rw mul_comm at ha,
      rw [← ((nat.div_mod_unique hp.pos).2 ⟨hc, hcp⟩).1,
        ← ((nat.div_mod_unique hp.pos).2 ⟨ha, lt_of_le_of_lt hap
        (nat.div_lt_self hp.pos dec_trivial)⟩).1] at hbq,
      exact lt_irrefl _ hbq
    end,
  have h₂ : ∀ x, x ∈ range (q / 2) → ∀ y, y ∈ range (q / 2) → x ≠ y →
      (erase (range p) 0).image (+ p * x) ∩ image (+ p * y) (erase (range p) 0) = ∅ :=
    λ x hx y hy hxy, begin
      suffices : ∀ z a, a ≠ 0 → a < p → a + p * x = z → ∀ b, b ≠ 0 → b < p → b + p * y ≠ z,
      { simpa only [finset.ext, mem_inter, mem_image, not_mem_empty, iff_false, not_and,
          exists_imp_distrib, not_exists, mem_erase, mem_range, and_imp] },
      assume z a ha0 hap ha b hb0 hbp hb,
      have : (a + p * x) / p = (b + p * y) / p,
      { rw [ha, hb] },
      rw [nat.add_mul_div_left _ _ hp.pos, nat.add_mul_div_left _ _ hp.pos,
        (nat.div_eq_zero_iff hp.pos).2 hap, (nat.div_eq_zero_iff hp.pos).2 hbp] at this,
      simpa only [zero_add, hxy]
    end,
  by rw [prod_union h₁, prod_bind h₂]
... = (((range ((p * q) / 2).succ)).filter (coprime p)).prod (λ x, x) :
  prod_congr (filter_range_p_mul_q_div_two_eq hp hq hp1 hq1 hpq).symm (λ _ _, rfl)

lemma prod_filter_range_p_mul_q_div_two_mod_p_eq :
  ((((range ((p * q) / 2).succ).filter (coprime p)).prod (λ x, x) : ℕ) : zmodp p hp)
  = (-1) ^ (q / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) :=
begin
  rw [← prod_filter_range_p_mul_q_div_two_eq hp hq hp1 hq1 hpq, nat.cast_mul,
    ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul,
    ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul],
  simp only [(prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul).symm,
    cast_add, cast_mul, cast_self_eq_zero, zero_mul, mul_zero, add_zero,
    prod_const, zmodp.prod_range_prime_erase_zero, card_range]
end

lemma prod_filter_range_p_mul_q_not_coprime_eq :
  (((((range ((p * q) / 2).succ).filter (coprime p)).filter
  (λ x, ¬ coprime q x)).prod (λ x, x) : ℕ) : zmodp p hp) =
  q ^ (p / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) :=
have hcard : ((range (p / 2).succ).erase 0).card = p / 2 :=
  by rw [card_erase_of_mem (mem_range.2 (succ_pos _)), card_range, pred_succ],
begin
  rw [← hcard, ← prod_const, hcard, ← prod_mul_distrib, ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul],
  exact eq.symm (prod_bij (λ a _, a * q)
    (λ a ha,
      have ha' : a ≤ p / 2 ∧ a > 0,
        by simpa only [nat.pos_iff_ne_zero, mem_erase, mem_range, lt_succ_iff, and_comm] using ha,
      mem_filter.2 ⟨mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $
        (calc a * q ≤ q * (p / 2) :
            by rw mul_comm; exact mul_le_mul_left _ ha'.1
          ... ≤ _ : by rw [mul_comm p, odd_mul_odd_div_two hq1 hp1];
              exact nat.le_add_right _ _),
        by rw [hp.coprime_iff_not_dvd, hp.dvd_mul, not_or_distrib];
          refine ⟨λ hpa, not_le_of_gt (show p / 2 < p, from nat.div_lt_self hp.pos dec_trivial)
            (le_trans (le_of_dvd ha'.2 hpa) ha'.1), by rwa [← hp.coprime_iff_not_dvd, coprime_primes hp hq]⟩⟩,
      λ H, hq.coprime_iff_not_dvd.1 H (dvd_mul_left _ _)⟩)
    (λ _ _, by simp only [cast_mul, mul_comm])
    (λ _ _ _ _, (nat.mul_right_inj hq.pos).1)
    (λ b hb, have hb' : (b ≤ p * q / 2 ∧ coprime p b) ∧ q ∣ b,
        by simpa only [hq.coprime_iff_not_dvd, mem_filter, mem_range, lt_succ_iff, not_not] using hb,
      have hb0 : b > 0, from nat.pos_of_ne_zero (λ hb0,
        by simpa only [hb0, hp.coprime_iff_not_dvd, dvd_zero, not_true, and_false, false_and] using hb'),
      ⟨b / q, mem_erase.2 ⟨nat.pos_iff_ne_zero.1 (nat.div_pos (le_of_dvd hb0 hb'.2) hq.pos),
        mem_range.2 $ lt_succ_of_le $
          by rw [mul_comm, odd_mul_odd_div_two hq1 hp1] at hb';
          have := @nat.div_le_div_right _ _ hb'.1.1 q;
          rwa [add_comm, nat.add_mul_div_left _ _ hq.pos,
      ((nat.div_eq_zero_iff hq.pos).2 (nat.div_lt_self hq.pos (lt_succ_self _))), zero_add] at this⟩,
        by rw nat.div_mul_cancel hb'.2⟩))
end

lemma prod_range_p_mul_q_filter_coprime_mod_p (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  ((((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, x) : ℕ) : zmodp p hp) =
  (-1) ^ (q / 2) * q ^ (p / 2) :=
have hq0 : (q : zmodp p hp) ≠ 0, by rwa [← nat.cast_zero, ne.def, zmodp.eq_iff_modeq_nat, nat.modeq.modeq_zero_iff,
  ← hp.coprime_iff_not_dvd, coprime_primes hp hq],
(domain.mul_right_inj
  (show (q ^ (p / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) : zmodp p hp) ≠ 0,
    from mul_ne_zero
      (pow_ne_zero _ hq0)
        (suffices h : ∀ (x : ℕ), ¬x = 0 → x ≤ p / 2 → ¬(x : zmodp p hp) = 0,
            by simpa only [ne.def, prod_eq_zero_iff, not_exists, mem_erase, mem_range, lt_succ_iff, and_imp],
          assume x hx0 hxp,
          by rwa [← @nat.cast_zero (zmodp p hp), zmodp.eq_iff_modeq_nat, nat.modeq,
            zero_mod, mod_eq_of_lt (lt_of_le_of_lt hxp (nat.div_lt_self hp.pos (lt_succ_self _)))]))).1 $
have h₁ : (range (succ (p * q / 2))).filter (coprime (p * q)) ∩
      filter (λ x, ¬coprime q x) (filter (coprime p) (range (succ (p * q / 2)))) = ∅,
  by simp only [eq_empty_iff_forall_not_mem, mem_inter, mem_filter];
    exact λ x ⟨⟨_, H1⟩, ⟨_, H2⟩⟩, H2 H1.coprime_mul_left,
calc ((((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, x) : ℕ) : zmodp p hp)
     * (q ^ (p / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) : zmodp p hp)
   = (((range (succ (p * q / 2))).filter (coprime (p * q)) ∪
     filter (λ x, ¬coprime q x) (filter (coprime p) (range (succ (p * q / 2))))).prod (λ x, x) : ℕ) :
  by rw [← prod_filter_range_p_mul_q_not_coprime_eq hp hq hp1 hq1 hpq, ← nat.cast_mul, ← prod_union h₁]
... = (((range ((p * q) / 2).succ).filter (coprime p)).prod (λ x, x) : ℕ) :
  congr_arg coe (prod_congr (finset.ext' $ λ x,
    by simp only [finset.ext, mem_filter, mem_union, coprime_mul_iff_left];
      rw [← and_assoc, ← and_or_distrib_left, and_iff_left]; exact dec_em _) (λ _ _, rfl))
... = _ : by rw [prod_filter_range_p_mul_q_div_two_mod_p_eq hp hq hp1 hq1 hpq];
  cases zmodp.pow_div_two_eq_neg_one_or_one hp hq0; simp only [h, mul_assoc, one_mul, neg_one_mul, neg_neg]

lemma card_range_p_mul_q_filter_not_coprime :
  card (filter (λ x, ¬coprime p x) (range (succ (p * q / 2)))) = (q / 2).succ :=
calc card (filter (λ x, ¬coprime p x) (range (succ (p * q / 2))))
    = card ((range (q / 2).succ).image (* p)) :
  congr_arg card $ finset.ext.2 $ λ x, begin
    rw [mem_filter, mem_range, hp.coprime_iff_not_dvd, not_not, mem_image],
    exact ⟨λ ⟨h, ⟨m, hm⟩⟩, ⟨m, mem_range.2 (lt_of_mul_lt_mul_left
        (by rw ← hm; exact lt_of_lt_of_le h (by rw [succ_le_iff, mul_succ,
            odd_mul_odd_div_two hp1 hq1];
          exact add_lt_add_left (div_lt_self hp.pos (lt_succ_self 1)) _))
        (nat.zero_le p)), hm.symm ▸ mul_comm m p⟩,
      λ ⟨m, hm₁, hm₂⟩, ⟨lt_succ_of_le (by rw [← hm₂, odd_mul_odd_div_two hp1 hq1];
        exact le_trans (by rw mul_comm; exact mul_le_mul_left _
          (le_of_lt_succ (mem_range.1 hm₁))) (le_add_right _ _)),
        by simp only [hm₂.symm, dvd_mul_left]⟩⟩
  end
... = _ : by rw [card_image_of_injective _ (λ _ _ h, (nat.mul_right_inj hp.pos).1 h), card_range]

lemma prod_filter_range_p_mul_q_div_two_eq_prod_product :
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
    (λ x, if (x : zmodp q hq).1 ≤ q / 2 then ((x : zmodp p hp), (x : zmodp q hq))
      else -((x : zmodp p hp), (x : zmodp q hq))) =
  (((range p).erase 0).product ((range (q / 2).succ).erase 0)).prod
    (λ x, ((x.1 : zmodp p hp), (x.2 : zmodp q hq))) :=
have hpqpnat : (((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) : ℤ) = (p * q : ℤ), by simp only [pnat.mk_coe, int.coe_nat_mul],
have hpqpnat' : ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) = p * q, from pnat.mk_coe _ _,
have hpq1 : ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) % 2 = 1,
  from nat.odd_mul_odd hp1 hq1,
have hpq1' : p * q > 1, from one_lt_mul hp.pos hq.gt_one,
have hhq0 : ∀ a : ℕ, coprime q a → a ≠ 0,
  from λ a, imp_not_comm.1 $ by rintro rfl; simp only [hq.coprime_iff_not_dvd, dvd_zero, not_not],
have hpq0 : 0 < p * q / 2, from nat.div_pos (succ_le_of_lt $ one_lt_mul hp.pos hq.gt_one) dec_trivial,
have hinj : ∀ a₁ a₂ : ℕ,
    a₁ ∈ (range (p * q / 2).succ).filter (coprime (p * q)) →
    a₂ ∈ (range (p * q / 2).succ).filter (coprime (p * q)) →
    (if (a₁ : zmodp q hq).1 ≤ q / 2 then ((a₁ : zmodp p hp).1, (a₁ : zmodp q hq).1)
      else ((-a₁ : zmodp p hp).1, (-a₁ : zmodp q hq).1)) =
    (if (a₂ : zmodp q hq).1 ≤ q / 2 then ((a₂ : zmodp p hp).1, (a₂ : zmodp q hq).1)
      else ((-a₂ : zmodp p hp).1, (-a₂ : zmodp q hq).1)) → a₁ = a₂,
  from λ a b ha hb h,
    have ha' : a ≤ (p * q) / 2 ∧ coprime (p * q) a,
      by simpa only [mem_filter, mem_range, lt_succ_iff] using ha,
    have hapq' : a < ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) :=
      lt_of_le_of_lt ha'.1 (div_lt_self (mul_pos hp.pos hq.pos) dec_trivial),
    have hb' : b ≤ (p * q) / 2 ∧ coprime (p * q) b,
      by simpa only [mem_filter, mem_range, lt_succ_iff, coprime_mul_iff_left] using hb,
    have hbpq' : b < ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) :=
      lt_of_le_of_lt hb'.1 (div_lt_self (mul_pos hp.pos hq.pos) dec_trivial),
    have val_inj : ∀ {p : ℕ} (hp : prime p) (x y : zmodp p hp), x.val = y.val ↔ x = y,
      from λ _ _ _ _, ⟨fin.eq_of_veq, fin.veq_of_eq⟩,
    have hbpq0 : (b : zmod (⟨p * q, mul_pos hp.pos hq.pos⟩)) ≠ 0,
      by rw [ne.def, zmod.eq_zero_iff_dvd_nat];
        exact λ h, not_coprime_of_dvd_of_dvd hpq1' (dvd_refl (p * q)) h hb'.2,
    have habneg : ¬((a : zmodp p hp) = -b ∧ (a : zmodp q hq) = -b),
      begin
        rw [← int.cast_coe_nat a, ← int.cast_coe_nat b, ← int.cast_coe_nat a, ← int.cast_coe_nat b,
          ← int.cast_neg, ← int.cast_neg, zmodp.eq_iff_modeq_int, zmodp.eq_iff_modeq_int,
          @int.modeq.modeq_and_modeq_iff_modeq_mul _ _ p q ((coprime_primes hp hq).2 hpq), ← hpqpnat,
          ← zmod.eq_iff_modeq_int, int.cast_coe_nat, int.cast_neg, int.cast_coe_nat],
        assume h,
        rw [← hpqpnat', ← zmod.val_cast_of_lt hbpq', zmod.le_div_two_iff_lt_neg hpq1 hbpq0,
          ← h, zmod.val_cast_of_lt hapq', ← not_le] at hb',
        exact hb'.1 ha'.1,
      end,
    have habneg' : ¬((-a : zmodp p hp) = b ∧ (-a : zmodp q hq) = b),
      by rwa [← neg_inj', neg_neg, ← @neg_inj' _ _ (-a : zmodp q hq), neg_neg],
    suffices (a : zmodp p hp) = b ∧ (a : zmodp q hq) = b,
      by rw [← mod_eq_of_lt hapq', ← mod_eq_of_lt hbpq'];
        rwa [zmodp.eq_iff_modeq_nat, zmodp.eq_iff_modeq_nat,
          nat.modeq.modeq_and_modeq_iff_modeq_mul ((coprime_primes hp hq).2 hpq)] at this,
    by split_ifs at h; simpa only [prod.ext_iff, val_inj, neg_inj'] using h,
have hmem : ∀ a : ℕ,
    a ∈ (range (p * q / 2).succ).filter (coprime (p * q)) →
    (if (a : zmodp q hq).1 ≤ q / 2 then ((a : zmodp p hp).1, (a : zmodp q hq).1)
      else ((-a : zmodp p hp).1, (-a : zmodp q hq).1)) ∈
      ((range p).erase 0).product ((range (succ (q / 2))).erase 0),
  from λ x hx, have hxp : ∀ {p : ℕ} (hp : prime p), (x : zmodp p hp).val = 0 ↔ p ∣ x,
    from λ p hp, by rw [zmodp.val_cast_nat, nat.dvd_iff_mod_eq_zero],
  have hxpneg : ∀ {p : ℕ} (hp : prime p), (-x : zmodp p hp).val = 0 ↔ p ∣ x,
    from λ p hp, by rw [← int.cast_coe_nat x, ← int.cast_neg, ← int.coe_nat_inj',
      zmodp.coe_val_cast_int, int.coe_nat_zero, ← int.dvd_iff_mod_eq_zero, dvd_neg, int.coe_nat_dvd],
  have hxplt : (x : zmodp p hp).val < p := (x : zmodp p hp).2,
  have hxpltneg : (-x : zmodp p hp).val < p := (-x : zmodp p hp).2,
  have hneglt : ¬(x : zmodp q hq).val ≤ q / 2 → (x : zmodp q hq) ≠ 0 → (-x : zmodp q hq).val ≤ q / 2,
    from λ hx₁ hx0, by rwa [zmodp.le_div_two_iff_lt_neg hq hq1 hx0, not_lt] at hx₁,
  by split_ifs; simp only [mem_filter, mem_range, lt_succ_iff, coprime_mul_iff_left,
      hp.coprime_iff_not_dvd, hq.coprime_iff_not_dvd] at hx;
    simp only [mem_product, mem_erase, mem_range, and_true, ne.def, zmodp.eq_zero_iff_dvd_nat hq,
      lt_succ_iff, *, not_false_iff],
prod_bij (λ x _, if (x : zmodp q hq).1 ≤ (q / 2) then ((x : zmodp p hp).val, (x : zmodp q hq).val)
      else ((-x : zmodp p hp).val, (-x : zmodp q hq).val))
  hmem
  (λ a ha, by split_ifs; ext; simp only [zmod.cast_val]; refl)
  hinj
  (surj_on_of_inj_on_of_card_le _ hmem hinj
    (@nat.le_of_add_le_add_right (q / 2 + (p / 2).succ) _ _
      (calc card (finset.product (erase (range p) 0) (erase (range (succ (q / 2))) 0)) + (q / 2 + (p / 2).succ)
            = (p * q) / 2 + 1 :
          by rw [card_product, card_erase_of_mem (mem_range.2 hp.pos), card_erase_of_mem (mem_range.2 (succ_pos _)),
            card_range, card_range, pred_succ, ← add_assoc, ← succ_mul, succ_pred_eq_of_pos hp.pos,
            odd_mul_odd_div_two hp1 hq1, add_succ]
        ... = card (range (p * q / 2).succ) : by rw card_range
        ... = card ((range (p * q / 2).succ).filter (coprime (p * q)) ∪
                    ((range (p * q / 2).succ).filter (λ x, ¬coprime p x)).erase 0 ∪
                    (range (p * q / 2).succ).filter (λ x, ¬coprime q x)) :
          congr_arg card (finset.ext' $ λ x, if h : x = 0
            then by simp only [h, mem_range, zero_lt_succ, true_iff, mem_union, mem_filter, hq.coprime_iff_not_dvd,
              dvd_zero, not_not, and_true, or_true]
            else by simp only [mem_filter, mem_erase, mem_range, lt_succ_iff, mem_union,
              coprime_mul_iff_left, ne.def, h, not_false_iff, true_and];
              rw [or_assoc, ← and_or_distrib_left, ← and_or_distrib_left, ← not_and_distrib];
              simp only [dec_em, and_true])
        ... ≤ card ((range (p * q / 2).succ).filter (coprime (p * q))) +
              card (((range (p * q / 2).succ).filter (λ x, ¬coprime p x)).erase 0) +
              card ((range (p * q / 2).succ).filter (λ x, ¬coprime q x)) :
          le_trans (card_union_le _ _) (add_le_add_right (card_union_le _ _) _)
        ... = _ : by rw [card_erase_of_mem, card_range_p_mul_q_filter_not_coprime hp hq hp1 hq1 hpq,
              mul_comm p q, card_range_p_mul_q_filter_not_coprime hq hp hq1 hp1 hpq.symm, pred_succ,
              add_assoc];
            simp only [hp.coprime_iff_not_dvd, mem_filter, not_not, dvd_zero, mem_range, zero_lt_succ, hpq0, and_true])))

lemma prod_range_div_two_erase_zero :
  ((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp)) ^ 2 * (-1) ^ (p / 2) = -1 :=
have hcard : card (erase (range (succ (p / 2))) 0) = p / 2,
  by rw [card_erase_of_mem (mem_range.2 (succ_pos _)), card_range, pred_succ],
have hp2 : p / 2 < p, from div_lt_self hp.pos dec_trivial,
have h₁ : (range (p / 2).succ).erase 0 = ((range p).erase 0).filter (λ x, (x : zmodp p hp).val ≤ p / 2) :=
  finset.ext.2 (λ a,
  ⟨λ h, mem_filter.2 $ by rw [mem_erase, mem_range, lt_succ_iff] at h;
    exact ⟨mem_erase.2 ⟨h.1, mem_range.2 (lt_of_le_of_lt h.2 hp2)⟩,
      by rw zmodp.val_cast_of_lt hp (lt_of_le_of_lt h.2 hp2); exact h.2⟩,
  λ h, mem_erase.2 ⟨(mem_erase.1 (mem_filter.1 h).1).1,
    by rw [mem_filter, mem_erase, mem_range] at h;
    rw [mem_range, lt_succ_iff, ← zmodp.val_cast_of_lt hp h.1.2]; exact h.2⟩⟩),
have hmem : ∀ x ∈ (range (p / 2).succ).erase 0, x ≠ 0 ∧ x ≤ p / 2,
  from λ x hx, by simpa only [mem_erase, mem_range, lt_succ_iff] using hx,
have hmemv : ∀ x ∈ (range (p / 2).succ).erase 0, (x : zmodp p hp).val = x,
  from λ x hx, zmodp.val_cast_of_lt hp (lt_of_le_of_lt (hmem x hx).2 hp2),
have hmem0 : ∀ x ∈ (range (p / 2).succ).erase 0, (x : zmodp p hp) ≠ 0,
  from λ x hx heq, (hmem x hx).1 $ by rw [← hmemv x hx, heq, zero_val],
have hmem0' : ∀ x ∈ (range (p / 2).succ).erase 0, (-x : zmodp p hp) ≠ 0,
  from λ x hx, neg_ne_zero.2 (hmem0 x hx),
have h₂ : ((range (p / 2).succ).erase 0).prod (λ x : ℕ, (x : zmodp p hp) * -1) =
    (((range p).erase 0).filter (λ x : ℕ, ¬(x : zmodp p hp).val ≤ p / 2)).prod (λ x, (x : zmodp p hp)) :=
  prod_bij (λ a _, (-a : zmodp p hp).1)
    (λ a ha,  mem_filter.2 ⟨mem_erase.2 ⟨fin.vne_of_ne (hmem0' a ha), mem_range.2 (-a : zmodp p hp).2⟩,
        by simp only [cast_val, neg_neg, not_lt, zmodp.le_div_two_iff_lt_neg hp hp1 (hmem0' a ha), hmemv a ha, (hmem a ha).2]⟩)
    (λ _ _, by simp only [cast_val, mul_neg_one])
    (λ a₁ a₂ ha₁ ha₂ h,
      by rw [← hmemv a₁ ha₁, ← hmemv a₂ ha₂]; exact fin.veq_of_eq (by rw neg_inj (fin.eq_of_veq h)))
    (λ b hb,
      have hb' : (b ≠ 0 ∧ b < p) ∧ (¬(b : zmodp p hp).1 ≤ p / 2),
        by simpa only [mem_filter, mem_erase, mem_range] using hb,
      have hbv : (b : zmodp p hp).1 = b, from zmodp.val_cast_of_lt hp hb'.1.2,
      have hb0 : (b : zmodp p hp) ≠ 0, from λ heq, hb'.1.1 $ by rw [← hbv, heq, zero_val],
    ⟨(-b : zmodp p hp).1, mem_erase.2 ⟨fin.vne_of_ne (neg_ne_zero.2 hb0 : _),
      mem_range.2 $ lt_succ_of_le $ by rw [← not_lt, ← zmodp.le_div_two_iff_lt_neg hp hp1 hb0]; exact hb'.2⟩,
      by simp only [cast_val, neg_neg, hbv]⟩),
calc ((((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp)) ^ 2)) * (-1) ^ (p / 2) =
  ((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp)) *
  ((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp) * -1) :
  by rw [prod_mul_distrib, _root_.pow_two, mul_assoc, prod_const, hcard]
... = (((range p).erase 0).filter (λ x : ℕ, (x : zmodp p hp).val ≤ p / 2)).prod (λ x, (x : zmodp p hp)) *
    (((range p).erase 0).filter (λ x : ℕ, ¬(x : zmodp p hp).val ≤ p / 2)).prod (λ x, (x : zmodp p hp)) :
  by rw [h₂, h₁]
... = ((range p).erase 0).prod (λ x, (x : zmodp p hp)) :
  begin
    rw ← prod_union,
    { exact finset.prod_congr (filter_union_filter_neg_eq _) (λ _ _, rfl) },
    { exact filter_inter_filter_neg_eq _ }
  end
... = -1 : zmodp.prod_range_prime_erase_zero _

lemma range_p_product_range_q_div_two_prod :
  (((range p).erase 0).product ((range (q / 2).succ).erase 0)).prod
    (λ x, ((x.1 : zmodp p hp), (x.2 : zmodp q hq))) =
  ((-1) ^ (q / 2), (-1) ^ (p / 2) * (-1) ^ (p / 2 * (q / 2))) :=
have hcard : card (erase (range (succ (q / 2))) 0) = q / 2,
  by rw [card_erase_of_mem (mem_range.2 (succ_pos _)), card_range, pred_succ],
have finset.prod (erase (range (succ (q / 2))) 0) (λ x : ℕ, (x : zmodp q hq)) ^ 2 = -((-1 : zmodp q hq) ^ (q / 2)),
  from (domain.mul_right_inj (show (-1 : zmodp q hq) ^ (q / 2) ≠ 0, from pow_ne_zero _ (neg_ne_zero.2 zero_ne_one.symm))).1 $
  by rw [prod_range_div_two_erase_zero hq hp hq1 hp1 hpq.symm, ← neg_mul_eq_neg_mul, ← _root_.pow_add, ← two_mul,
    pow_mul, _root_.pow_two, neg_one_mul, neg_neg, _root_.one_pow],
have finset.prod (erase (range (succ (q / 2))) 0) (λ x, (x : zmodp q hq)) ^ card (erase (range p) 0) =
  (- 1) ^ (p / 2) * ((-1) ^ (p / 2 * (q / 2))),
 by rw [card_erase_of_mem (mem_range.2 hp.pos), card_range, pred_eq_sub_one,
   ← two_mul_odd_div_two hp1, pow_mul, this, mul_comm (p / 2), pow_mul, ← _root_.mul_pow, neg_one_mul],
by simp only [prod_product, (prod_mk_prod _ _ _).symm, prod_pow, -range_succ, prod_nat_pow, prod_const, *,
  zmodp.prod_range_prime_erase_zero hp]

lemma prod_range_p_mul_q_div_two_ite_eq :
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
  (λ x, if (x : zmodp q hq).1 ≤ (q / 2) then ((x : zmodp p hp), (x : zmodp q hq))
    else -((x : zmodp p hp), (x : zmodp q hq))) =
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, if (x : zmodp q hq).1 ≤ q / 2 then 1 else -1) *
  ((-1) ^ (q / 2) * q ^ (p / 2), (-1) ^ (p / 2) * p ^ (q / 2)) :=
calc ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
  (λ x, if (x : zmodp q hq).1 ≤ (q / 2) then ((x : zmodp p hp), (x : zmodp q hq))
    else -((x : zmodp p hp), (x : zmodp q hq))) =
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
  (λ x, (if (x : zmodp q hq).1 ≤ (q / 2) then 1 else -1) * ((x : zmodp p hp), (x : zmodp q hq))) :
  prod_congr rfl (λ _ _, by split_ifs; simp only [one_mul, neg_one_mul])
... = _ : by rw [prod_mul_distrib, ← prod_mk_prod,
    prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul,
    prod_range_p_mul_q_filter_coprime_mod_p hp hq hp1 hq1 hpq,
    prod_hom (coe : ℕ → zmodp q hq) nat.cast_one nat.cast_mul,
    mul_comm p q, prod_range_p_mul_q_filter_coprime_mod_p hq hp hq1 hp1 hpq.symm]

end quadratic_reciprocity_aux

open quadratic_reciprocity_aux

variables {p q : ℕ} (hp : prime p) (hq : prime q)

namespace zmodp

def legendre_sym (a p : ℕ) (hp : prime p) : ℤ :=
if (a : zmodp p hp) = 0 then 0 else if ∃ b : zmodp p hp, b ^ 2 = a then 1 else -1

lemma legendre_sym_eq_pow (a p : ℕ) (hp : prime p) : (legendre_sym a p hp : zmodp p hp) = (a ^ (p / 2)) :=
if ha : (a : zmodp p hp) = 0
then by simp only [legendre_sym, ha, if_pos, _root_.zero_pow (nat.div_pos hp.ge_two (succ_pos 1)), int.cast_zero]
else
(prime.eq_two_or_odd hp).elim
  (λ hp2, begin subst hp2,
    suffices : ∀ a : zmodp 2 prime_two,
      (((ite (a = 0) 0 (ite (∃ (b : zmodp 2 hp), b ^ 2 = a) 1 (-1))) : ℤ) : zmodp 2 prime_two) = a ^ (2 / 2),
    { exact this a },
    exact dec_trivial,
   end)
  (λ hp1, have _ := euler_criterion hp ha,
    have (-1 : zmodp p hp) ≠ 1, from (ne_neg_self hp hp1 zero_ne_one.symm).symm,
    by cases zmodp.pow_div_two_eq_neg_one_or_one hp ha;
    simp only [legendre_sym, *, if_pos, if_false, int.cast_one, int.cast_neg] at *)

lemma legendre_sym_eq_one_or_neg_one (a : ℕ) (hp : prime p) (ha : (a : zmodp p hp) ≠ 0) :
  legendre_sym a p hp = 1 ∨ legendre_sym a p hp = -1 :=
by unfold legendre_sym; rw if_neg ha; split_ifs; [exact or.inl rfl, exact or.inr rfl]

theorem quadratic_reciprocity (hp : prime p) (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  legendre_sym p q hq * legendre_sym q p hp = (-1) ^ ((p / 2) * (q / 2)) :=
have hneg_one_or_one : ((range (p * q / 2).succ).filter (coprime (p * q))).prod
    (λ (x : ℕ), if (x : zmodp q hq).val ≤ q / 2 then (1 : zmodp p hp × zmodp q hq) else -1) = 1 ∨
    ((range (p * q / 2).succ).filter (coprime (p * q))).prod
    (λ (x : ℕ), if (x : zmodp q hq).val ≤ q / 2 then (1 : zmodp p hp × zmodp q hq) else -1) = -1 :=
  finset.induction_on ((range (p * q / 2).succ).filter (coprime (p * q))) (or.inl rfl)
    (λ a s h ih, by cases ih; simp only [prod_insert h, ih]; split_ifs;
      simp only [one_mul, neg_one_mul, neg_neg, eq_self_iff_true, true_or, or_true]),
have haux : ∀ {p:ℕ} {n1 n2:ℤ} (hp : prime p) (hp1 : p%2=1)
  (hn1 : n1 = 1 ∨ n1 = -1) (hn2 : n2 = 1 ∨ n2 = -1),
    (n1 : zmodp p hp) = n2 ↔ n1 = n2,
  from λ p n1 n2 hp hp1 hn1 hn2, ⟨match n1, n2, hn1, hn2 with
    | _, _, or.inl rfl, or.inl rfl, H := rfl
    | _, _, or.inl rfl, or.inr rfl, H := (ne_neg_self hp hp1 one_ne_zero
        (by simpa only [int.cast_one, int.cast_neg] using H)).elim
    | _, _, or.inr rfl, or.inl rfl, H := (ne_neg_self hp hp1 one_ne_zero
        (by simpa only [int.cast_one, int.cast_neg] using H.symm)).elim
    | _, _, or.inr rfl, or.inr rfl, H := rfl
    end,
  by rintro rfl; refl⟩,
have h : (q ^ (p / 2) : zmodp p hp) = (1:ℤ) ∧ (p ^ (q / 2) : zmodp q hq) = ((-1) ^ (p / 2 * (q / 2)):ℤ) ∨
    (q ^ (p / 2) : zmodp p hp) = (-1:ℤ) ∧ (p ^ (q / 2) : zmodp q hq) = (-((-1) ^ (p / 2 * (q / 2))):ℤ) :=
  begin
    have := prod_filter_range_p_mul_q_div_two_eq_prod_product hp hq hp1 hq1 hpq,
    rw [prod_range_p_mul_q_div_two_ite_eq hp hq hp1 hq1 hpq,
      range_p_product_range_q_div_two_prod hp hq hp1 hq1 hpq] at this,
    simp only [int.cast_pow, int.cast_neg, int.cast_one],
    cases hneg_one_or_one with h h;
      simp only [h, one_mul, neg_one_mul, prod.ext_iff, prod.fst_neg, prod.snd_neg] at this,
    { left, split,
      { rw [← domain.mul_left_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) : ((-1) ^ (q / 2) : zmodp p hp) ≠ 0), this.1, mul_one] },
      { rw [← domain.mul_left_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) : ((-1) ^ (p / 2) : zmodp q hq) ≠ 0), this.2] } },
    { right, split,
      { rw [← domain.mul_left_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) : ((-1) ^ (q / 2) : zmodp p hp) ≠ 0), mul_neg_one, eq_neg_iff_eq_neg, this.1] },
      { rw [← domain.mul_left_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) : ((-1) ^ (p / 2) : zmodp q hq) ≠ 0), ← neg_eq_iff_neg_eq.1 this.2, neg_mul_eq_mul_neg] } }
  end,
begin
  simp only [(legendre_sym_eq_pow p q hq).symm, (legendre_sym_eq_pow q p hp).symm] at h,
  rw [haux hp hp1 (legendre_sym_eq_one_or_neg_one q hp (zmodp.prime_ne_zero hp hq hpq)) (or.inl rfl)] at h,
  rw [haux hp hp1 (legendre_sym_eq_one_or_neg_one q hp (zmodp.prime_ne_zero hp hq hpq)) (or.inr rfl)] at h,
  rw [haux hq hq1 (legendre_sym_eq_one_or_neg_one p hq (zmodp.prime_ne_zero hq hp hpq.symm)) (neg_one_pow_eq_or _)] at h,
  rw [haux hq hq1 (legendre_sym_eq_one_or_neg_one p hq (zmodp.prime_ne_zero hq hp hpq.symm))] at h,
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩,
  { rw [h1, h2, mul_one] },
  { rw [h1, h2, mul_neg_one, neg_neg] },
  { rcases neg_one_pow_eq_or (p/2*(q/2)) with h | h; rw h,
    { exact or.inr rfl }, { exact or.inl (neg_neg _) } }
end

lemma is_square_iff_is_square_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q % 2 = 1) :
  (∃ a : zmodp p hp, a ^ 2 = q) ↔ ∃ b : zmodp q hq, b ^ 2 = p :=
if hpq : p = q then by subst hpq else
have h1 : ((p / 2) * (q / 2)) % 2 = 0,
  from (dvd_iff_mod_eq_zero _ _).1
    (dvd_mul_of_dvd_left ((dvd_iff_mod_eq_zero _ _).2 $
    by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp1]; refl) _),
begin
  have := quadratic_reciprocity hp hq (odd_of_mod_four_eq_one hp1) hq1 hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym,
    if_neg (zmodp.prime_ne_zero hp hq hpq),
    if_neg (zmodp.prime_ne_zero hq hp (ne.symm hpq))] at this,
  split_ifs at this with h2 h3 h3 h2 h3 h3,
  { exact iff_of_true h3 h2 },
  { exact absurd this dec_trivial },
  { exact absurd this dec_trivial },
  { exact iff_of_false h3 h2 }
end

lemma is_square_iff_is_not_square_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
  (hpq : p ≠ q) : (∃ a : zmodp p hp, a ^ 2 = q) ↔ ¬∃ b : zmodp q hq, b ^ 2 = p :=
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
  split_ifs at this with h2 h3 h3 h2 h3 h3,
  { exact absurd this dec_trivial },
  { exact iff_of_false h3 (not_not_intro h2) },
  { exact iff_of_true h3 h2 },
  { exact absurd this dec_trivial },
end

end zmodp