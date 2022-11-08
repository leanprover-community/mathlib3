/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import number_theory.legendre_symbol.quadratic_reciprocity

/-!
# Lemmas of Gauss and Eisenstein

This file contains code for the proof of the Lemmas of Gauss and Eisenstein
on the Legendre symbol. The main results are `zmod.gauss_lemma_aux` and
`zmod.eisenstein_lemma_aux`.
-/

open function finset nat finite_field zmod
open_locale big_operators nat

namespace zmod

section wilson

variables (p : ℕ) [fact p.prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp] lemma wilsons_lemma : ((p - 1)! : zmod p) = -1 :=
begin
  refine
  calc ((p - 1)! : zmod p) = (∏ x in Ico 1 (succ (p - 1)), x) :
    by rw [← finset.prod_Ico_id_eq_factorial, prod_nat_cast]
                               ... = (∏ x : (zmod p)ˣ, x) : _
                               ... = -1 : by simp_rw [← units.coe_hom_apply,
    ← (units.coe_hom (zmod p)).map_prod, prod_univ_units_id_eq_neg_one, units.coe_hom_apply,
    units.coe_neg, units.coe_one],
  have hp : 0 < p := (fact.out p.prime).pos,
  symmetry,
  refine prod_bij (λ a _, (a : zmod p).val) _ _ _ _,
  { intros a ha,
    rw [mem_Ico, ← nat.succ_sub hp, nat.succ_sub_one],
    split,
    { apply nat.pos_of_ne_zero, rw ← @val_zero p,
      assume h, apply units.ne_zero a (val_injective p h) },
    { exact val_lt _ } },
  { intros a ha, simp only [cast_id, nat_cast_val], },
  { intros _ _ _ _ h, rw units.ext_iff, exact val_injective p h },
  { intros b hb,
    rw [mem_Ico, nat.succ_le_iff, ← succ_sub hp, succ_sub_one, pos_iff_ne_zero] at hb,
    refine ⟨units.mk0 b _, finset.mem_univ _, _⟩,
    { assume h, apply hb.1, apply_fun val at h,
      simpa only [val_cast_of_lt hb.right, val_zero] using h },
    { simp only [val_cast_of_lt hb.right, units.coe_mk0], } }
end

@[simp] lemma prod_Ico_one_prime : (∏ x in Ico 1 p, (x : zmod p)) = -1 :=
begin
  conv in (Ico 1 p) { rw [← succ_sub_one p, succ_sub (fact.out p.prime).pos] },
  rw [← prod_nat_cast, finset.prod_Ico_id_eq_factorial, wilsons_lemma]
end

end wilson

end zmod

section gauss_eisenstein

namespace zmod

/-- The image of the map sending a non zero natural number `x ≤ p / 2` to the absolute value
  of the element of interger in the interval `(-p/2, p/2]` congruent to `a * x` mod p is the set
  of non zero natural numbers `x` such that `x ≤ p / 2` -/
lemma Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
  (p : ℕ) [hp : fact p.prime] (a : zmod p) (hap : a ≠ 0) :
  (Ico 1 (p / 2).succ).1.map (λ x, (a * x).val_min_abs.nat_abs) =
  (Ico 1 (p / 2).succ).1.map (λ a, a) :=
begin
  have he : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x ≠ 0 ∧ x ≤ p / 2,
    by simp [nat.lt_succ_iff, nat.succ_le_iff, pos_iff_ne_zero] {contextual := tt},
  have hep : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x < p,
    from λ x hx, lt_of_le_of_lt (he hx).2 (nat.div_lt_self hp.1.pos dec_trivial),
  have hpe : ∀ {x}, x ∈ Ico 1 (p / 2).succ → ¬ p ∣ x,
    from λ x hx hpx, not_lt_of_ge (le_of_dvd (nat.pos_of_ne_zero (he hx).1) hpx) (hep hx),
  have hmem : ∀ (x : ℕ) (hx : x ∈ Ico 1 (p / 2).succ),
    (a * x : zmod p).val_min_abs.nat_abs ∈ Ico 1 (p / 2).succ,
  { assume x hx,
    simp [hap, char_p.cast_eq_zero_iff (zmod p) p, hpe hx, lt_succ_iff, succ_le_iff,
        pos_iff_ne_zero, nat_abs_val_min_abs_le _], },
  have hsurj : ∀ (b : ℕ) (hb : b ∈ Ico 1 (p / 2).succ),
    ∃ x ∈ Ico 1 (p / 2).succ, b = (a * x : zmod p).val_min_abs.nat_abs,
  { assume b hb,
    refine ⟨(b / a : zmod p).val_min_abs.nat_abs, mem_Ico.mpr ⟨_, _⟩, _⟩,
    { apply nat.pos_of_ne_zero,
      simp only [div_eq_mul_inv, hap, char_p.cast_eq_zero_iff (zmod p) p, hpe hb, not_false_iff,
        val_min_abs_eq_zero, inv_eq_zero, int.nat_abs_eq_zero, ne.def, mul_eq_zero, or_self] },
    { apply lt_succ_of_le, apply nat_abs_val_min_abs_le },
    { rw nat_cast_nat_abs_val_min_abs,
      split_ifs,
      { erw [mul_div_cancel' _ hap, val_min_abs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), int.nat_abs_of_nat], },
      { erw [mul_neg, mul_div_cancel' _ hap, nat_abs_val_min_abs_neg,
          val_min_abs_def_pos, val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (mem_Ico.1 hb).2),
          int.nat_abs_of_nat] } } },
  exact multiset.map_eq_map_of_bij_of_nodup _ _ (finset.nodup _) (finset.nodup _)
    (λ x _, (a * x : zmod p).val_min_abs.nat_abs) hmem (λ _ _, rfl)
    (inj_on_of_surj_on_of_card_le _ hmem hsurj le_rfl) hsurj
end

private lemma gauss_lemma_aux₁ (p : ℕ) [fact p.prime] [fact (p % 2 = 1)]
  {a : ℤ} (hap : (a : zmod p) ≠ 0) :
  (a^(p / 2) * (p / 2)! : zmod p) =
  (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card * (p / 2)! :=
calc (a ^ (p / 2) * (p / 2)! : zmod p) =
    (∏ x in Ico 1 (p / 2).succ, a * x) :
  by rw [prod_mul_distrib, ← prod_nat_cast, prod_Ico_id_eq_factorial,
      prod_const, card_Ico, succ_sub_one]; simp
... = (∏ x in Ico 1 (p / 2).succ, (a * x : zmod p).val) : by simp
... = (∏ x in Ico 1 (p / 2).succ,
    (if (a * x : zmod p).val ≤ p / 2 then 1 else -1) *
      (a * x : zmod p).val_min_abs.nat_abs) :
  prod_congr rfl $ λ _ _, begin
    simp only [nat_cast_nat_abs_val_min_abs],
    split_ifs; simp
  end
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card *
    (∏ x in Ico 1 (p / 2).succ, (a * x : zmod p).val_min_abs.nat_abs) :
  have (∏ x in Ico 1 (p / 2).succ,
        if (a * x : zmod p).val ≤ p / 2 then (1 : zmod p) else -1) =
      (∏ x in (Ico 1 (p / 2).succ).filter
        (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2), -1),
    from prod_bij_ne_one (λ x _ _, x)
      (λ x, by split_ifs; simp * at * {contextual := tt})
      (λ _ _ _ _ _ _, id)
      (λ b h _, ⟨b, by simp [-not_le, *] at *⟩)
      (by intros; split_ifs at *; simp * at *),
  by rw [prod_mul_distrib, this]; simp
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card * (p / 2)! :
  by rw [← prod_nat_cast, finset.prod_eq_multiset_prod,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap,
      ← finset.prod_eq_multiset_prod, prod_Ico_id_eq_factorial]

lemma gauss_lemma_aux (p : ℕ) [hp : fact p.prime] [fact (p % 2 = 1)]
  {a : ℤ} (hap : (a : zmod p) ≠ 0) :
  (a^(p / 2) : zmod p) = (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
(mul_left_inj'
    (show ((p / 2)! : zmod p) ≠ 0,
      by rw [ne.def, char_p.cast_eq_zero_iff (zmod p) p, hp.1.dvd_factorial, not_le];
          exact nat.div_lt_self hp.1.pos dec_trivial)).1 $
  by simpa using gauss_lemma_aux₁ p hap

/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
lemma gauss_lemma {p : ℕ} [fact p.prime] {a : ℤ} (hp : p ≠ 2) (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = (-1) ^ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
begin
  haveI hp' : fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩,
  have : (legendre_sym p a : zmod p) = (((-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card : ℤ) : zmod p) :=
    by { rw [legendre_sym.eq_pow, gauss_lemma_aux p ha0]; simp },
  cases legendre_sym.eq_one_or_neg_one p ha0;
  cases neg_one_pow_eq_or ℤ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card;
  simp [*, ne_neg_self p one_ne_zero, (ne_neg_self p one_ne_zero).symm] at *
end

private lemma eisenstein_lemma_aux₁ (p : ℕ) [fact p.prime] [hp2 : fact (p % 2 = 1)]
  {a : ℕ} (hap : (a : zmod p) ≠ 0) :
  ((∑ x in Ico 1 (p / 2).succ, a * x : ℕ) : zmod 2) =
    ((Ico 1 (p / 2).succ).filter
      ((λ x : ℕ, p / 2 < (a * x : zmod p).val))).card +
      ∑ x in Ico 1 (p / 2).succ, x
    + (∑ x in Ico 1 (p / 2).succ, (a * x) / p : ℕ) :=
have hp2 : (p : zmod 2) = (1 : ℕ), from (eq_iff_modeq_nat _).2 hp2.1,
calc ((∑ x in Ico 1 (p / 2).succ, a * x : ℕ) : zmod 2)
    = ((∑ x in Ico 1 (p / 2).succ, ((a * x) % p + p * ((a * x) / p)) : ℕ) : zmod 2) :
  by simp only [mod_add_div]
... = (∑ x in Ico 1 (p / 2).succ, ((a * x : ℕ) : zmod p).val : ℕ) +
    (∑ x in Ico 1 (p / 2).succ, (a * x) / p : ℕ) :
  by simp only [val_nat_cast];
    simp [sum_add_distrib, mul_sum.symm, nat.cast_add, nat.cast_mul, nat.cast_sum, hp2]
... = _ : congr_arg2 (+)
  (calc ((∑ x in Ico 1 (p / 2).succ, ((a * x : ℕ) : zmod p).val : ℕ) : zmod 2)
      = ∑ x in Ico 1 (p / 2).succ,
          ((((a * x : zmod p).val_min_abs +
            (if (a * x : zmod p).val ≤ p / 2 then 0 else p)) : ℤ) : zmod 2) :
        by simp only [(val_eq_ite_val_min_abs _).symm]; simp [nat.cast_sum]
  ... = ((Ico 1 (p / 2).succ).filter
        (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card +
      ((∑ x in Ico 1 (p / 2).succ, (a * x : zmod p).val_min_abs.nat_abs) : ℕ) :
    by { simp [ite_cast, add_comm, sum_add_distrib, finset.sum_ite, hp2, nat.cast_sum], }
  ... = _ : by rw [finset.sum_eq_multiset_sum,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap,
      ← finset.sum_eq_multiset_sum];
    simp [nat.cast_sum]) rfl

lemma eisenstein_lemma_aux (p : ℕ) [fact p.prime] [fact (p % 2 = 1)]
  {a : ℕ} (ha2 : a % 2 = 1) (hap : (a : zmod p) ≠ 0) :
  ((Ico 1 (p / 2).succ).filter
    ((λ x : ℕ, p / 2 < (a * x : zmod p).val))).card
  ≡ ∑ x in Ico 1 (p / 2).succ, (x * a) / p [MOD 2] :=
have ha2 : (a : zmod 2) = (1 : ℕ), from (eq_iff_modeq_nat _).2 ha2,
(eq_iff_modeq_nat 2).1 $ sub_eq_zero.1 $
  by simpa [add_left_comm, sub_eq_add_neg, finset.mul_sum.symm, mul_comm, ha2, nat.cast_sum,
            add_neg_eq_iff_eq_add.symm, neg_eq_self_mod_two, add_assoc]
    using eq.symm (eisenstein_lemma_aux₁ p hap)

lemma div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) : a / b =
  ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :=
calc a / b = (Ico 1 (a / b).succ).card : by simp
... = ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :
  congr_arg _ $ finset.ext $ λ x,
    have x * b ≤ a → x ≤ c,
      from λ h, le_trans (by rwa [le_div_iff_mul_le hb0]) hc,
    by simp [lt_succ_iff, le_div_iff_mul_le hb0]; tauto

/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`  -/
private lemma sum_Ico_eq_card_lt {p q : ℕ} :
  ∑ a in Ico 1 (p / 2).succ, (a * q) / p = ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter $
    λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q).card :=
if hp0 : p = 0 then by simp [hp0, finset.ext_iff]
else
  calc ∑ a in Ico 1 (p / 2).succ, (a * q) / p =
    ∑ a in Ico 1 (p / 2).succ,
      ((Ico 1 (q / 2).succ).filter (λ x, x * p ≤ a * q)).card :
    finset.sum_congr rfl $ λ x hx,
      div_eq_filter_card (nat.pos_of_ne_zero hp0)
        (calc x * q / p ≤ (p / 2) * q / p :
            nat.div_le_div_right (mul_le_mul_of_nonneg_right
              (le_of_lt_succ $ (mem_Ico.mp hx).2)
              (nat.zero_le _))
          ... ≤ _ : nat.div_mul_div_le_div _ _ _)
  ... = _ : by rw [← card_sigma];
    exact card_congr (λ a _, ⟨a.1, a.2⟩)
      (by simp only [mem_filter, mem_sigma, and_self, forall_true_iff, mem_product]
        {contextual := tt})
      (λ ⟨_, _⟩ ⟨_, _⟩, by simp only [prod.mk.inj_iff, eq_self_iff_true, and_self, heq_iff_eq,
        forall_true_iff] {contextual := tt})
      (λ ⟨b₁, b₂⟩ h, ⟨⟨b₁, b₂⟩,
        by revert h; simp only [mem_filter, eq_self_iff_true, exists_prop_of_true, mem_sigma,
          and_self, forall_true_iff, mem_product] {contextual := tt}⟩)

/-- Each of the sums in this lemma is the cardinality of the set integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
lemma sum_mul_div_add_sum_mul_div_eq_mul (p q : ℕ) [hp : fact p.prime]
  (hq0 : (q : zmod p) ≠ 0) :
  ∑ a in Ico 1 (p / 2).succ, (a * q) / p +
  ∑ a in Ico 1 (q / 2).succ, (a * p) / q =
  (p / 2) * (q / 2) :=
begin
  have hswap : ((Ico 1 (q / 2).succ ×ˢ Ico 1 (p / 2).succ).filter
    (λ x : ℕ × ℕ, x.2 * q ≤ x.1 * p)).card =
  ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter
    (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p)).card :=
  card_congr (λ x _, prod.swap x)
    (λ ⟨_, _⟩, by simp only [mem_filter, and_self, prod.swap_prod_mk, forall_true_iff, mem_product]
      {contextual := tt})
    (λ ⟨_, _⟩ ⟨_, _⟩, by simp only [prod.mk.inj_iff, eq_self_iff_true, and_self, prod.swap_prod_mk,
      forall_true_iff] {contextual := tt})
    (λ ⟨x₁, x₂⟩ h, ⟨⟨x₂, x₁⟩, by revert h; simp only [mem_filter, eq_self_iff_true, and_self,
      exists_prop_of_true, prod.swap_prod_mk, forall_true_iff, mem_product] {contextual := tt}⟩),
  have hdisj : disjoint
    ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter
      (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q))
    ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter
      (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p)),
  { apply disjoint_filter.2 (λ x hx hpq hqp, _),
    have hxp : x.1 < p, from lt_of_le_of_lt
      (show x.1 ≤ p / 2, by simp only [*, lt_succ_iff, mem_Ico, mem_product] at *; tauto)
      (nat.div_lt_self hp.1.pos dec_trivial),
    have : (x.1 : zmod p) = 0,
    { simpa [hq0] using congr_arg (coe : ℕ → zmod p) (le_antisymm hpq hqp) },
    apply_fun zmod.val at this,
    rw [val_cast_of_lt hxp, val_zero] at this,
    simpa only [this, nonpos_iff_eq_zero, mem_Ico, one_ne_zero, false_and, mem_product] using hx },
  have hunion : (Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter
      (λ x : ℕ × ℕ, x.2 * p ≤ x.1 * q) ∪
    (Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter
      (λ x : ℕ × ℕ, x.1 * q ≤ x.2 * p) =
    (Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ),
  from finset.ext (λ x, by have := le_total (x.2 * p) (x.1 * q);
    simp only [mem_union, mem_filter, mem_Ico, mem_product]; tauto),
  rw [sum_Ico_eq_card_lt, sum_Ico_eq_card_lt, hswap, ← card_disjoint_union hdisj, hunion,
    card_product],
  simp only [card_Ico, tsub_zero, succ_sub_succ_eq_sub]
end

lemma eisenstein_lemma {p : ℕ} [fact p.prime] (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1)
  (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = (-1)^∑ x in Ico 1 (p / 2).succ, (x * a) / p :=
begin
  haveI hp' : fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩,
  have ha0' : ((a : ℤ) : zmod p) ≠ 0 := by { norm_cast, exact ha0 },
  rw [neg_one_pow_eq_pow_mod_two, gauss_lemma hp ha0', neg_one_pow_eq_pow_mod_two,
      (by norm_cast : ((a : ℤ) : zmod p) = (a : zmod p)),
      show _ = _, from eisenstein_lemma_aux p ha1 ha0]
end

end zmod

end gauss_eisenstein
