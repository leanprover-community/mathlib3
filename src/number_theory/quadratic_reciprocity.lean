/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import field_theory.finite
import data.zmod.basic
import data.nat.parity

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

open function finset nat finite_field zmod

namespace zmod

variables (p q : ℕ) [fact p.prime] [fact q.prime]

@[simp] lemma card_units : fintype.card (units (zmod p)) = p - 1 :=
by rw [card_units, card]

/-- Fermat's Little Theorem: for every unit `a` of `zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem fermat_little_units {p : ℕ} [fact p.prime] (a : units (zmod p)) :
  a ^ (p - 1) = 1 :=
by rw [← card_units p, pow_card_eq_one]

/-- Fermat's Little Theorem: for all nonzero `a : zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem fermat_little {a : zmod p} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
begin
  have := fermat_little_units (units.mk0 a ha),
  apply_fun (coe : units (zmod p) → zmod p) at this,
  simpa,
end

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion_units (x : units (zmod p)) :
  (∃ y : units (zmod p), y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
begin
  cases nat.prime.eq_two_or_odd ‹p.prime› with hp2 hp_odd,
  { resetI, subst p, refine iff_of_true ⟨1, _⟩ _; apply subsingleton.elim  },
  obtain ⟨g, hg⟩ := is_cyclic.exists_generator (units (zmod p)),
  obtain ⟨n, hn⟩ : x ∈ powers g, { rw powers_eq_gpowers, apply hg },
  split,
  { rintro ⟨y, rfl⟩, rw [← pow_mul, two_mul_odd_div_two hp_odd, fermat_little_units], },
  { subst x, assume h,
    have key : 2 * (p / 2) ∣ n * (p / 2),
    { rw [← pow_mul] at h,
      rw [two_mul_odd_div_two hp_odd, ← card_units, ← order_of_eq_card_of_forall_mem_gpowers hg],
      apply order_of_dvd_of_pow_eq_one h },
    have : 0 < p / 2 := nat.div_pos (show fact (1 < p), by apply_instance) dec_trivial,
    obtain ⟨m, rfl⟩ := dvd_of_mul_dvd_mul_right this key,
    refine ⟨g ^ m, _⟩,
    rw [mul_comm, pow_mul], },
end

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion {a : zmod p} (ha : a ≠ 0) :
  (∃ y : zmod p, y ^ 2 = a) ↔ a ^ (p / 2) = 1 :=
begin
  apply (iff_congr _ (by simp [units.ext_iff])).mp (euler_criterion_units p (units.mk0 a ha)),
  simp only [units.ext_iff, _root_.pow_two, units.coe_mk0, units.coe_mul],
  split, { rintro ⟨y, hy⟩, exact ⟨y, hy⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [_root_.zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

lemma exists_pow_two_eq_neg_one_iff_mod_four_ne_three :
  (∃ y : zmod p, y ^ 2 = -1) ↔ p % 4 ≠ 3 :=
begin
  cases nat.prime.eq_two_or_odd ‹p.prime› with hp2 hp_odd,
  { resetI, subst p, exact dec_trivial },
  change fact (p % 2 = 1) at hp_odd, resetI,
  have neg_one_ne_zero : (-1 : zmod p) ≠ 0, from mt neg_eq_zero.1 one_ne_zero,
  rw [euler_criterion p neg_one_ne_zero, neg_one_pow_eq_pow_mod_two],
  cases mod_two_eq_zero_or_one (p / 2) with p_half_even p_half_odd,
  { rw [p_half_even, _root_.pow_zero, eq_self_iff_true, true_iff],
    contrapose! p_half_even with hp,
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp],
    exact dec_trivial },
  { rw [p_half_odd, _root_.pow_one,
        iff_false_intro (ne_neg_self p one_ne_zero).symm, false_iff, not_not],
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl] at p_half_odd,
    rw [_root_.fact, ← nat.mod_mul_left_mod _ 2, show 2 * 2 = 4, from rfl] at hp_odd,
    have hp : p % 4 < 4, from nat.mod_lt _ dec_trivial,
    revert hp hp_odd p_half_odd,
    generalize : p % 4 = k, revert k, exact dec_trivial }
end

lemma pow_div_two_eq_neg_one_or_one {a : zmod p} (ha : a ≠ 0) :
  a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
begin
  cases nat.prime.eq_two_or_odd ‹p.prime› with hp2 hp_odd,
  { resetI, subst p, revert a ha, exact dec_trivial },
  rw [← mul_self_eq_one_iff, ← _root_.pow_add, ← two_mul, two_mul_odd_div_two hp_odd],
  exact fermat_little p ha
end

/-- Wilson's Lemma: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp] lemma wilsons_lemma : (nat.fact (p - 1) : zmod p) = -1 :=
begin
  refine
  calc (nat.fact (p - 1) : zmod p) = (Ico 1 (succ (p - 1))).prod (λ (x : ℕ), x) :
    by rw [← finset.prod_Ico_id_eq_fact, prod_nat_cast]
                               ... = finset.univ.prod (λ x : units (zmod p), x) : _
                               ... = -1 :
    by rw [prod_hom _ (coe : units (zmod p) → zmod p),
           prod_univ_units_id_eq_neg_one, units.coe_neg, units.coe_one],
  have hp : 0 < p := nat.prime.pos ‹p.prime›,
  symmetry,
  refine prod_bij (λ a _, (a : zmod p).val) _ _ _ _,
  { intros a ha,
    rw [Ico.mem, ← nat.succ_sub hp, nat.succ_sub_one],
    split,
    { apply nat.pos_of_ne_zero, rw ← @val_zero p,
      assume h, apply units.coe_ne_zero a (val_injective p h) },
    { exact val_lt _ } },
  { intros a ha, simp only [cast_id, nat_cast_val], },
  { intros _ _ _ _ h, rw units.ext_iff, exact val_injective p h },
  { intros b hb,
    rw [Ico.mem, nat.succ_le_iff, ← succ_sub hp, succ_sub_one, nat.pos_iff_ne_zero] at hb,
    refine ⟨units.mk0 b _, finset.mem_univ _, _⟩,
    { assume h, apply hb.1, apply_fun val at h,
      simpa only [val_cast_of_lt hb.right, val_zero] using h },
    { simp only [val_cast_of_lt hb.right, units.coe_mk0], } }
end

@[simp] lemma prod_Ico_one_prime : (Ico 1 p).prod (λ x, (x : zmod p)) = -1 :=
begin
  conv in (Ico 1 p) { rw [← succ_sub_one p, succ_sub (nat.prime.pos ‹p.prime›)] },
  rw [← prod_nat_cast, finset.prod_Ico_id_eq_fact, wilsons_lemma]
end

end zmod

/-- The image of the map sending a non zero natural number `x ≤ p / 2` to the absolute value
  of the element of interger in the interval `(-p/2, p/2]` congruent to `a * x` mod p is the set
  of non zero natural numbers `x` such that `x ≤ p / 2` -/
lemma Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
  (p : ℕ) [hp : fact p.prime] (a : zmod p) (hap : a ≠ 0) :
  (Ico 1 (p / 2).succ).1.map (λ x, (a * x).val_min_abs.nat_abs) =
  (Ico 1 (p / 2).succ).1.map (λ a, a) :=
begin
  have he : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x ≠ 0 ∧ x ≤ p / 2,
    by simp [nat.lt_succ_iff, nat.succ_le_iff, nat.pos_iff_ne_zero] {contextual := tt},
  have hep : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x < p,
    from λ x hx, lt_of_le_of_lt (he hx).2 (nat.div_lt_self hp.pos dec_trivial),
  have hpe : ∀ {x}, x ∈ Ico 1 (p / 2).succ → ¬ p ∣ x,
    from λ x hx hpx, not_lt_of_ge (le_of_dvd (nat.pos_of_ne_zero (he hx).1) hpx) (hep hx),
  have hmem : ∀ (x : ℕ) (hx : x ∈ Ico 1 (p / 2).succ),
    (a * x : zmod p).val_min_abs.nat_abs ∈ Ico 1 (p / 2).succ,
  { assume x hx,
    simp [hap, char_p.cast_eq_zero_iff (zmod p) p, hpe hx, lt_succ_iff, succ_le_iff,
        nat.pos_iff_ne_zero, nat_abs_val_min_abs_le _], },
  have hsurj : ∀ (b : ℕ) (hb : b ∈ Ico 1 (p / 2).succ),
    ∃ x ∈ Ico 1 (p / 2).succ, b = (a * x : zmod p).val_min_abs.nat_abs,
  { assume b hb,
    refine ⟨(b / a : zmod p).val_min_abs.nat_abs, Ico.mem.mpr ⟨_, _⟩, _⟩,
    { apply nat.pos_of_ne_zero,
      simp only [div_eq_mul_inv, hap, char_p.cast_eq_zero_iff (zmod p) p, hpe hb, not_false_iff,
        val_min_abs_eq_zero, inv_eq_zero, int.nat_abs_eq_zero, ne.def, mul_eq_zero_iff', or_self] },
      { apply lt_succ_of_le, apply nat_abs_val_min_abs_le },
      { rw cast_nat_abs_val_min_abs,
        split_ifs,
        { erw [mul_div_cancel' _ hap, val_min_abs_def_pos, val_cast_of_lt (hep hb),
            if_pos (le_of_lt_succ (Ico.mem.1 hb).2), int.nat_abs_of_nat], },
        { erw [mul_neg_eq_neg_mul_symm, mul_div_cancel' _ hap, nat_abs_val_min_abs_neg,
            val_min_abs_def_pos, val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (Ico.mem.1 hb).2),
            int.nat_abs_of_nat] } } },
  exact multiset.map_eq_map_of_bij_of_nodup _ _ (finset.nodup _) (finset.nodup _)
    (λ x _, (a * x : zmod p).val_min_abs.nat_abs) hmem (λ _ _, rfl)
    (inj_on_of_surj_on_of_card_le _ hmem hsurj (le_refl _)) hsurj
end

private lemma gauss_lemma_aux₁ (p : ℕ) [hp : fact p.prime] [hp2 : fact (p % 2 = 1)]
  {a : ℕ} (hap : (a : zmod p) ≠ 0) :
  (a^(p / 2) * (p / 2).fact : zmod p) =
  (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card * (p / 2).fact :=
calc (a ^ (p / 2) * (p / 2).fact : zmod p) =
    (Ico 1 (p / 2).succ).prod (λ x, a * x) :
  by rw [prod_mul_distrib, ← prod_nat_cast, ← prod_nat_cast, prod_Ico_id_eq_fact,
      prod_const, Ico.card, succ_sub_one]; simp
... = (Ico 1 (p / 2).succ).prod (λ x, (a * x : zmod p).val) : by simp
... = (Ico 1 (p / 2).succ).prod
    (λ x, (if (a * x : zmod p).val ≤ p / 2 then 1 else -1) *
      (a * x : zmod p).val_min_abs.nat_abs) :
  prod_congr rfl $ λ _ _, begin
    simp only [cast_nat_abs_val_min_abs],
    split_ifs; simp
  end
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card *
    (Ico 1 (p / 2).succ).prod (λ x, (a * x : zmod p).val_min_abs.nat_abs) :
  have (Ico 1 (p / 2).succ).prod
        (λ x, if (a * x : zmod p).val ≤ p / 2 then (1 : zmod p) else -1) =
      ((Ico 1 (p / 2).succ).filter
        (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).prod (λ _, -1),
    from prod_bij_ne_one (λ x _ _, x)
      (λ x, by split_ifs; simp * at * {contextual := tt})
      (λ _ _ _ _ _ _, id)
      (λ b h _, ⟨b, by simp [-not_le, *] at *⟩)
      (by intros; split_ifs at *; simp * at *),
  by rw [prod_mul_distrib, this]; simp
... = (-1)^((Ico 1 (p / 2).succ).filter
      (λ x : ℕ, ¬(a * x : zmod p).val ≤ p / 2)).card * (p / 2).fact :
  by rw [← prod_nat_cast, finset.prod_eq_multiset_prod,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap,
      ← finset.prod_eq_multiset_prod, prod_Ico_id_eq_fact]

private lemma gauss_lemma_aux₂ (p : ℕ) [hp : fact p.prime] [hp2 : fact (p % 2 = 1)]
  {a : ℕ} (hap : (a : zmod p) ≠ 0) :
  (a^(p / 2) : zmod p) = (-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
(domain.mul_right_inj
    (show ((p / 2).fact : zmod p) ≠ 0,
      by rw [ne.def, char_p.cast_eq_zero_iff (zmod p) p, hp.dvd_fact, not_le];
          exact nat.div_lt_self hp.pos dec_trivial)).1 $
  by simpa using gauss_lemma_aux₁ p hap

private lemma eisenstein_lemma_aux₁ (p : ℕ) [hp : fact p.prime] [hp2 : fact (p % 2 = 1)]
  {a : ℕ} (hap : (a : zmod p) ≠ 0) :
  (((Ico 1 (p / 2).succ).sum (λ x, a * x) : ℕ) : zmod 2) =
    ((Ico 1 (p / 2).succ).filter
      ((λ x : ℕ, p / 2 < (a * x : zmod p).val))).card +
      (Ico 1 (p / 2).succ).sum (λ x, x)
    + ((Ico 1 (p / 2).succ).sum (λ x, (a * x) / p) : ℕ) :=
have hp2 : (p : zmod 2) = (1 : ℕ), from (eq_iff_modeq_nat _).2 hp2,
calc (((Ico 1 (p / 2).succ).sum (λ x, a * x) : ℕ) : zmod 2)
    = (((Ico 1 (p / 2).succ).sum (λ x, (a * x) % p + p * ((a * x) / p)) : ℕ) : zmod 2) :
  by simp only [mod_add_div]
... = ((Ico 1 (p / 2).succ).sum (λ x, ((a * x : ℕ) : zmod p).val) : ℕ) +
    ((Ico 1 (p / 2).succ).sum (λ x, (a * x) / p) : ℕ) :
  by simp only [val_cast_nat];
    simp [sum_add_distrib, mul_sum.symm, nat.cast_add, nat.cast_mul, sum_nat_cast, hp2]
... = _ : congr_arg2 (+)
  (calc (((Ico 1 (p / 2).succ).sum (λ x, ((a * x : ℕ) : zmod p).val) : ℕ) : zmod 2)
      = (Ico 1 (p / 2).succ).sum
          (λ x, ((((a * x : zmod p).val_min_abs +
            (if (a * x : zmod p).val ≤ p / 2 then 0 else p)) : ℤ) : zmod 2)) :
        by simp only [(val_eq_ite_val_min_abs _).symm]; simp [sum_nat_cast]
  ... = ((Ico 1 (p / 2).succ).filter
        (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card +
      (((Ico 1 (p / 2).succ).sum (λ x, (a * x : zmod p).val_min_abs.nat_abs)) : ℕ) :
    by { simp [ite_cast, add_comm, sum_add_distrib, finset.sum_ite, hp2, sum_nat_cast], }
  ... = _ : by rw [finset.sum_eq_multiset_sum,
      Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap,
      ← finset.sum_eq_multiset_sum];
    simp [sum_nat_cast]) rfl

private lemma eisenstein_lemma_aux₂ (p : ℕ) [hp : fact p.prime] [hp2 : fact (p % 2 = 1)]
  {a : ℕ} (ha2 : a % 2 = 1) (hap : (a : zmod p) ≠ 0) :
  ((Ico 1 (p / 2).succ).filter
    ((λ x : ℕ, p / 2 < (a * x : zmod p).val))).card
  ≡ (Ico 1 (p / 2).succ).sum (λ x, (x * a) / p) [MOD 2] :=
have ha2 : (a : zmod 2) = (1 : ℕ), from (eq_iff_modeq_nat _).2 ha2,
(eq_iff_modeq_nat 2).1 $ sub_eq_zero.1 $
  by simpa [add_left_comm, sub_eq_add_neg, finset.mul_sum.symm, mul_comm, ha2, sum_nat_cast,
            add_neg_eq_iff_eq_add.symm, neg_eq_self_mod_two]
    using eq.symm (eisenstein_lemma_aux₁ p hap)

lemma div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) : a / b =
  ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :=
calc a / b = (Ico 1 (a / b).succ).card : by simp
... = ((Ico 1 c.succ).filter (λ x, x * b ≤ a)).card :
  congr_arg _$ finset.ext.2 $ λ x,
    have x * b ≤ a → x ≤ c,
      from λ h, le_trans (by rwa [le_div_iff_mul_le _ _ hb0]) hc,
    by simp [lt_succ_iff, le_div_iff_mul_le _ _ hb0]; tauto

/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
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
private lemma sum_mul_div_add_sum_mul_div_eq_mul (p q : ℕ) [hp : fact p.prime]
  (hq0 : (q : zmod p) ≠ 0) :
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
    have : (x.1 : zmod p) = 0,
    { simpa [hq0] using congr_arg (coe : ℕ → zmod p) (le_antisymm hpq hqp) },
    apply_fun zmod.val at this,
    rw [val_cast_of_lt hxp, val_zero] at this,
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

-- move this
instance prime_two' : fact (nat.prime 2) := nat.prime_two

-- move this
instance prime_three' : fact (nat.prime 3) := nat.prime_three

/-- An auxilliary target type for the Legendre symbol -/
@[derive decidable_eq, derive fintype, derive field]
def legendre_sym_aux.type := zmod 3

/-- Intermediate definition of the Legendre symbol -/
def legendre_sym_aux (p : ℕ) (a : zmod p) : legendre_sym_aux.type :=
if      a = 0           then  0
else if a ^ (p / 2) = 1 then  1
                        else -1

namespace legendre_sym_aux

lemma cases : ∀ x : type, x = 0 ∨ x = 1 ∨ x = -1 := dec_trivial

/-- Interpret an auxilliary Legendre symbol as integer -/
def to_int : type →* ℤ :=
{ to_fun := zmod.val_min_abs,
  map_one' := rfl,
  map_mul' := dec_trivial }

@[simp] lemma to_int_neg_one : to_int (-1) = -1 := rfl
@[simp] lemma to_int_zero : to_int 0 = 0 := rfl
@[simp] lemma to_int_one : to_int 1 = 1 := rfl
@[simp] lemma to_int_neg : ∀ x : type, to_int (-x) = - to_int x := dec_trivial

lemma to_int_injective : function.injective to_int := dec_trivial

-- set_option pp.all true

-- move this
lemma val_min_abs_one (p : ℕ) [hp : fact (1 < p)] : val_min_abs (1 : zmod p) = 1 :=
begin
  rw [zmod.val_min_abs_def_pos, zmod.val_one, if_pos, int.coe_nat_one],
  rwa [le_div_iff_mul_le 1 p (show 0 < 2, from dec_trivial), one_mul]
end

-- move this
lemma val_neg_one (n : ℕ) [fact (0 < n)] : (-1 : zmod n).val = n - 1 :=
begin
  resetI, cases n,
  { exfalso, exact nat.not_lt_zero 0 ‹0 < 0› },
  cases n, { refl },
  show int.nat_mod (-(fin.val 1 : ℕ)) _ = (n + 1),
  rw [fin.val_one, ← int.coe_nat_inj', int.nat_mod, int.coe_nat_one,
    int.to_nat_of_nonneg (int.mod_nonneg _ _)],
  { have : (n.succ + 1 - 1) % (n.succ + 1) = n + 1,
    { exact nat.mod_eq_of_lt (lt_add_one (n + 1)) },
    conv_rhs { rw ← this },
    show (-1 % (n+1+1) : ℤ) = (n + 1) % (n+1+1),
    rw [← @int.add_mod_self_left (n+1+1) (-1), add_neg_cancel_right] },
  { exact_mod_cast nat.succ_ne_zero _ }
end

-- move this
lemma val_min_abs_neg_one (p : ℕ) (hp : 2 < p) : val_min_abs (-1 : zmod p) = -1 :=
begin
  haveI hp1 : fact (1 < p) := lt_trans dec_trivial hp,
  rw [zmod.val_min_abs_def_pos, val_neg_one, if_neg],
  { rw [sub_eq_iff_eq_add', ← sub_eq_add_neg, int.coe_nat_sub (le_of_lt hp1), int.coe_nat_one] },
  { rwa [le_div_iff_mul_le _ p (show 0 < 2, from dec_trivial), not_le],
    rw [nat.mul_sub_right_distrib, mul_two, one_mul, nat.lt_sub_right_iff_add_lt],
    exact add_lt_add_left hp p }
end

lemma coe_to_int_injective (p : ℕ) (hp : 2 < p) :
  function.injective (λ x : type, (to_int x : zmod p)) :=
begin
  apply function.injective_of_has_left_inverse,
  refine ⟨λ x, x.val_min_abs, _⟩,
  haveI hp1 : _root_.fact (1 < p) := lt_trans dec_trivial hp,
  intro x,
  show (val_min_abs (to_int x : zmod p) : type) = x,
  rcases cases x with rfl|rfl|rfl,
  { rw [to_int_zero, int.cast_zero, zmod.val_min_abs_zero, int.cast_zero] },
  { rw [to_int_one, int.cast_one, val_min_abs_one, int.cast_one] },
  { simp only [to_int_neg_one, int.cast_neg, int.cast_one, val_min_abs_neg_one p hp] },
end

lemma eq_pow (p : ℕ) [hp : fact p.prime] (a : zmod p) :
  (to_int (legendre_sym_aux p a) : zmod p) = (a ^ (p / 2)) :=
begin
  resetI, cases hp.eq_two_or_odd with hp2 hp_odd,
  { subst p, revert a, exact dec_trivial },
  rw legendre_sym_aux,
  change fact (p % 2 = 1) at hp_odd,
  by_cases ha : a = 0,
  { rw [if_pos ha, ha, _root_.zero_pow (nat.div_pos (hp.two_le) (succ_pos 1))], refl },
  { rw if_neg ha,
    have : (-1 : zmod p) ≠ 1, from (ne_neg_self p one_ne_zero).symm,
    cases zmod.pow_div_two_eq_neg_one_or_one p ha with h h,
    { rw [if_pos h, h, to_int_one, int.cast_one], },
    { rw [h, if_neg this, to_int_neg_one, int.cast_neg, int.cast_one], } }
end

lemma one (p : ℕ) [hp : fact p.prime] : legendre_sym_aux p 1 = 1 :=
begin
  resetI, cases eq_or_lt_of_le (hp.two_le) with hp2 hp3,
  { subst p, exact dec_trivial },
  apply coe_to_int_injective p hp3,
  show (to_int (legendre_sym_aux p 1) : zmod p) = (1 : ℤ),
  rw [eq_pow, _root_.one_pow, int.cast_one]
end

lemma mul (p : ℕ) [hp : fact p.prime] (a b : zmod p) :
  legendre_sym_aux p (a * b) = legendre_sym_aux p a * legendre_sym_aux p b :=
begin
  resetI, cases eq_or_lt_of_le (hp.two_le) with hp2 hp3,
  { subst p, revert a b, exact dec_trivial },
  apply coe_to_int_injective p hp3,
  show (to_int (legendre_sym_aux p (a * b)) : zmod p) =
    to_int (legendre_sym_aux p a * legendre_sym_aux p b),
  simp only [eq_pow, to_int.map_mul, int.cast_mul, _root_.mul_pow],
end

def hom (p : ℕ) [hp : fact p.prime] : zmod p →* type :=
{ to_fun := legendre_sym_aux p,
  map_one' := one p,
  map_mul' := mul p }

end legendre_sym_aux

/-- The Legendre symbol as multiplicative map from `zmod p` to `ℤ`, where `p` is a prime.

* `0` if `a` is `0` modulo `p`;
* `1` if `a ^ (p / 2)` is `1` modulo `p`
   (by `zmod.euler_criterion` this is equivalent to “`a` is a square modulo `p`”);
* `-1` otherwise.

Unfortunately, we get the syntax `legendre_sym_hom p a`
for what is usually written as “`a` over `p`”.
For that reason, we also provide `legendre_sym a p`. -/
def legendre_sym_hom (p : ℕ) [fact p.prime] : zmod p →* ℤ :=
(legendre_sym_aux.to_int).comp (legendre_sym_aux.hom p)

section legendre_sym

variables (p q : ℕ) [fact p.prime] [fact q.prime]

/-- The Legendre symbol of `a` and `p` is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a ^ (p / 2)` is `1` modulo `p`
  (if `p` is prime, this is equivalent to “`a` is a nonzero square modulo `p`”,
   by `zmod.euler_criterion`);
* `-1` otherwise.

This symbol is typically used under the assumption that `p` is prime. -/
def legendre_sym (a p : ℕ) : ℤ :=
if      (a : zmod p) = 0           then  0
else if (a : zmod p) ^ (p / 2) = 1 then  1
                                   else -1

lemma legendre_sym_eq_neg_one_or_zero_or_one (a p : ℕ) :
  legendre_sym a p = -1 ∨ legendre_sym a p = 0 ∨ legendre_sym a p = 1 :=
by { delta legendre_sym, split_ifs; tauto }

@[simp] lemma legendre_sym_zero (p : ℕ) : legendre_sym 0 p = 0 :=
if_pos nat.cast_zero

@[simp] lemma legendre_sym_one (p : ℕ) [fact (1 < p)] : legendre_sym 1 p = 1 :=
begin
  delta legendre_sym, rw [if_neg, if_pos],
  { rw [nat.cast_one, _root_.one_pow] },
  { rw [nat.cast_one], exact one_ne_zero },
end

@[simp] lemma legendre_sym_hom_apply (a : ℕ) : legendre_sym_hom p a = legendre_sym a p :=
show (legendre_sym_aux.to_int : legendre_sym_aux.type → ℤ) (ite _ _ _) = ite _ _ _,
by split_ifs; refl

lemma legendre_sym_mod (a p : ℕ) :
  legendre_sym a p = legendre_sym (a % p) p :=
by { delta legendre_sym, simp only [cast_mod_nat], split_ifs; refl }

lemma legendre_sym_two_right (a : ℕ) :
  legendre_sym a 2 = a % 2 :=
begin
  rw [legendre_sym_mod, show (a % 2 : ℤ) = ((a % 2 : ℕ) : ℤ), from rfl],
  cases mod_two_eq_zero_or_one a with h h,
  { rw [h, legendre_sym_zero, int.coe_nat_zero] },
  { rw [h, legendre_sym_one, int.coe_nat_one] }
end

lemma legendre_sym_eq_pow (a p : ℕ) [hp : fact p.prime] :
  (legendre_sym a p : zmod p) = (a ^ (p / 2)) :=
by { rw ← legendre_sym_hom_apply, exact legendre_sym_aux.eq_pow p a }

lemma legendre_sym_eq_one_or_neg_one (a p : ℕ) (ha : (a : zmod p) ≠ 0) :
  legendre_sym a p = -1 ∨ legendre_sym a p = 1 :=
by unfold legendre_sym; split_ifs; simp only [*, eq_self_iff_true, or_true, true_or] at *

lemma legendre_sym_eq_zero_iff (a p : ℕ) :
  legendre_sym a p = 0 ↔ (a : zmod p) = 0 :=
begin
  split,
  { classical, contrapose,
    assume ha, cases legendre_sym_eq_one_or_neg_one a p ha with h h,
    all_goals { rw h, norm_num } },
  { assume ha, rw [legendre_sym, if_pos ha] }
end

lemma legendre_sym_mul (a b p : ℕ) [fact p.prime] :
  legendre_sym (a * b) p = legendre_sym a p * legendre_sym b p :=
by simp only [← legendre_sym_hom_apply, nat.cast_mul, (legendre_sym_hom p).map_mul]

/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
lemma zmod.gauss_lemma {a : ℕ} [hp1 : fact (p % 2 = 1)] (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym a p = (-1) ^ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
have (legendre_sym a p : zmod p) = (((-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card : ℤ) : zmod p),
  by rw [legendre_sym_eq_pow, gauss_lemma_aux₂ p ha0]; simp,
begin
  cases legendre_sym_eq_one_or_neg_one a p ha0;
  cases @neg_one_pow_eq_or ℤ _  ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card;
  simp [*, ne_neg_self p one_ne_zero, (ne_neg_self p one_ne_zero).symm] at *
end

lemma legendre_sym_eq_one_iff {a : ℕ} (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym a p = 1 ↔ (∃ b : zmod p, b ^ 2 = a) :=
begin
  rw [zmod.euler_criterion p ha0, legendre_sym, if_neg ha0],
  split_ifs,
  { simp only [h, eq_self_iff_true] },
  finish -- this is quite slow. I'm actually surprised that it can close the goal at all!
end

lemma zmod.eisenstein_lemma [hp1 : fact (p % 2 = 1)] {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym a p = (-1)^(Ico 1 (p / 2).succ).sum (λ x, (x * a) / p) :=
by rw [neg_one_pow_eq_pow_mod_two, zmod.gauss_lemma p ha0, neg_one_pow_eq_pow_mod_two,
    show _ = _, from eisenstein_lemma_aux₂ p ha1 ha0]

/-- Quadratic reciprocity gives a relation between the Legendre symbols
 `legendre_sym p q` and `legendre_sym q p` for two distinct odd primes `p` and `q`. -/
theorem quadratic_reciprocity [hp1 : fact (p % 2 = 1)] [hq1 : fact (q % 2 = 1)] (hpq : p ≠ q) :
  legendre_sym p q * legendre_sym q p = (-1) ^ ((p / 2) * (q / 2)) :=
have hpq0 : (p : zmod q) ≠ 0, from prime_ne_zero q p hpq.symm,
have hqp0 : (q : zmod p) ≠ 0, from prime_ne_zero p q hpq,
by rw [zmod.eisenstein_lemma q hp1 hpq0, zmod.eisenstein_lemma p hq1 hqp0,
  ← _root_.pow_add, sum_mul_div_add_sum_mul_div_eq_mul q p hpq0, mul_comm]

lemma legendre_sym_swap [hp1 : fact (p % 2 = 1)] [hq1 : fact (q % 2 = 1)] (hpq : p ≠ q) :
  legendre_sym p q = legendre_sym q p * (-1) ^ ((p / 2) * (q / 2)) :=
begin
  have : (legendre_sym q p)^2 = 1,
  { cases legendre_sym_eq_one_or_neg_one q p (prime_ne_zero p q hpq) with h h,
    all_goals { rw [h], refl } },
  calc legendre_sym p q = (legendre_sym p q) * (legendre_sym q p)^2 : by rw [this, mul_one]
     ... = (legendre_sym q p) * ((legendre_sym p q) * (legendre_sym q p)) : by ring
     ... = legendre_sym q p * (-1) ^ ((p / 2) * (q / 2)) : by rw quadratic_reciprocity p q hpq
end

lemma legendre_sym_two [hp1 : fact (p % 2 = 1)] : legendre_sym 2 p = (-1) ^ (p / 4 + p / 2) :=
have hp2 : p ≠ 2, from mt (congr_arg (% 2)) (by simpa using hp1),
have hp22 : p / 2 / 2 = _ := div_eq_filter_card (show 0 < 2, from dec_trivial)
  (nat.div_le_self (p / 2) 2),
have hcard : (Ico 1 (p / 2).succ).card = p / 2, by simp,
have hx2 : ∀ x ∈ Ico 1 (p / 2).succ, (2 * x : zmod p).val = 2 * x,
  from λ x hx, have h2xp : 2 * x < p,
      from calc 2 * x ≤ 2 * (p / 2) : mul_le_mul_of_nonneg_left
        (le_of_lt_succ $ by finish) dec_trivial
      ... < _ : by conv_rhs {rw [← mod_add_div p 2, add_comm, show p % 2 = 1, from hp1]}; exact lt_succ_self _,
    by rw [← nat.cast_two, ← nat.cast_mul, val_cast_of_lt h2xp],
have hdisj : disjoint
    ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val))
    ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)),
  from disjoint_filter.2 (λ x hx, by simp [hx2 _ hx, mul_comm]),
have hunion :
    ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val)) ∪
    ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)) =
    Ico 1 (p / 2).succ,
  begin
    rw [filter_union_right],
    conv_rhs {rw [← @filter_true _ (Ico 1 (p / 2).succ)]},
    exact filter_congr (λ x hx, by simp [hx2 _ hx, lt_or_le, mul_comm])
  end,
begin
  rw [zmod.gauss_lemma p (prime_ne_zero p 2 hp2),
    neg_one_pow_eq_pow_mod_two, @neg_one_pow_eq_pow_mod_two _ _ (p / 4 + p / 2)],
  refine congr_arg2 _ rfl ((eq_iff_modeq_nat 2).1 _),
  rw [show 4 = 2 * 2, from rfl, ← nat.div_div_eq_div_mul, hp22, nat.cast_add,
    ← sub_eq_iff_eq_add', sub_eq_add_neg, neg_eq_self_mod_two,
    ← nat.cast_add, ← card_disjoint_union hdisj, hunion, hcard]
end

lemma exists_pow_two_eq_two_iff [hp1 : fact (p % 2 = 1)] :
  (∃ a : zmod p, a ^ 2 = 2) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
have hp2 : ((2 : ℕ) : zmod p) ≠ 0,
  from prime_ne_zero p 2 (λ h, by simpa [h] using hp1),
have hpm4 : p % 4 = p % 8 % 4, from (nat.mod_mul_left_mod p 2 4).symm,
have hpm2 : p % 2 = p % 8 % 2, from (nat.mod_mul_left_mod p 4 2).symm,
begin
  rw [show (2 : zmod p) = (2 : ℕ), by simp, ← legendre_sym_eq_one_iff p hp2,
    legendre_sym_two p, neg_one_pow_eq_one_iff_even (show (-1 : ℤ) ≠ 1, from dec_trivial),
    even_add, even_div, even_div],
  have := nat.mod_lt p (show 0 < 8, from dec_trivial),
  resetI, rw _root_.fact at hp1,
  revert this hp1,
  erw [hpm4, hpm2],
  generalize hm : p % 8 = m,
  clear hm,
  revert m,
  exact dec_trivial
end

lemma exists_pow_two_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) [hq1 : fact (q % 2 = 1)] :
  (∃ a : zmod p, a ^ 2 = q) ↔ ∃ b : zmod q, b ^ 2 = p :=
if hpq : p = q then by resetI; subst hpq else
have h1 : ((p / 2) * (q / 2)) % 2 = 0,
  from (dvd_iff_mod_eq_zero _ _).1
    (dvd_mul_of_dvd_left ((dvd_iff_mod_eq_zero _ _).2 $
    by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp1]; refl) _),
begin
  haveI hp_odd : fact (p % 2 = 1) := odd_of_mod_four_eq_one hp1,
  have hpq0 : (p : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : (q : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym,
    if_neg hqp0, if_neg hpq0] at this,
  rw [zmod.euler_criterion q hpq0, zmod.euler_criterion p hqp0],
  split_ifs at this; simp *; contradiction,
end

lemma exists_pow_two_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3)
  (hq3 : q % 4 = 3) (hpq : p ≠ q) : (∃ a : zmod p, a ^ 2 = q) ↔ ¬∃ b : zmod q, b ^ 2 = p :=
have h1 : ((p / 2) * (q / 2)) % 2 = 1,
  from nat.odd_mul_odd
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp3]; refl)
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hq3]; refl),
begin
  haveI hp_odd : fact (p % 2 = 1) := odd_of_mod_four_eq_three hp3,
  haveI hq_odd : fact (q % 2 = 1) := odd_of_mod_four_eq_three hq3,
  have hpq0 : (p : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : (q : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym,
    if_neg hpq0, if_neg hqp0] at this,
  rw [zmod.euler_criterion q hpq0, zmod.euler_criterion p hqp0],
  split_ifs at this; simp *; contradiction
end

end legendre_sym
