/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space_two

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables (X : Type*) [mul_one_class X] [topological_space X]
variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)
variables (R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space (units (zmod d) × units (ℤ_[p])) R)
variables {c : ℕ} [fact (0 < d)]
variables [algebra ℚ R] [norm_one_class R]

set_option old_structure_cmd true

open_locale big_operators

/-- A variant of `zmod` which has type `finset _`. -/
def zmod' (n : ℕ) (h : 0 < n) : finset (zmod n) :=
  @finset.univ _ (@zmod.fintype n (fact_iff.2 h))

--def zmod' (n : ℕ) (h : fact (0 < n)) : finset (zmod n) :=
--  @set.to_finset _ (@set.univ (zmod n)) (@set_fintype _ (@zmod.fintype n h) set.univ _)

lemma succ_eq_bUnion_equi_class : zmod' (d*p^m.succ) (mul_prime_pow_pos p d m.succ) =
  (zmod' (d*p^m) (mul_prime_pow_pos p d m)).bUnion
    (λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (nat.le_succ m)) a)) :=
begin
  ext y, simp only [exists_prop, finset.mem_bUnion, set.mem_to_finset], split,
  any_goals { intro h, },
  { refine ⟨(y : zmod (d * p^m)), _, _⟩,
    { rw finset.mem_def, exact finset.mem_univ y, },
    { rw mem_equi_class, }, },
  { rw finset.mem_def, exact finset.mem_univ y, },
end

example {R S : Type*} [ring R] [ring S] {f : R →+* S} {x y : R} (h : f x = 0) :
  x ∈ ring_hom.ker f := by refine (ring_hom.mem_ker f).mpr h

example {a b c : ℤ} (h : a ∣ (b - c) ) : -(b - c) = c - b := neg_sub b c

lemma mul_pow_lt_mul_pow_succ (m : ℕ) : d * p ^ m < d * p ^ m.succ :=
begin
  apply mul_lt_mul',
  any_goals { simp, },
  { apply nat.pow_lt_pow_succ, apply nat.prime.one_lt, apply fact.out, },
  { apply fact.out, },
end

example (a b c : ℕ) (h1 : a < b) (h2 : b ≤ c) : a < c := gt_of_ge_of_gt h2 h1

lemma val_le_val (n m : ℕ) [fact (0 < m)] (h : m ≤ n) (y : zmod n) : (y.val : zmod m).val ≤ y.val :=
begin
  by_cases y.val < m,
  { have := zmod.val_cast_of_lt h, rw this, },
  { push_neg at h,
    apply le_of_lt, apply gt_of_ge_of_gt h _, apply zmod.val_lt (y.val : zmod m), },
end

open zmod padic_int

lemma val_le_val' (n m : ℕ) [fact (0 < m)] [fact (0 < n)] (h : m ≤ n) (y : zmod n) :
  (y : zmod m).val ≤ y.val :=
begin
  rw ← nat_cast_val, apply val_le_val _ _ h _,
end

lemma equi_class_eq (f : locally_constant (zmod d × ℤ_[p]) R) (x : zmod (d * p^m)) (hd : d.gcd p = 1)
  (h : classical.some (factor_F p d R hd f) ≤ m)
  (y : zmod (d * p^m.succ))
  (hy : y ∈ ((λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (nat.le_succ m)) a)) x)) :
  f y = f x :=
begin
  -- note that y ≠ ↑x !
  simp at hy, rw mem_equi_class at hy, rw ←locally_constant.factors,
  repeat { rw function.comp_apply, }, apply _root_.congr_arg,
  have h' := classical.some_spec (factor_F p d R hd f),
  have h'' := le_F_of_ge p d _ _ h,
  have h3 := le_trans h'' h',
--  have h4 := h3 x y,
  rw ←discrete_quotient.of_le_proj h3,
  repeat { rw function.comp_apply, }, refine congr_arg _ _,
  suffices : ↑y ∈ ((F p d m).proj)⁻¹' {(F p d m).proj x},
  { rw set.mem_preimage at this, rw set.mem_singleton_iff at this, exact this, },
  rw discrete_quotient.fiber_eq, simp only [set.mem_set_of_eq],
  rw F_rel, simp only [prod.fst_zmod_cast, prod.snd_zmod_cast],
  rw ←hy,
  have val_le_val : (y.val : zmod (d * p^m)).val ≤ y.val,
  { apply val_le_val, apply le_of_lt, exact mul_pow_lt_mul_pow_succ p d m, },
  have : (d * p^m) ∣ y.val - (y.val : zmod (d * p^m)).val,
  { rw ←zmod.nat_coe_zmod_eq_zero_iff_dvd, rw nat.cast_sub val_le_val,
    { simp only [zmod.cast_id', id.def, sub_self, zmod.nat_cast_val], }, },
  split,
  { rw ←sub_eq_zero, rw ←ring_hom.map_sub, rw ←ring_hom.mem_ker, rw ker_to_zmod_pow,
    rw ideal.mem_span_singleton, repeat { rw ←zmod.nat_cast_val, }, rw ←dvd_neg, rw neg_sub,
    rw ←nat.cast_pow, rw ←nat.cast_sub val_le_val,
    { apply nat.coe_nat_dvd,
      apply dvd_trans (dvd_mul_left _ _) this, }, },
  { repeat { rw ←zmod.nat_cast_val, }, rw zmod.nat_coe_eq_nat_coe_iff,
    rw nat.modeq_iff_dvd' val_le_val, apply dvd_trans (dvd_mul_right _ _) this, },
end
-- This lemma has a lot of mini lemmas that can be generalized.

lemma fract_eq_self {a : ℚ} (h : 0 ≤ a) (ha : a < 1) : int.fract a = a :=
begin
   rw int.fract_eq_iff,
   refine ⟨h, ha, ⟨0, _⟩⟩, simp,
end

/-lemma coe_addd (m : ℕ) (b c : zmod (d * p^m.succ)) : (b + c : zmod (d * p^m)) = (b : zmod (d * p^m)) + (c : zmod (d * p^m)) :=
begin
  simp only [eq_self_iff_true],
end -/
-- (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_3))) m))
lemma maybe_generalize (m : ℕ) : (coe : zmod (p^(m.succ)) → zmod (p^m)) ∘ (coe : zmod (p^m) → zmod (p^(m.succ))) = id :=
begin
 ext x,
  simp only [id.def, function.comp_app],
  have : p^m ∣ (p^(m+1)),
  { apply pow_dvd_pow, simp, },
  rw ← @zmod.nat_cast_val (p^m) _ _ (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_5))) m)) x,
  conv_rhs {
    rw ← zmod.cast_id (p^m) x,
    rw ← @zmod.nat_cast_val (p^m) _ _ (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_5))) m)) x, },
  exact zmod.cast_nat_cast this x.val,
end

lemma val_coe_eq_val (n m : ℕ) (b : zmod n) [h1 : fact (0 < n)] [h2 : fact (n < m)] :
  (b.val : zmod m).val = b.val :=
begin
  have : b.val = (b : zmod m).val,
  { have h1 := zmod.val_lt b,
    have h2 : b.val < m, { transitivity n, assumption, apply fact.out, },
    have := zmod.val_cast_of_lt h2, rw ←this, refine congr_arg _ _, simp, },
  conv_rhs { rw this, },
  refine congr_arg _ _, rw @zmod.nat_cast_val _ _ _ _ _, assumption,
end

example (a b c d : ℕ) (h : a ≤ b) : a < b.succ :=
begin
  exact nat.lt_succ_iff.mpr h,
end

lemma sum_lt (m : ℕ) (a : zmod (d * p^m)) (x : fin p) : a.val + ↑x * (d * p ^ m) < d * p ^ m.succ :=
begin
  have h1 := zmod.val_lt a,
  have h2 : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1),
  { rw mul_comm, apply nat.mul_le_mul_left, rw [←nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel], apply x.2,
    { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, },
  have := add_lt_add_of_lt_of_le h1 h2,
  convert this,
  ring_nf, rw nat.sub_add_cancel,
  { rw ←pow_succ, },
  { apply le_of_lt, apply fact_iff.1 (nat.prime.one_lt' p), },
end

lemma sum_equiv {α β γ : Type*} {s : finset α} {s' : finset β} {φ : s ≃ s'} {f : α → γ}
  [add_comm_monoid γ] : ∑ x : s, f x = ∑ y : s', f(φ.inv_fun y) :=
begin
  apply finset.sum_bij',
  swap 4, rintros, exact φ.to_fun a,
  swap 5, rintros, exact φ.inv_fun a,
  all_goals {simp},
end

lemma why_no_find (a b : ℤ) : a = b ↔ a.succ = b.succ :=
begin
  split,
  exact congr_arg (λ (a : ℤ), a.succ),
  rintros, rw int.succ at *, rw int.succ at *, simp at *, assumption,
end

lemma this_must_exist (n : ℕ) [fact (0 < n)] (a : zmod n) : (a.val : ℤ) = (a : ℤ) :=
begin
  rw ←zmod.nat_cast_val a, congr, rw nat.cast_coe, rw coe_base,
  congr, ext, rw coe_b,
  induction x,
  { norm_num, change int.of_nat 0 = _, change int.of_nat 0 = (0 : ℤ), simp, },
  { norm_num, change int.of_nat x_n.succ = _, change (int.of_nat x_n).succ = _,
    rw why_no_find at x_ih, convert x_ih, },
end

lemma zmod_int_add (n : ℕ) [fact (0 < n)] (a b : zmod n) : (((a + b) : zmod n) : ℤ) = (a + (b : ℤ)) % n :=
begin
  rw [←this_must_exist, zmod.val_add],
  simp only [int.coe_nat_add, int.coe_nat_mod],
  apply _root_.congr_fun,
  refine congr_arg _ _,
  rw [←this_must_exist, ←this_must_exist],
end

example (n : ℕ) (h : 0 < n) : n ≠ 0 := ne_of_gt h

lemma zero_le_and_lt_one (n : ℕ) (x : zmod (d * p^n)) :
  0 ≤ (x.val : ℚ) / (d * p^n) ∧ (x.val : ℚ) / (d * p^n) < 1 :=
begin
  split,
  { norm_cast, refine div_nonneg _ _,
    all_goals { norm_cast, apply nat.zero_le _, }, },
  { rw div_lt_one,
    { norm_cast, apply @zmod.val_lt _ _, apply imp p d n, },
    { norm_cast,apply fact_iff.1 (imp p d n), }, },
end

lemma sum_rat_fin (n : ℕ) : (((∑ (x : fin n), (x : ℤ)) : ℤ) : ℚ) = (n - 1) * (n : ℚ) / 2 :=
begin
  have : ∀ (x : fin n), (x : ℤ)= ((x : ℕ) : ℤ), { simp, },
  conv_lhs { congr, congr, skip, funext, rw this x, },
  rw ←finset.sum_range,
  induction n with d hd, { simp, },
  { rw finset.sum_range_succ, rw int.cast_add, rw hd _,
    { simp, rw div_add',
      { rw mul_comm _ (d : ℚ), rw ←mul_add, ring, },
      { simp, }, },
    { simp, }, },
end

lemma coe_add_eq_ite' {n : ℕ} [fact (0 < n)] (a b : zmod n) (h : (a + b : ℤ) < n) :
  (((a + b) : zmod n) : ℤ) = (a : ℤ) + (b : ℤ) :=
begin
  rw zmod.coe_add_eq_ite,
  rw if_neg, push_neg, assumption,
end

lemma coe_nat_int (n a : ℕ) (h : a < n) : ((a : zmod n) : ℤ) = (a : ℤ) :=
begin
  by_cases h' : 0 < n,
  { rw ←zmod.nat_cast_val _,
    { apply congr, { ext y, simp, },
      rw zmod.val_cast_of_lt, assumption, },
    apply fact_iff.2, assumption, },
  simp only [not_lt, _root_.le_zero_iff] at h',
  rw h', simp only [zmod.cast_id', id.def, int.nat_cast_eq_coe_nat],
end

lemma lt_mul_pow (m a b : ℕ) (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 < m) : a < b * a^m :=
begin
  have : a ≤ b * a, apply (le_mul_iff_one_le_left _).2,
  { assumption, },
  { apply lt_trans _ h2, linarith, },
  apply lt_of_le_of_lt this _,
  apply mul_lt_mul',
  any_goals { linarith, },
  conv { congr, rw ←pow_one a, skip, skip, },
  apply pow_lt_pow,
  any_goals { assumption, },
end

example (m n : ℕ) (h : (m : ℤ) < n) : m < n := int.coe_nat_lt.mp h

lemma fin_le_val (m n : ℕ) (y : fin m) (h : m ≤ n) : (y : zmod n).val = y :=
begin
  dsimp,
  rw zmod.val_cast_of_lt _,
  refine lt_of_lt_of_le _ h,
  exact fin.is_lt y,
end
--example (m n : ℕ) (h : m < n) : (m : zmod n).val = m := zmod.val_cast_of_lt h

--example : ¬ (1 = 2 ∧ 3 < 4) := by push_neg

lemma pow_lt_mul_pow (m : ℕ) : p ^ m < d * p ^ m.succ :=
begin
  rw pow_succ, rw ←mul_assoc, apply lt_mul_of_one_lt_left,
  { apply pow_pos, apply nat.prime.pos, apply fact.out, },
  { apply one_lt_mul,
    { apply (nat.succ_le_iff).2, apply fact.out, },
    { apply nat.prime.one_lt, apply fact.out, }, },
end

lemma nat_cast_eq_coe_b (x : ℕ) : @nat.cast ℤ _ _ _ x = coe_b x :=
begin
  induction x with d hd,
  { change 0 = @has_coe.coe ℕ ℤ _ 0,
    change _ = int.of_nat 0, simp only [int.coe_nat_zero, int.of_nat_eq_coe], },
  { show d.cast + 1 = @has_coe.coe ℕ ℤ _ d.succ,
    change _ = int.of_nat d.succ, simp,
    change _ = int.of_nat d at hd, simp [hd], },
end

lemma fin_coe_coe (m : ℕ) (y : fin p) : (y : zmod (d * p^m.succ)) = ((y : ℕ) : zmod (d * p^m.succ)) :=
  coe_coe y

lemma fin_mul_lt (y : fin p) (m : ℕ) : (y : ℕ) * (d * p ^ m) < d * p ^ m.succ :=
begin
  rw pow_succ', rw ←mul_assoc d _ _, rw mul_comm (y : ℕ) _,
  apply mul_lt_mul', any_goals { linarith, },
  { exact fin.is_lt y, },
  { apply fact_iff.1, exact imp p d m, },
end

example (m : ℕ) : m^1 = m := pow_one m

lemma one_int_cast (n : ℕ) [fact (1 < n)] : ((1 : zmod n) : ℤ) = 1 :=
begin
  rw ←zmod.nat_cast_val _, rw zmod.val_one _,
  simp only [int.coe_nat_zero, int.coe_nat_succ, zero_add, int.nat_cast_eq_coe_nat],
  { assumption, },
  { apply fact_iff.2, apply lt_trans zero_lt_one,
    { apply fact.out, },
    { apply_instance, }, },
end

example {α β : Type*} {f : α → β} {a b : α} (h : a = b) : f a = f b :=by refine congr_arg f h

lemma sum_fract (m : ℕ) (x : zmod (d * p^m)) : ∑ (x_1 : (equi_class p d m m.succ (nat.le_succ m) x)),
  int.fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) =
    (x.val : ℚ) / (d * p^m) + (p - 1) / 2 :=
begin
  conv_lhs { congr, skip, funext, rw [fract_eq_self ((zero_le_and_lt_one p d m.succ x_1).1)
    ((zero_le_and_lt_one p d m.succ x_1).2)], },
  rw fintype.sum_equiv (equi_iso_fin p d m x) _ (λ k, (((equi_iso_fin p d m x).inv_fun k).val : ℚ) / (d * p ^ m.succ)),
  { rw ←finset.sum_div,
    have : ∀ k : fin p, ((equi_iso_fin p d m x).inv_fun k).val = x.val + ↑k * (d * p^m),
--  sorry, sorry, }, sorry end #exit -- 0.1 seconds!
    { intro k, unfold equi_iso_fin, dsimp, norm_cast, rw mul_assoc, },
--  sorry, }, sorry end #exit -- 0.15s
    conv_lhs { congr, congr, skip, funext, rw this x, rw ←zmod.int_cast_cast,
      skip, },
    --rw [coe_add_eq_ite'],
--  sorry, }, sorry end #exit -- 0.22 seconds
--    classical,
    --push_neg,
--  sorry, }, sorry end #exit -- 0.5 seconds
    convert_to (∑ x_1 : fin p, ((((x.val) : zmod (d * p^m.succ)) : ℤ) +
      (↑x_1 * ((d : zmod (d * p^m.succ)) * (p : zmod (d * p^m.succ)) ^ m) : ℤ) : ℚ)) / (d * p^m.succ : ℚ) = _,
--  sorry, sorry }, sorry, recover, sorry, end #exit -- 0.6 seconds
    { congr,
      funext y,
--sorry }, sorry }, sorry, end #exit -- 0.8 seconds
      rw ←int.cast_add, congr,
      --rw nat.cast_add,
--sorry }, sorry }, sorry, end #exit -- 1.6 seconds
      rw coe_add_eq_ite' _,
      { congr, rw ←zmod.nat_cast_val,
        rw zmod.val_mul, rw nat.mod_eq_of_lt _,
        { rw nat.cast_mul, apply congr_arg2,
          { rw fin_le_val, simp, rw mul_comm,
            apply le_mul_of_le_of_le_one,
            { conv { congr, rw ←pow_one p, skip, skip, },
              apply (nat.pow_le_iff_le_right _).2,
              { apply nat.succ_le_succ, linarith, },
              { apply nat.prime.two_le, apply fact.out, }, },
            apply (nat.succ_le_iff).2, apply fact.out, },
          { --rw nat.cast_mul,
            --rw ←zmod.nat_cast_val,
            rw zmod.val_mul, rw nat.mod_eq_of_lt _,
            { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.nat_cast_val,
              congr, rw ←nat.cast_pow,
              by_cases m = 0,
              { rw h, rw pow_zero, rw pow_zero, rw nat.cast_one, apply one_int_cast _,
                apply fact_iff.2, apply one_lt_mul,
                { rw nat.succ_le_iff, apply fact.out, },
                { rw pow_one p, apply nat.prime.one_lt, apply fact.out, }, },
              { rw coe_nat_int, rw coe_nat_int, simp,
                { refine lt_mul_pow (m.succ) p d _ _ _,
                  apply fact.out,
                  apply nat.prime.one_lt, apply fact.out,
                  apply nat.succ_lt_succ, apply nat.pos_of_ne_zero, assumption, },
                apply pow_lt_mul_pow, }, },
            { rw ←nat.cast_pow, rw zmod.val_cast_of_lt _, rw zmod.val_cast_of_lt _,
              { apply mul_pow_lt_mul_pow_succ, },
              { apply pow_lt_mul_pow, },
              { apply lt_mul_of_one_lt_right,
                { apply fact.out, },
                { apply nat.one_lt_pow,
                  { apply nat.succ_pos, },
                  { apply nat.prime.one_lt, apply fact.out, }, }, }, }, }, },
        { rw ←nat.cast_pow, rw ←nat.cast_mul, rw zmod.val_cast_of_lt _, rw fin_le_val _ _ _ _,
          { apply fin_mul_lt, },
          { rw mul_comm,
            apply le_mul_of_le_of_one_le,
            { conv { congr, rw ←pow_one p, skip, skip, },
              apply pow_le_pow,
              { apply le_of_lt, apply nat.prime.one_lt, apply fact.out, },
              { apply nat.succ_le_succ, apply nat.zero_le _, }, },
            { rw nat.succ_le_iff, apply fact.out, }, },
          { apply mul_pow_lt_mul_pow_succ, }, }, },
      { rw zmod.nat_cast_val, rw ←zmod.nat_cast_val, rw ←zmod.nat_cast_val (↑y * (_ * _)),
        rw ←nat.cast_add,
        { have := sum_lt p d m x y,
          have f := (int.coe_nat_lt).2 this,
          convert f using 1,
          apply congr,
          { ext y, simp, },
          { apply congr_arg2,
            { rw ←zmod.nat_cast_val, rw val_coe_eq_val _ _ _,
              { apply imp p d m, },
              { apply fact_iff.2, apply mul_pow_lt_mul_pow_succ, }, },
            { rw ←nat.cast_pow, rw ←nat.cast_mul, rw fin_coe_coe, rw ←nat.cast_mul,
              rw zmod.val_cast_of_lt,
              apply fin_mul_lt, }, }, }, --convert sum_lt p d m x y using 1, },
        { apply imp p d m.succ, }, },
      { apply imp p d m.succ, }, },
--    sorry, }, sorry, end #exit -- 2.7 seconds
    { rw finset.sum_add_distrib, rw finset.sum_const, rw finset.card_univ, rw fintype.card_fin _,
      norm_cast, rw ←finset.sum_mul, rw _root_.add_div, apply congr_arg2,
      { rw div_eq_iff _,
        { rw div_mul_comm,
          --rw div_mul_comm',
          rw _root_.nsmul_eq_mul, apply congr_arg2,
          { norm_num, rw mul_div_mul_left _, rw pow_succ, rw mul_div_cancel _,
            { norm_cast, apply pow_ne_zero m (nat.prime.ne_zero (fact_iff.1 _)), assumption, },
            { norm_num, apply ne_of_gt, apply fact_iff.1, assumption, }, },
          { rw zmod.int_cast_cast,
            rw zmod.nat_cast_val, rw ←zmod.nat_cast_val (x : zmod (d * p^m.succ)),
            refine congr_arg _ _, rw ←zmod.nat_cast_val x, rw val_coe_eq_val _ _ _,
            { apply imp p d m, },
            { rw mul_comm d (p^m), rw mul_comm d (p^m.succ), apply fact_iff.2, apply mul_lt_mul,
--sorry, sorry, sorry, sorry }, }, }, sorry, }, sorry, }, }, sorry, end #exit -- 4.72
              any_goals { simp, },
--sorry, sorry }, }, }, sorry, }, sorry, }, }, sorry, end #exit -- 5.3s
              { apply pow_lt_pow _ (nat.lt_succ_self m), apply nat.prime.one_lt, apply fact_iff.1,
                assumption, },
              { apply fact_iff.1, assumption, }, }, }, },
        { norm_cast, apply ne_of_gt, apply fact_iff.1, apply imp p d m.succ, }, },
--      sorry, }, }, sorry, end #exit -- 4.94 seconds
      { rw int.cast_mul, rw mul_div_assoc,
        --have : (((∑ (x : fin p), (x : ℤ)) : ℤ) : ℚ) = (p - 1) * (p : ℚ) / 2, sorry,
        rw sum_rat_fin, rw nat.cast_mul, rw int.cast_mul,
        have one : ((p : ℚ) - 1) * (p : ℚ) / 2 * (1 / (p : ℚ)) = ((p : ℚ) - 1) / 2,
        { rw _root_.div_mul_div_comm,
          --rw _root_.div_mul_div,
          rw mul_one, rw mul_div_mul_right,
          norm_cast, apply ne_of_gt, apply nat.prime.pos, apply fact_iff.1, assumption, },
        convert one using 2, rw div_eq_div_iff _ _,
--        sorry, sorry, sorry, }, }, }, sorry, end #exit -- 5.14 seconds
        { rw one_mul, rw zmod.int_cast_cast, rw int.cast_pow, rw zmod.int_cast_cast,
          rw pow_succ', rw nat.cast_mul, rw nat.cast_pow, rw mul_assoc, apply congr_arg2,
          { rw ←zmod.nat_cast_val _,
            { rw zmod.val_nat_cast, congr, apply nat.mod_eq_of_lt, rw lt_mul_iff_one_lt_right _,
              { rw ←pow_succ', apply _root_.one_lt_pow,
                { apply nat.prime.one_lt, apply fact_iff.1, assumption, },
                { simp, }, },
              { apply fact_iff.1, assumption, }, },
            { rw ←pow_succ', apply imp p d (m + 1), } },
          { apply congr_arg2,
            { by_cases m = 0,
              { rw h, rw pow_zero, rw pow_zero, },

              apply congr_arg2,
              { rw ←zmod.nat_cast_val _,
                { rw zmod.val_nat_cast, congr, apply nat.mod_eq_of_lt,
                  rw ←mul_assoc,
                  rw lt_mul_iff_one_lt_left _,
                  { apply one_lt_mul,
                    { rw nat.succ_le_iff, apply fact_iff.1, assumption, },
                    { apply _root_.one_lt_pow,
                      { apply nat.prime.one_lt, apply fact_iff.1, assumption, },
                      { apply h, }, }, },
                        --rw nat.succ_le_iff, apply nat.pos_of_ne_zero h, }, }, },
                  { apply nat.prime.pos, apply fact_iff.1, assumption, }, },
                { rw ←pow_succ', apply imp p d (m + 1), }, },
              { refl, }, },
            { refl, }, }, },
        { rw ←nat.cast_mul, norm_cast, apply ne_of_gt, apply fact_iff.1, apply imp p d _, },
        { norm_cast, apply ne_of_gt, apply nat.prime.pos, apply fact_iff.1, assumption, }, }, }, },
  { rintros y,
    simp only [equiv.symm_apply_apply, subtype.val_eq_coe, equiv.inv_fun_as_coe,
      zmod.nat_cast_val], },
end

lemma div_coe (m n : ℕ) (h : m ∣ n) (a : zmod m) : ((a : zmod n) : zmod m) = a :=
begin
  conv_rhs
  { rw ←zmod.ring_hom_map_cast (zmod.cast_hom h (zmod m)) a, },
  rw zmod.cast_hom_apply,
end

lemma fract_eq_val (n : ℕ) [h : fact (0 < n)] (a : zmod n) : int.fract ((a : ℚ) / n) = (a.val : ℚ) / n :=
begin
  rw int.fract_eq_iff, split,
  { apply div_nonneg _ _,
    { exact (zmod.val a).cast_nonneg, },
    { exact nat.cast_nonneg n, }, },
  split,
  { rw div_lt_one,
    { norm_cast, apply zmod.val_lt, },
    { norm_cast, apply fact_iff.1, assumption, }, },
  { rw ←zmod.nat_cast_val, use 0, simp, },
end

lemma card_equi_class (m : ℕ) (x : zmod (d * p^m)) :
  finset.card (@finset.univ (equi_class p d m m.succ (nat.le_succ m) x) _) = p :=
begin
  rw finset.card_univ,
  rw ←fintype.of_equiv_card (equi_iso_fin p d m x),
  convert fintype.card_fin p,
end

lemma is_unit_mul (hc : c.gcd p = 1) (hc' : c.gcd d = 1) :
  is_unit ((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))) :=
begin
  rw is_unit, refine ⟨(zmod.unit_of_coprime c _), _⟩,
  { apply nat.coprime.symm (nat.coprime.mul (nat.coprime.symm hc')
      (nat.coprime.pow_left m.succ (nat.coprime.symm hc))), },
  { rw zmod.coe_unit_of_coprime c _,
    rw zmod.cast_nat_cast _,
    swap, { refine zmod.char_p _, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, linarith, }, },
end

lemma is_unit_mul' (hc : c.gcd p = 1) (hc' : c.gcd d = 1) :
  is_unit ((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^m)) :=
begin
  rw is_unit, refine ⟨(zmod.unit_of_coprime c _), _⟩,
  { apply nat.coprime.symm (nat.coprime.mul (nat.coprime.symm hc')
      (nat.coprime.pow_left m (nat.coprime.symm hc))), },
  { rw zmod.coe_unit_of_coprime c _,
    rw zmod.cast_nat_cast _,
    swap, { refine zmod.char_p _, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, rw ←one_mul m,
      apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, }, },
end

--example (a b c : ℤ) (h : a = b) : c * a = c * b := congr_arg (has_mul.mul c) h

-- A lot of goals are recurring, maybe make them local instances / lemmas?
lemma coe_inv (m : ℕ) (hc : c.gcd p = 1) (hc' : c.gcd d = 1) :
  ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m))⁻¹ =
  ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m.succ)) : zmod (d * p^m)) :=
begin
  have : ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)) =
    (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)),
    { repeat { rw zmod.cast_nat_cast _, },
      any_goals { refine zmod.char_p _ },
      any_goals { apply mul_dvd_mul_left, },
      any_goals { apply pow_dvd_pow _, },
      { apply nat.le_succ, },
      { linarith, },
      { rw ←one_mul m, apply mul_le_mul, any_goals { linarith, },
        { rw one_mul, apply nat.le_succ, }, }, },
  convert_to (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))⁻¹ = _,
  { refine congr_arg _ _, assumption, },
  { have g1 : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))
      * (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))⁻¹ = 1,
    { rw zmod.mul_inv_of_unit, rw ←this, apply is_unit_mul' p d m hc hc', },
    have g2 : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))
      * ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m.succ)) : zmod (d * p^m)) = 1,
    { rw ←zmod.cast_mul _,
      { rw ←zmod.cast_one _,
        { congr, rw zmod.mul_inv_of_unit, apply is_unit_mul p d m hc hc', },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
    rw ←g1 at g2,
    have g3 := congr_arg (has_mul.mul
      ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m)))) g2,
    rw [←mul_assoc, ←mul_assoc, zmod.inv_mul_of_unit _, one_mul, one_mul] at g3,
    { rw g3, },
    { rw ←this, apply is_unit_mul' p d m hc hc', }, },
end

lemma rep (m : ℕ) : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)) =
  ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)) :=
begin
  repeat { rw zmod.cast_nat_cast _, },
  any_goals { refine zmod.char_p _, },
  any_goals { apply mul_dvd_mul_left, apply pow_dvd_pow, },
  { rw ←one_mul m, apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, },
  { apply nat.le_succ, },
  { linarith, },
end

/---is this true?
lemma E_c_sum_equi_class'' [has_coe ℝ R] (x : zmod d) (hc : c.gcd p = 1)
  (hc' : c.gcd d = 1) :
  ∑ (y : equi_class p d 0 1 (nat.le_succ 0) x), (E_c p d hc 1 y) = (E_c p d hc 0 x) :=
begin
  rw E_c, simp,
  sorry
end-/

lemma dvd_sub_comm (a b n : ℕ) (h : (n : ℤ) ∣ (a : ℤ) - (b : ℤ)) : (n : ℤ) ∣ (b : ℤ) - (a : ℤ) :=
begin
  refine (dvd_neg ↑n (↑b - ↑a)).mp _, simp [h],
end

lemma zmod.cast_inv (a m n : ℕ) (ha : a.coprime n) (h : m ∣ n) :
  (((a : zmod n)⁻¹ : zmod n) : zmod m) = ((a : zmod n) : zmod m)⁻¹ :=
begin
  set b : (zmod n)ˣ := zmod.unit_of_coprime a ha with hb,
  have : (b : zmod n) = a,
  { rw hb, simp, },
  rw ← this,
  change (((b⁻¹ : units (zmod n)) : zmod n) : zmod m) = _,
  have h1 : ∀ c : (zmod m)ˣ, (c : zmod m)⁻¹ = ((c⁻¹ : units (zmod m)) : zmod m),
  { intro c, simp, },
  rw ← zmod.cast_hom_apply _,
  swap 3, { apply zmod.char_p m, },
  swap, { apply h, },
  rw ← ring_hom.coe_monoid_hom,
  rw ← units.coe_map_inv _ b, rw ← h1,
  congr,
end

lemma fract_eq_of_zmod_eq (a b n : ℕ) [fact (0 < n)] (h : (a : zmod n) = (b : zmod n)) :
  int.fract (a / n : ℚ) = int.fract (b / n : ℚ) :=
begin
  rw [int.fract_eq_fract, div_sub_div_same],
  rw zmod.eq_iff_modeq_nat at h,
  rw nat.modeq_iff_dvd at h,
  have := dvd_sub_comm _ _ _ h,
  cases this with z hz,
  refine ⟨z, _⟩,
  have h : ∀ z : ℕ, (z : ℚ) = ((z : ℤ) : ℚ),
  { intro z, norm_cast, },
  rw h a, rw h b, rw ← int.cast_sub, rw hz, rw int.cast_mul,
  rw ← h n, rw mul_comm, rw mul_div_cancel,
  norm_cast, apply ne_of_gt, apply fact.out,
end

open nat

lemma dvd_val_sub_cast_val (m n : ℕ) [fact (0 < m)] [fact (0 < n)] (a : zmod m) :
  n ∣ a.val - (a : zmod n).val :=
by { --split,
  have : (a.val : zmod n) = ((a : zmod n).val : zmod n),
  { rw [nat_cast_val, nat_cast_val], norm_cast, },
  rw zmod.eq_iff_modeq_nat at this, delta modeq at this,
  have f := sub_mod_eq_zero_of_mod_eq this, rw ← dvd_iff_mod_eq_zero at f, exact f, }
