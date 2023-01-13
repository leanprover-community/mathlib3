/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_measure.bernoulli_measure_three

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
 * `coprime_pow_spl` replaced with `coprime.pow_right`
 * `val_le_val'` replaced with `val_coe_val_le_val'`
 * `imp` replaced with `apply_instance`
 * `factor_F` replaced with `discrete_quotient_of_to_zmod_pow.le`
 * `succ_eq_bUnion_equi_class` replaced with `zmod'_succ_eq_bUnion_equi_class`
 * `g` replaced with `eventually_constant_seq.from_loc_const`
 * `mem_nonempty` replaced with `nonempty.intro`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {p : ℕ} [fact p.prime] {d : ℕ}
variables (R : Type*) [normed_comm_ring R] {c : ℕ} {m : ℕ} [fact (0 < d)]

open_locale big_operators
open padic_int zmod nat

namespace nat
lemma coprime.mul_pow {a b c : ℕ} (n : ℕ) (hc' : c.coprime a) (hc : c.coprime b) :
  c.coprime (a * b^n) := coprime_mul_iff_right.2 ⟨hc', coprime.pow_right n hc⟩

end nat

lemma helper_E_c_sum_equi_class' (hc' : c.coprime d) (hc : c.coprime p) (x : zmod (d * p^m)) :
  ∑ (x_1 : (equi_class m.succ x)), int.fract (((c : zmod (d * p^(2 * m.succ)))⁻¹.val : ℚ) *
  ↑(x_1 : zmod (d * p^m.succ)) / (↑d * ↑p ^ m.succ)) =
  ∑ (x_1 : (equi_class m.succ (↑((c : zmod (d * p^(2 * m.succ)))⁻¹.val) * x))),
  int.fract (↑((x_1 : zmod (d * p^m.succ)).val) / (↑d * ↑p ^ m.succ)) :=
begin
  have h1 : d * p ^ m ∣ d * p ^ m.succ,
  { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, },
  have h2 : ∀ z : ℕ, d * p ^ z ∣ d * p ^ (2 * z),
  { intro z, apply mul_dvd_mul_left _ (pow_dvd_pow p _), linarith, },
  have h3 : d * p ^ m ∣ d * p ^ (2 * m.succ),
  { apply mul_dvd_mul_left _ (pow_dvd_pow p _),
    rw [nat.succ_eq_add_one, mul_add], linarith, },
  have h4 : (((c : zmod (d * p^(2 * m.succ)))⁻¹  : zmod (d * p^(2 * m.succ))) :
    zmod (d * p^m.succ)).val ≤ (c : zmod (d * p^(2 * m.succ)))⁻¹.val := val_coe_val_le_val' _,
  apply finset.sum_bij (λ a ha, _) (λ a ha, finset.mem_univ _) (λ a ha, _) (λ a1 a2 ha1 ha2 h, _) _,
  { refine ⟨(((c : zmod (d * p^(2*m.succ)))⁻¹).val : zmod (d * p^m.succ)) * a,
      (mem_equi_class _ _).2 _⟩,
    rw [zmod.cast_mul h1, cast_nat_cast h1 _],
    conv_rhs { congr, skip, rw ←((@mem_equi_class p _ d _ m.succ x a).1 a.prop), },
    any_goals { refine zmod.char_p _, }, },
  { rw [int.fract_eq_fract, subtype.coe_mk, div_sub_div_same, ← nat_cast_val
      (a : zmod (d * p^m.succ)), zmod.val_mul, ← nat.cast_mul, ← nat.cast_sub
      (le_trans (mod_le _ _) _), nat_cast_val, nat.cast_sub (le_trans (mod_le _ _) _),
      ← sub_add_sub_cancel _ ((((c : zmod (d * p^(2 * m.succ)))⁻¹ : zmod (d * p^(2 * m.succ))) :
      zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val : ℚ) _, ← nat.cast_mul],
    obtain ⟨z₁, hz₁⟩ := @dvd_sub_mod (d * p^m.succ) ((((c : zmod (d * p^(2 * m.succ)))⁻¹ :
      zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val),
    obtain ⟨z₂, hz₂⟩ := dvd_val_sub_cast_val (d * p^m.succ) (c : zmod (d * p^(2 * m.succ)))⁻¹,
    rw [← nat.cast_sub (mod_le _ _), hz₁, ← nat.cast_sub, ← nat.mul_sub_right_distrib, hz₂,
      mul_assoc (d * p^(m.succ)) _ _, nat.cast_mul, nat.cast_mul _ z₁, ← mul_add,
      ← nat.cast_pow, ← nat.cast_mul d _, mul_comm,
      mul_div_cancel _ ((@cast_ne_zero ℚ _ _ _ _).2 (ne_of_gt (fact_iff.1 _)))],
    refine ⟨((z₂ * (a : zmod (d * p ^ m.succ)).val + z₁ : ℕ) : ℤ), by { norm_cast } ⟩,
    any_goals { refine mul_le_mul_right' h4 _, },
    { apply_instance, },
    { rw nat_cast_val, refine mul_le_mul_right' h4 _, }, },
  { simp only [subtype.mk_eq_mk, nat_cast_val] at h,
    rw subtype.ext ((is_unit.mul_right_inj (is_unit_iff_exists_inv'.2
      ⟨((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))), _⟩)).1 h),
    rw [cast_inv (nat.coprime.mul_pow _ hc' hc) (h2 _), cast_nat_cast (h2 m.succ)],
    apply zmod.mul_inv_of_unit _ (is_unit_mul m.succ hc' hc),
    { refine zmod.char_p _, }, },
  { simp only [cast_nat_cast, nat_cast_val, subtype.coe_mk, finset.mem_univ, exists_true_left,
      set_coe.exists, forall_true_left, set_coe.forall, subtype.mk_eq_mk, exists_prop],
    rintros a ha, rw mem_equi_class at ha,
    refine ⟨((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) * a, _, _⟩,
    { rw [mem_equi_class, zmod.cast_mul h1],
      { rw [ha, ←mul_assoc, cast_inv (nat.coprime.mul_pow _ hc' hc) h3,
          cast_nat_cast (h2 m.succ) _, cast_nat_cast h1 _, cast_nat_cast h3 _,
          zmod.mul_inv_of_unit _ (is_unit_mul m hc' hc), one_mul],
        any_goals { refine zmod.char_p _ }, },
      { refine zmod.char_p _, }, },
    { rw [←mul_assoc, zmod.cast_inv (nat.coprime.mul_pow _ hc' hc) (h2 _),
        zmod.inv_mul_of_unit _ _, one_mul a, true_and],
      rw cast_nat_cast (h2 m.succ) c,
      apply is_unit_mul _ hc' hc,
      { refine zmod.char_p _, }, }, },
end

lemma E_c_sum_equi_class' (x : zmod (d * p^m)) (hc : c.coprime p) (hc' : c.coprime d) :
  ∑ (y : equi_class m.succ x), (E_c p d c m.succ y) = (E_c p d c m x) :=
begin
  rw [E_c, ← ring_hom.map_sum],
  apply congr_arg,
  rw [finset.sum_add_distrib, finset.sum_sub_distrib, sum_fract, ←finset.mul_sum],
  have h2 : ∀ z : ℕ, d * p ^ z ∣ d * p ^ (2 * z),
  { intro z, apply mul_dvd_mul_left _ (pow_dvd_pow p _), linarith, },
  have h3 : d * p ^ m ∣ d * p ^ (2 * m.succ),
  { apply mul_dvd_mul_left _ (pow_dvd_pow p _),
    rw [nat.succ_eq_add_one, mul_add], linarith, },
  convert_to ((x.val : ℚ) / (d * p ^ m) + (p - 1) / 2) - (c : ℚ) *
    ∑ (x_1 : (equi_class m.succ ( ((c : zmod (d * p^(2*m.succ)))⁻¹.val) * x))),
    int.fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) +
    (∑ (x : (equi_class m.succ x)), ((c : ℚ) - 1) / 2) = _ - _ + _,
  { rw [add_right_cancel_iff, sub_right_inj],
    refine congr_arg _ (helper_E_c_sum_equi_class' hc' hc _), },
  rw [sum_fract, ←nat.cast_pow, ←nat.cast_mul, int.fract_eq_self' (zero_le_div_and_div_lt_one x).1
    (zero_le_div_and_div_lt_one x).2, mul_add, finset.sum_const, card_equi_class,
    _root_.nsmul_eq_mul, sub_add_eq_add_sub, sub_add_eq_add_sub, sub_add_eq_sub_sub, sub_right_comm],
  apply congr_arg2 _ _ (congr_arg _ _),
  { rw [add_assoc, add_sub_assoc], congr, linarith, },
  { rw [←fract_eq_val _, ← zmod.nat_cast_val, ← zmod.nat_cast_val, ← nat.cast_mul],
    apply fract_eq_of_zmod_eq,
    rw [nat.cast_mul, zmod.nat_cast_val, zmod.nat_cast_val, zmod.nat_cast_val, zmod.cast_mul',
      zmod.nat_cast_val, zmod.cast_id],
    apply congr_arg2 _ _ rfl,
    rw [cast_inv (nat.coprime.mul_pow _ hc' hc) h3, cast_inv (nat.coprime.mul_pow _ hc' hc) (h2 _),
      cast_nat_cast h3, cast_nat_cast (h2 _)],
    any_goals { refine zmod.char_p _, },
    { apply_instance, }, },
end

variable [algebra ℚ_[p] R]

lemma E_c_sum_equi_class (x : zmod (d * p^m)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1) :
  ∑ (y : zmod (d * p ^ m.succ)) in (λ a : zmod (d * p ^ m), ((equi_class m.succ) a).to_finset) x,
  ((algebra_map ℚ_[p] R) (E_c p d c m.succ y)) = (algebra_map ℚ_[p] R) (E_c p d c m x) :=
begin
  rw ←E_c_sum_equi_class',
  { rw ring_hom.map_sum,
    apply finset.sum_bij (λ a ha, subtype.mk a _) (λ a ha, finset.mem_univ _) (λ a ha, _)
      (λ a b ha hb h, _) (λ b hb, _),
    { refine set.mem_to_finset.1 ha, },
    { simp only [subtype.coe_mk], },
    { simp only [subtype.mk_eq_mk, subtype.ext_iff, subtype.coe_mk] at h, rw h, },
    { simp only [set.mem_to_finset],
      refine ⟨b.val, b.prop, by { rw subtype.ext_iff_val, }⟩, }, },
  any_goals { assumption, },
end

namespace set
lemma inter_nonempty_of_not_disjoint {α : Type*} {s t : set α} (h : ¬disjoint s t) :
  ∃ x, x ∈ s ∧ x ∈ t :=
begin
  contrapose h, push_neg at h,
  rw [not_not, disjoint_iff],
  ext,
  refine ⟨λ h', (h x ((set.mem_inter_iff _ _ _).1 h').1) ((set.mem_inter_iff _ _ _).1 h').2, _⟩,
  simp,
end

end set

namespace finset
lemma inter_nonempty_of_not_disjoint {α : Type*} {s t : finset α} [decidable_eq α]
  (h : ¬disjoint s t) : ∃ x, x ∈ s ∧ x ∈ t :=
begin
  obtain ⟨x, hx⟩ : finset.nonempty (s ⊓ t),
  { rw [finset.inf_eq_inter, finset.nonempty_iff_ne_empty],
    contrapose h, push_neg at h,
    rw [not_not, disjoint],
    simp only [inf_eq_inter, bot_eq_empty, le_eq_subset], -- simp does not work without rw disjoint
    rw [finset.subset_empty, h], },
  refine ⟨x, finset.mem_inter.1 hx⟩,
end

end finset

open discrete_quotient_of_to_zmod_pow

namespace eventually_constant_seq
/-- An eventually constant sequence constructed from a locally constant function. -/
noncomputable abbreviation from_loc_const (hc : c.coprime p) (hc' : c.coprime d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (hd' : d.coprime p) : @eventually_constant_seq R :=
{ to_seq := λ (n : ℕ), ∑ a in (zmod' (d * p^n) (mul_prime_pow_pos n)),
    f(a) • ((algebra_map ℚ_[p] R) (E_c p d c n a)),
  is_eventually_const := ⟨classical.some (le hd' f) + 1,
  λ l hl', begin
  simp only [algebra.id.smul_eq_mul, set.mem_set_of_eq], -- why is the simp needed?
  have hl : classical.some (le hd' f) ≤ l := le_trans (nat.le_succ _) hl',
  set t := λ a : zmod (d * p ^ l), set.to_finset ((equi_class l.succ) a) with ht,
  have disj : set.pairwise_disjoint ↑(zmod' (d * p ^ l) _) t,
  { rintros x hx y hy hxy,
    contrapose hxy, push_neg,
    obtain ⟨z, hz⟩ := finset.inter_nonempty_of_not_disjoint hxy,
    rw ht at hz,
    simp only [set.mem_to_finset] at hz,
    rw [mem_equi_class, mem_equi_class] at hz,
    exact hz.1 ▸ hz.2, },
  rw [zmod'_succ_eq_bUnion_equi_class, finset.sum_bUnion disj],
  { haveI : fact (0 < l) := fact_iff.2 (lt_of_lt_of_le (nat.zero_lt_succ _) hl'),
    conv_lhs { apply_congr, skip, conv { apply_congr, skip, rw equi_class_eq R hd' hl x x_1 H_1, },
    rw [←finset.mul_sum, E_c_sum_equi_class R x hc hc'], }, }, end⟩, }

open eventually_constant_seq

lemma from_loc_const_def (hc : c.coprime p) (hc' : c.coprime d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (n : ℕ) (hd' : d.coprime p) :
  (from_loc_const R hc hc' f hd').to_seq n =
    ∑ a in (finset.range (d * p^n)),f(a) • ((algebra_map ℚ_[p] R) (E_c p d c n a)) :=
begin
  apply finset.sum_bij (λ a ha, _) (λ a ha, _) (λ a ha, _) (λ a b ha hb h, zmod.val_injective _ h)
    (λ b hb, ⟨(b : zmod (d * p^n)), finset.mem_univ _,
    (zmod.val_cast_of_lt (finset.mem_range.1 hb)).symm⟩),
  { simp only [finset.mem_range, val_lt _], },
  { simp only [nat_cast_val, zmod.cast_id], },
end

end eventually_constant_seq
open clopen_from

-- does not require [fact (0 < d)]
lemma equi_class_clopen {n : ℕ} (a : zmod (d * p^n)) (hm : n ≤ m) (b : (equi_class m a)) :
  (b.val : zmod d × ℤ_[p]) ∈ (clopen_from a) :=
begin
  simp_rw [subtype.val_eq_coe, mem_clopen_from, ←(mem_equi_class _ _).1 b.prop],
  refine ⟨_, _⟩,
  { conv_rhs { congr, rw ←nat_cast_val, },
    rw [prod.fst_zmod_cast, cast_nat_cast (dvd_mul_right d _) _, nat_cast_val],
    refine zmod.char_p _, },
  { rw [prod.snd_zmod_cast],
    convert_to _ = ((b: zmod (d * p^m)) : zmod (p^n)),
    { rw ←zmod.int_cast_cast (b: zmod (d * p^m)),
      conv_rhs { rw ←zmod.int_cast_cast (b: zmod (d * p^m)), },
      change (ring_hom.comp (to_zmod_pow n) (int.cast_ring_hom ℤ_[p])) ((b : zmod (d * p^m)) : ℤ) =
        (int.cast_ring_hom (zmod (p^n))) ((b : zmod (d * p^m)) : ℤ),
      apply _root_.congr_fun _ _,
      congr,
      convert @ring_hom.ext_zmod 0 _ _ _ _, },
    { rw [←cast_hom_apply' (zmod (p^n)) (dvd_mul_left (p^n) d) _, ←cast_hom_apply' (zmod (d * p^n))
        (mul_dvd_mul_left d (pow_dvd_pow p hm)) _, ←cast_hom_apply' (zmod (p^n))
        (dvd_mul_of_dvd_right (pow_dvd_pow p hm) d) _, ←ring_hom.comp_apply],
        apply _root_.congr_fun _,
        congr,
        convert ring_hom.ext_zmod _ _, }, },
end

open eventually_constant_seq locally_constant

lemma from_loc_const_char_fn {n : ℕ} (a : zmod (d * p^n)) (hc : c.coprime p) (hc' : c.coprime d)
  (h' : d.coprime p) (hm : n ≤ m) :
  (from_loc_const R hc hc' (char_fn R (clopen_from.is_clopen a)) h').to_seq m =
  ∑ (y : equi_class m a), (algebra_map ℚ_[p] R) (E_c p d c m y) :=
begin
  rw [from_loc_const_def, char_fn],
  simp only [algebra.id.smul_eq_mul, boole_mul, locally_constant.coe_mk, finset.sum_ite, add_zero,
    finset.sum_const_zero],
  rw finset.sum_bij (λ b hb, _) (λ b hb, finset.mem_univ _) (λ b hb, _) (λ b c hb hc h, _)
    (λ b hb, _),
  { simp only [finset.mem_filter] at hb,
    rw [mem_clopen_from, prod.fst_nat_cast, prod.snd_nat_cast] at hb,
    refine ⟨b, (mem_equi_class _ _).2 ((function.injective.eq_iff (equiv.injective
      (zmod.chinese_remainder (coprime.pow_right n h')).to_equiv )).1 (prod.ext_iff.2 ⟨_, _⟩))⟩,
    { rw [inv_fst, inv_fst, cast_nat_cast (mul_dvd_mul_left d (pow_dvd_pow p hm)) _,
        cast_nat_cast (dvd_mul_right d _), hb.2.1],
      any_goals { refine zmod.char_p _, }, },
    { rw [inv_snd, inv_snd, cast_nat_cast (mul_dvd_mul_left d (pow_dvd_pow p hm)) _,
        cast_nat_cast (dvd_mul_left _ _), hb.2.2, map_nat_cast],
      any_goals { refine zmod.char_p _, },  }, },
  { simp only [subtype.coe_mk], },
  { simp only [finset.mem_filter, finset.mem_range] at hc,
    simp only [finset.mem_filter, finset.mem_range] at hb,
    rw [←zmod.val_cast_of_lt hb.1, ←zmod.val_cast_of_lt hc.1,
      (function.injective.eq_iff (zmod.val_injective _)).2 _],
    { apply_instance, },
    { exact subtype.ext_iff.1 h, }, },
  { simp only [finset.mem_filter, finset.mem_range, subtype.val_eq_coe],
    refine ⟨(b.val).val, _, _⟩,
    { simp only [finset.mem_filter, finset.mem_range, subtype.val_eq_coe, zmod.nat_cast_val],
      refine ⟨zmod.val_lt _, equi_class_clopen a hm _⟩, },
    { rw subtype.ext_iff_val,
      simp only [zmod.cast_id', id.def, zmod.nat_cast_val], }, },
end

open eventually_constant_seq

-- zmod.cast_cast'
lemma seq_lim_from_loc_const_char_fn {n : ℕ} (a : zmod (d * p^n)) (hc : c.coprime p)
  (hc' : c.coprime d) (h' : d.coprime p) :
  sequence_limit_index' (from_loc_const R hc hc' (char_fn R (clopen_from.is_clopen a)) h') ≤ n :=
begin
  refine nat.Inf_le (λ m hm, _),
  have hm' : d * p^n ∣ d * p^m := mul_dvd_mul_left d (pow_dvd_pow p hm),
  rw [from_loc_const_char_fn R a hc hc' h' hm,
    from_loc_const_char_fn R a hc hc' h' (le_trans hm (le_succ _))],
  conv_rhs { apply_congr, skip, rw ←E_c_sum_equi_class R _ hc hc', },
  rw ←finset.sum_bUnion,
  { refine finset.sum_bij (λ b hb, b.val) (λ b hb, finset.mem_bUnion.2 _) (λ b hb, rfl)
      (λ b b' hb hb' h, subtype.ext_iff_val.2 h) (λ b hb, _),
    { simp only [finset.mem_univ, set_coe.exists, finset.mem_bUnion, set.mem_to_finset,
        exists_true_left],
      refine ⟨b.val, (mem_equi_class _ _).2 _, (mem_equi_class _ _).2 rfl⟩,
      simp_rw [←(mem_equi_class _ _).1 b.prop, subtype.val_eq_coe],
      rw [←nat_cast_val (b : zmod (d * p ^ m.succ)), cast_nat_cast hm' _, nat_cast_val],
      refine zmod.char_p _, },
    { simp only [finset.mem_univ, set_coe.exists, finset.mem_bUnion, set.mem_to_finset,
        subtype.coe_mk, exists_true_left, exists_prop] at hb,
      simp only [exists_prop, finset.mem_univ, set_coe.exists, exists_eq_right',
        exists_true_left, subtype.coe_mk, subtype.val_eq_coe],
      rcases hb with ⟨z, h1, h3⟩,
      rw mem_equi_class at *,
      symmetry,
      rw [←h1, ←h3.2, ←nat_cast_val b, cast_nat_cast hm' _, nat_cast_val],
      refine zmod.char_p _, }, },
  { -- if I attach this to finset.sum_bUnion, I get an extra error of types and an extra goal of
    -- decidability
    refine (λ x hx y hy hxy, finset.disjoint_iff_ne.2 (λ z hz z' hz', λ h, hxy
      (subtype.ext_iff_val.2 (by { rw [subtype.val_eq_coe, subtype.val_eq_coe,
      ←((mem_equi_class _ _).1 (set.mem_to_finset_val.1 hz)), ←(((mem_equi_class _ _).1
      (set.mem_to_finset_val.1 hz'))), h], })))), },
end

/-- An `R`-linear map from `locally_constant (zmod d × ℤ_[p]) R` to `R` which is a Bernoulli
  measure. -/
noncomputable abbreviation loc_const_to_seq_limit (hc : c.coprime p) (hc' : c.coprime d)
  (h' : d.coprime p) : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R :=
{ to_fun := λ f, sequence_limit (from_loc_const R hc hc' f h'),
  map_add' := λ x y, begin
    repeat { rw sequence_limit_eq (from_loc_const R hc hc' _ h') ((sequence_limit_index'
      (from_loc_const R hc hc' (x + y) h')) ⊔ (sequence_limit_index' (from_loc_const R hc hc' x h'))
      ⊔ (sequence_limit_index' (from_loc_const R hc hc' y h'))) _, },
    { simp only [algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add,
        ←finset.sum_add_distrib],
      refine finset.sum_congr rfl (λ y hy, add_mul _ _ _), },
    { refine le_sup_iff.2 (or.inr le_rfl), },
    { refine le_sup_iff.2 (or.inl (le_sup_iff.2 (or.inr le_rfl))), },
    { refine le_sup_iff.2 (or.inl (le_sup_iff.2 (or.inl le_rfl))), }, end,
  map_smul' := λ m x, begin
    repeat { rw sequence_limit_eq (from_loc_const R hc hc' _ h') ((sequence_limit_index'
      (from_loc_const R hc hc' x h')) ⊔
      (sequence_limit_index' (from_loc_const R hc hc' (m • x) h'))) _, },
    { simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply, finset.mul_sum],
      refine finset.sum_congr rfl (λ y hy, by { rw [mul_assoc, ring_hom.id_apply], }), },
    { refine le_sup_iff.2 (or.inl le_rfl), },
    { refine le_sup_iff.2 (or.inr le_rfl), }, end }

lemma loc_const_to_seq_limit_mem_bernoulli_measure [nontrivial R] (hc : c.coprime p)
  (hc' : c.coprime d) (h' : d.coprime p) :
  loc_const_to_seq_limit R hc hc' h' ∈ (@bernoulli_measure p _ d R _ c _) :=
begin
  rw bernoulli_measure,
  simp only [algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add, linear_map.coe_mk,
    le_sup_iff, set.mem_set_of_eq],
  intros n a, -- refine is unable to unfold the next line but rw can
  rw [sequence_limit_eq (from_loc_const R hc hc' _ h') n
    (seq_lim_from_loc_const_char_fn R a hc hc' h'), from_loc_const_def R hc hc' _ n h',
    finset.sum_eq_add_sum_diff_singleton (finset.mem_range.2 (zmod.val_lt a.val)) _],
  swap, { apply_instance, },
  rw [nat_cast_val a, zmod.cast_id, nat_cast_val a, (char_fn_one R _ _).1 (self_mem_clopen_from a),
    one_smul, nat_cast_val a, zmod.cast_id, add_right_eq_self],
  refine finset.sum_eq_zero (λ x hx, _),
  rw (char_fn_zero R _ _).1 (λ h'', (finset.mem_sdiff.1 hx).2 _),
  { rw zero_smul, },
  { obtain ⟨h1, h2⟩ := (mem_clopen_from _ _).1 h'',
    suffices : (x : zmod (p^n)) = (a : zmod (p^n)),
    { rw [←nat_cast_val a, nat_coe_eq_nat_coe_iff] at this,
      rw [←nat_cast_val a, prod.fst_nat_cast, nat_coe_eq_nat_coe_iff] at h1,
      have h4 := congr_arg zmod.val ((zmod.nat_coe_eq_nat_coe_iff _ _ _).2
        ((nat.modeq_and_modeq_iff_modeq_mul (coprime.pow_right n h')).1 ⟨h1, this⟩)),
      rw [zmod.val_cast_of_lt (finset.mem_range.1 ((finset.mem_sdiff.1 hx).1)),
        zmod.val_cast_of_lt (zmod.val_lt a)] at h4,
      rw [h4, finset.mem_singleton], },
    { simp only [h2, map_nat_cast, prod.snd_nat_cast], }, },
end

lemma bernoulli_measure_nonempty [nontrivial R] (hc : c.coprime p) (hc' : c.coprime d)
  (h' : d.coprime p) : nonempty (@bernoulli_measure p _ d R _ c _) :=
nonempty.intro ⟨loc_const_to_seq_limit R hc hc' h',
  loc_const_to_seq_limit_mem_bernoulli_measure R hc hc' h'⟩
