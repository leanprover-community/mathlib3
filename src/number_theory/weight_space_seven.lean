/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space_six

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
variables [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R]

set_option old_structure_cmd true

open_locale big_operators

open padic_int zmod nat locally_constant

/-- Constructs a measure from the Bernoulli measure `E_c`. -/
noncomputable def bernoulli_measure_of_measure (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (h' : d.gcd p = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥ ) :
  measures (units (zmod d) × units ℤ_[p]) R :=
begin
  constructor, swap,
  { --constructor,
    constructor, swap 3,
    { rintros f,
      --choose g hg using subspace_induces_locally_constant R p d f, --cases does not work as no prop
  --exact (classical.choice (bernoulli_measure_nonempty p d R hc hc' h')).val g,
      exact (classical.some (@set.nonempty_of_nonempty_subtype _ _
        (bernoulli_measure_nonempty p d R hc hc' h'))) (loc_const_ind_fn _ p d f), },
    { have := classical.some_spec (@set.nonempty_of_nonempty_subtype _ _
        (bernoulli_measure_nonempty p d R hc hc' h')),
      rw set.mem_def at this,
      --simp at this,
      rintros f1 f2,
      convert linear_map.map_add _ _ _,
      ext y,
      repeat { rw loc_const_ind_fn, },
      simp only [pi.add_apply, locally_constant.coe_add, locally_constant.coe_mk],
      repeat {rw ind_fn, },
      simp only [pi.add_apply, locally_constant.coe_add],
      by_cases pos : is_unit y.fst ∧ is_unit y.snd,
      { convert dif_pos pos,
        any_goals { convert dif_pos pos, }, },
      { have : (0 : R) = 0 + 0, rw add_zero,
        convert this,
        any_goals { convert dif_neg pos, }, }, },
    { rintros m f,
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, locally_constant.to_fun_eq_coe],
      convert linear_map.map_smul _ _ _,
      ext y,
      repeat { rw loc_const_ind_fn, },
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply,
        locally_constant.coe_mk],
      repeat { rw ind_fn, },
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply],
      by_cases pos : is_unit y.fst ∧ is_unit y.snd,
      { convert dif_pos pos, convert dif_pos pos, },
      { convert (mul_zero m).symm,
        any_goals { convert dif_neg pos, }, }, }, },
  { simp only [linear_map.coe_mk, locally_constant.to_fun_eq_coe],
    set K := 1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ with hK,
    have Kpos : 0 < K,
    { rw hK, rw add_comm, apply add_pos_of_nonneg_of_pos,
      { apply norm_nonneg, },
      { apply zero_lt_one, }, },
    refine ⟨K, _, λ f, _⟩,
    { apply Kpos, },
    obtain ⟨n, hn⟩ := loc_const_eq_sum_char_fn p d R (loc_const_ind_fn R p d f) h',
    rw hn,
    rw linear_map.map_sum,
    convert le_trans (na (d * p^n) _) _,
    set a := ⨆ (i : zmod (d * p ^ n)),
      ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _
      (bernoulli_measure_nonempty p d R hc hc' h')))
      (((loc_const_ind_fn R p d f) ↑(i.val)) • char_fn R (is_clopen_clopen_from p d n (i.val)))∥ with ha,
    set s := {i : zmod (d * p^n) | ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _
      (bernoulli_measure_nonempty p d R hc hc' h')))
    ((loc_const_ind_fn R p d f) ↑(i.val) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a } with hs,
    have nons : set.nonempty s,
    { apply s_nonempty, rw ha, },
    set i := classical.some nons with hi,
    have hi' := classical.some_spec nons,
    rw set.mem_def at hi',
    change ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _
      (bernoulli_measure_nonempty p d R hc hc' h')))
      ((loc_const_ind_fn R p d f) ↑(i.val) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a at hi',
    by_cases is_unit (i : zmod d) ∧ is_unit (i : ℤ_[p]),
    { suffices : a ≤ K * ∥(loc_const_ind_fn R p d f) ↑i∥,
      convert_to a ≤ _,
      apply le_trans this _,
      rw mul_le_mul_left _,
      rw continuous_map.norm_eq_supr_norm,
      apply le_cSup,
      { apply set.finite.bdd_above,
        change (set.range (λ (x : units (zmod d) × units ℤ_[p]), ∥f x∥)).finite,
        refine is_locally_constant.range_finite _,
        change is_locally_constant (norm ∘ f),
        apply is_locally_constant.comp f.is_locally_constant _, },
      { refine ⟨(is_unit.unit h.1, is_unit.unit h.2), _⟩,
        change ∥f.to_fun _ ∥ = _,
        rw ind_fn_eq_fun,
        rw loc_const_ind_fn,
        simp only [function.comp_app, locally_constant.coe_mk, prod.map_mk],
        refine congr_arg _ _, refine congr_arg _ _,
        rw prod.ext_iff,
        simp only [prod.snd_nat_cast, prod.fst_nat_cast, prod.map_mk],
        repeat { rw is_unit.unit_spec, },
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, eq_self_iff_true, and_self], },
      { apply Kpos, },
      { rw ←hi',
        rw linear_map.map_smul,
        rw smul_eq_mul,
        apply le_trans (norm_mul_le _ _) _,
        rw mul_comm, apply mul_le_mul,
        { apply meas_E_c, },
        { simp only [zmod.nat_cast_val], },
        { apply norm_nonneg, },
        { apply le_of_lt, apply Kpos, }, }, },
    { have zer : (loc_const_ind_fn R p d f) ↑(i.val) = 0,
      { rw loc_const_ind_fn, simp only [locally_constant.coe_mk],
        rw ind_fn, convert dif_neg _, convert h,
        { simp only [prod.fst_zmod_cast, zmod.nat_cast_val], },
        { simp only [prod.snd_zmod_cast, zmod.nat_cast_val], }, },
      rw zer at hi', rw zero_smul at hi',
      simp only [linear_map.map_zero, norm_zero, finset.mem_range] at hi',
      rw hi'.symm at ha, rw ←ha,
      apply mul_nonneg,
      { apply le_of_lt, apply Kpos, },
      apply norm_nonneg, }, },
end
--is it ok to take R to be a semi_normed ring?
--function on clopen subsets of Z/dZ* x Z_p* or work in Z_p and restrict
--(i,a + p^nZ_p) (i,d) = 1

noncomputable def bernoulli_distribution (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) :
  linear_map (ring_hom.id R) (locally_constant ((zmod d) × ℤ_[p]) R) R :=
{ to_fun := λ f, sequence_limit (g p d R hc hc' (by {apply fact_iff.1, convert hd 0,
    rw [pow_zero, mul_one], }) f h'),
  map_add' := begin rintros,
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },

--      convert linear_map.map_add _ _ _,
--      ext y,
      /-repeat { rw loc_const_ind_fn, },

      --simp only [pi.add_apply, locally_constant.coe_add, locally_constant.coe_mk],
      repeat {rw ind_fn, },
      simp only [pi.add_apply, locally_constant.coe_add],
      by_cases pos : is_unit y.fst ∧ is_unit y.snd,
      { convert dif_pos pos,
        any_goals { convert dif_pos pos, }, },
      { have : (0 : R) = 0 + 0, rw add_zero,
        convert this,
        any_goals { convert dif_neg pos, }, },-/

    set n := (sequence_limit_index' (g p d R hc hc' hd' (x + y) h')) ⊔ (sequence_limit_index' (g p d R hc hc' hd' x h'))
      ⊔ (sequence_limit_index' (g p d R hc hc' hd' y h')) with hn,
    --rw sequence_limit_eq (g p d R hc (x + y)) n _,
    repeat { rw sequence_limit_eq (g p d R hc hc' hd' _ h') n _, },
    { rw g_def p d R hc hc' hd' _ n h', rw g_def p d R hc hc' hd' _ n h', rw g_def p d R hc hc' hd' _ n h',
      simp only [algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add],
      rw ←finset.sum_add_distrib,
      apply finset.sum_congr, refl,
      rintros, rw add_mul, },
    { rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, left, apply le_refl, }, end,
  map_smul' := begin
    rintros m x,
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
    set n := (sequence_limit_index' (g p d R hc hc' hd' x h')) ⊔ (sequence_limit_index' (g p d R hc hc' hd' (m • x) h'))
      with hn,
    repeat { rw sequence_limit_eq (g p d R hc hc' hd' _ h') n _, },
    { repeat { rw g_def p d R hc hc' hd' _ n h', }, simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply], rw finset.mul_sum,
      apply finset.sum_congr, refl,
      rintros, rw mul_assoc, rw ring_hom.id_apply, },
    { rw le_sup_iff, left, apply le_refl, },
    { rw le_sup_iff, right, apply le_refl, },
   end, }

lemma s_nonempty' (n : ℕ) (f : locally_constant ((zmod d) × ℤ_[p]) R) (a : ℝ)
  (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (h' : d.gcd p = 1)
  (ha : a = ⨆ (i : zmod (d * p ^ n)),
      ∥(bernoulli_distribution p d R hc hc' h') ((f (i.val)) • char_fn R
      (is_clopen_clopen_from p d n (i.val)))∥) :
  {i : zmod (d * p^n) | ∥(bernoulli_distribution p d R hc hc' h')
    ((f ↑(i.val)) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a }.nonempty :=
begin
  have := set.nonempty.cSup_mem,
  swap 4, { refine set.range (λ (i : zmod (d * p^n)),
    ∥((bernoulli_distribution p d R hc hc' h'))
    (f ↑i • char_fn R (is_clopen_clopen_from p d n i))∥), },
  swap, { apply_instance, },
  specialize this _ _,
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  { rw ←set.image_univ, apply set.finite.image, exact set.finite_univ, },
  { suffices : a ∈ set.range (λ (i : zmod (d * p^n)),
      ∥(bernoulli_distribution p d R hc hc' h')
      (f ↑i • char_fn R (is_clopen_clopen_from p d n i))∥),
    { cases this with y hy,
      simp only [algebra.id.smul_eq_mul, linear_map.map_smul] at hy,
      use y,
      simp only [zmod.cast_id', algebra.id.smul_eq_mul, id.def, set.mem_set_of_eq,
        finset.mem_range, linear_map.map_smul, zmod.nat_cast_val],
      refine hy, },
    { convert this using 1, rw ha,
      convert_to Sup (set.range (λ (i :zmod (d * p ^ n)),
        ∥(bernoulli_distribution p d R hc hc' h')
      ((f ↑(i.val)) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥)) = _,
      refine congr_arg _ _,
      simp only [zmod.cast_id', id.def, zmod.nat_cast_val], }, },
end

@[to_additive]
lemma prod_coe_to_finset {α : Type*} {β :Type*} [comm_monoid β] (s : set α) [fintype s] (f : α → β) :
  ∏ (i : α) in s.to_finset, f i = ∏ (i : s), f i :=
 by { apply finset.prod_bij,
  swap 5, { rintros t ht, simp [set.mem_to_finset] at ht, refine ⟨t, ht⟩, },
  { rintros a ha, simp only [finset.mem_univ], },
  { rintros a ha, simp only [subtype.coe_mk], },
  { rintros b c hb hc h, simp only [subtype.mk_eq_mk] at h, exact h, },
  { rintros b hb,
    refine ⟨b.val, set.mem_to_finset.2 b.prop, _⟩,
    simp only [subtype.coe_eta, subtype.val_eq_coe], }, }

lemma g_to_seq (n : ℕ) (a : zmod (d * p^n)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (h' : d.gcd p = 1) [hd : ∀ n : ℕ, fact (0 < d * p^n)] :
  (g p d R hc hc' (by {apply fact_iff.1, convert hd 0, rw pow_zero, rw mul_one, })
  (char_fn R (is_clopen_clopen_from p d n a)) h').to_seq n =
  (algebra_map ℚ R) (E_c p d hc n a) :=
begin
  rw g_char_fn p d R _ n a hc hc' h' _ (le_refl n),
  { --have : equi_class p d n n (le_refl n) a = {a}, sorry,
    --rw ←finset.sum_singleton,
    { --convert_to ∑ (y : @set.to_finset ({a} : set (zmod (d * p^n))) _), (algebra_map ℚ R) (E_c p d hc n ↑y) = _,
      convert_to ∑ (y : zmod (d * p^n)) in {a}, (algebra_map ℚ R) (E_c p d hc n ↑y) = _,
      { convert_to ∑ (y : zmod (d * p^n)) in (set.to_finset (equi_class p d n n (le_refl n) a)),
          (algebra_map ℚ R) (E_c p d hc n ↑y) = _,
        { rw sum_coe_to_finset,
          tidy, },
        { apply finset.sum_congr,
          { rw finset.ext_iff,
            rintros y, simp only [set.mem_to_finset, finset.mem_singleton],
            rw mem_equi_class, rw zmod.cast_id, },
          { rintros, refl, }, }, },
      { rw finset.sum_singleton, rw zmod.cast_id, }, }, },
end

lemma meas_E_c' {n : ℕ} {a : zmod (d * p^n)} (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (h' : d.gcd p = 1) : ∥ (bernoulli_distribution p d R hc hc' h')
  (char_fn R (is_clopen_clopen_from p d n a))∥ ≤
  1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ :=
begin
  /-have := (classical.some_spec (@set.nonempty_of_nonempty_subtype _ _
  (bernoulli_measure_nonempty p d R hc hc' h'))),
  rw set.mem_def at this,
  specialize this n a, -/
--  convert (algebra_map ℚ R) (E_c p d hc n a) ≤ _,
  --rw clopen_from,
--  rw this,

  convert_to ∥(algebra_map ℚ ℚ_[p]) (E_c p d hc n a)∥ ≤ _,
  { haveI : norm_one_class ℝ, exact cstar_ring.norm_one_class,
    --conv_rhs { rw ← mul_one (∥E_c p d hc n a∥), congr, skip, rw ← @norm_one_class.norm_one R _ _ _, },
    --rw ← norm_algebra_map,
--    rw ← mul_one (∥E_c p d hc n a∥), rw ← norm_one_class.norm_one, rw ←norm_algebra_map_eq R _,
    { --congr,
      rw bernoulli_distribution, simp only [linear_map.coe_mk],
      rw sequence_limit_eq _ _ (seq_lim_g_char_fn p d R n a hc hc' h' _),
      rw g_to_seq, rw is_scalar_tower.algebra_map_apply ℚ ℚ_[p] R,
      rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one, }, },
--    { apply_instance, }, },
  rw E_c, simp only,
  obtain ⟨z, hz⟩ := helper_meas_E_c p d a hc' hc,
  rw ring_hom.map_add,
  apply le_trans (norm_add_le _ _) _,
  apply add_le_add_right _ _,
  { apply_instance, },
  { rw hz, rw ring_hom.map_int_cast,
    apply padic_norm_e.norm_int_le_one z, },
    /-apply le_trans (norm_sub_le _ _) _,
    have : ∀ (x : ℚ), ∥int.fract x∥ ≤ 1, --should be separate lemma
    { intro x, convert_to ∥((int.fract x : ℚ) : ℝ)∥ ≤ 1, rw real.norm_of_nonneg _,
      { norm_cast, apply le_of_lt, apply int.fract_lt_one, },
      { norm_cast, apply int.fract_nonneg, }, },
    apply add_le_add,
    { sorry, }, --apply this, },
    { rw ←mul_one (∥(c : ℚ_[p])∥), rw ring_hom.map_mul, apply le_trans (norm_mul_le _ _) _,
      rw map_nat_cast,
      apply mul_le_mul_of_nonneg_left,
      { sorry, }, --apply this _, },
      { apply norm_nonneg, }, }, }, -/
end

--bernoulli_distribution p d R hc hc' h' (loc_const_ind_fn _ p d f)
noncomputable def bernoulli_measure' (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥ ) : measures (units (zmod d) × units ℤ_[p]) R :=
⟨ {
    to_fun := λ f, bernoulli_distribution p d R hc hc' h' (loc_const_ind_fn _ p d f),
    map_add' := begin
      rintros f1 f2,
      convert linear_map.map_add _ _ _,
      ext y,
      repeat { rw loc_const_ind_fn, },
      simp only [pi.add_apply, locally_constant.coe_add, locally_constant.coe_mk],
      repeat {rw ind_fn, },
      simp only [pi.add_apply, locally_constant.coe_add],
      by_cases pos : is_unit y.fst ∧ is_unit y.snd,
      { convert dif_pos pos,
        any_goals { convert dif_pos pos, }, },
      { have : (0 : R) = 0 + 0, rw add_zero,
        convert this,
        any_goals { convert dif_neg pos, }, },
    end,
    map_smul' := begin
      rintros m f,
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, locally_constant.to_fun_eq_coe],
      convert linear_map.map_smul _ _ _,
      ext y,
      repeat { rw loc_const_ind_fn, },
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply,
        locally_constant.coe_mk],
      repeat { rw ind_fn, },
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply],
      by_cases pos : is_unit y.fst ∧ is_unit y.snd,
      { convert dif_pos pos, convert dif_pos pos, },
      { convert (mul_zero m).symm,
        any_goals { convert dif_neg pos, }, },
      end, }, begin
    --simp only [linear_map.coe_mk, locally_constant.to_fun_eq_coe],
    simp only [linear_map.coe_mk, locally_constant.to_fun_eq_coe],
    set K := 1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ with hK,
    have Kpos : 0 < K,
    { rw hK, rw add_comm, apply add_pos_of_nonneg_of_pos,
      { apply norm_nonneg, },
      { apply zero_lt_one, }, },
    refine ⟨K, _, λ f, _⟩,
    { apply Kpos, },
    obtain ⟨n, hn⟩ := loc_const_eq_sum_char_fn p d R (loc_const_ind_fn R p d f) h',
    rw hn,
    rw linear_map.map_sum,
    convert le_trans (na (d * p^n) _) _,
    set a := ⨆ (i : zmod (d * p ^ n)),
      ∥bernoulli_distribution p d R hc hc' h' (((loc_const_ind_fn R p d f) ↑(i.val)) •
      char_fn R (is_clopen_clopen_from p d n (i.val)))∥ with ha,
    set s := {i : zmod (d * p^n) | ∥bernoulli_distribution p d R hc hc' h'
      ((loc_const_ind_fn R p d f) ↑(i.val) • char_fn R
      (is_clopen_clopen_from p d n ↑(i.val)))∥ = a } with hs,
    have nons : set.nonempty s,
    { apply s_nonempty', rw ha, },
    set i := classical.some nons with hi,
    have hi' := classical.some_spec nons,
    rw set.mem_def at hi',
    change ∥bernoulli_distribution p d R hc hc' h' ((loc_const_ind_fn R p d f) ↑(i.val) •
      char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a at hi',
    by_cases is_unit (i : zmod d) ∧ is_unit (i : ℤ_[p]),
    { suffices : a ≤ K * ∥(loc_const_ind_fn R p d f) ↑i∥,
      convert_to a ≤ _,
      apply le_trans this _,
      rw mul_le_mul_left _,
      rw continuous_map.norm_eq_supr_norm,
      apply le_cSup,
      { apply set.finite.bdd_above,
        change (set.range (λ (x : units (zmod d) × units ℤ_[p]), ∥f x∥)).finite,
        refine is_locally_constant.range_finite _,
        change is_locally_constant (norm ∘ f),
        apply is_locally_constant.comp f.is_locally_constant _, },
      { refine ⟨(is_unit.unit h.1, is_unit.unit h.2), _⟩,
        change ∥f.to_fun _ ∥ = _,
        rw ind_fn_eq_fun,
        rw loc_const_ind_fn,
        simp only [function.comp_app, locally_constant.coe_mk, prod.map_mk],
        refine congr_arg _ _, refine congr_arg _ _,
        rw prod.ext_iff,
        simp only [prod.snd_nat_cast, prod.fst_nat_cast, prod.map_mk],
        repeat { rw is_unit.unit_spec, },
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, eq_self_iff_true, and_self], },
      { apply Kpos, },
      { rw ←hi',
        rw linear_map.map_smul,
        rw smul_eq_mul,
        apply le_trans (norm_mul_le _ _) _,
        rw mul_comm, apply mul_le_mul,
        { apply meas_E_c', },
        { simp only [zmod.nat_cast_val], },
        { apply norm_nonneg, },
        { apply le_of_lt, apply Kpos, }, }, },
    { have zer : (loc_const_ind_fn R p d f) ↑(i.val) = 0,
      { rw loc_const_ind_fn, simp only [locally_constant.coe_mk],
        rw ind_fn, convert dif_neg _, convert h,
        { simp only [prod.fst_zmod_cast, zmod.nat_cast_val], },
        { simp only [prod.snd_zmod_cast, zmod.nat_cast_val], }, },
      rw zer at hi', rw zero_smul at hi',
      simp only [linear_map.map_zero, norm_zero, finset.mem_range] at hi',
      rw hi'.symm at ha, rw ←ha,
      apply mul_nonneg,
      { apply le_of_lt, apply Kpos, },
      apply norm_nonneg, },
--this is the proof to show it is also a measure on zmod _ × ℤ_[p]
/-    set K := 1 + ∥(c : ℚ)∥ + ∥((c : ℚ) - 1) / 2∥ with hK,
    have Kpos : 0 < K,
    { rw hK, rw add_comm, apply add_pos_of_nonneg_of_pos,
      { apply norm_nonneg, },
      { rw add_comm, apply add_pos_of_nonneg_of_pos,
        { apply norm_nonneg, },
        { apply zero_lt_one, }, }, },
    refine ⟨K, _, λ f, _⟩,
    { apply Kpos, },
    obtain ⟨n, hn⟩ := loc_const_eq_sum_char_fn p d R f h',
    rw hn,
    rw linear_map.map_sum,
    convert le_trans (na (d * p^n) _) _,
    set a := ⨆ (i : zmod (d * p ^ n)),
      ∥(bernoulli_distribution p d R hc hc' h') ((f ↑(i.val)) • char_fn R (is_clopen_clopen_from p d n (i.val)))∥ with ha,
    set s := {i : zmod (d * p^n) | ∥(bernoulli_distribution p d R hc hc' h')
    (f ↑(i.val) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a } with hs,
    have nons : set.nonempty s,
    { apply s_nonempty', rw ha, },
    set i := classical.some nons with hi,
    have hi' := classical.some_spec nons,
    rw set.mem_def at hi',
    change ∥(bernoulli_distribution p d R hc hc' h')
      (f ↑(i.val) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a at hi',
    --by_cases is_unit (i : zmod d) ∧ is_unit (i : ℤ_[p]),
    { suffices : a ≤ K * ∥f ↑i∥,
      --convert_to a ≤ _,
      apply le_trans this _,
      rw mul_le_mul_left _,
      rw continuous_map.norm_eq_supr_norm,
      apply le_cSup,
      { apply set.finite.bdd_above,
        rw ←hn,
        convert_to (set.range (λ (x : (zmod d) × ℤ_[p]), ∥f x∥)).finite,
        refine is_locally_constant.range_finite _,
        change is_locally_constant (norm ∘ f),
        apply is_locally_constant.comp f.is_locally_constant _, },
      { --refine ⟨(is_unit.unit h.1, is_unit.unit h.2), _⟩,
        rw ←hn,
        refine ⟨i, _⟩, refl,
        /-change ∥f.to_fun _ ∥ = _,
        --rw ind_fn_eq_fun,
        --rw loc_const_ind_fn,
        --simp only [function.comp_app, locally_constant.coe_mk, prod.map_mk],
        apply congr_arg _, apply congr_arg,
        rw prod.ext_iff,
        simp only [prod.snd_nat_cast, prod.fst_nat_cast, prod.map_mk],
        repeat { rw is_unit.unit_spec, },
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, eq_self_iff_true, and_self],-/ },
      { apply Kpos, },
      { rw ←hi',
        rw linear_map.map_smul,
        rw smul_eq_mul,
        apply le_trans (norm_mul_le _ _) _,
        rw mul_comm, apply mul_le_mul,
        { apply meas_E_c', },
        { simp only [zmod.nat_cast_val], },
        { apply norm_nonneg, },
        { apply le_of_lt, apply Kpos, }, }, },
    /-{ have zer : f ↑(i.val) = 0,
      { rw loc_const_ind_fn, simp only [locally_constant.coe_mk],
        rw ind_fn, convert dif_neg _, convert h,
        { simp only [prod.fst_zmod_cast, zmod.nat_cast_val], },
        { simp only [prod.snd_zmod_cast, zmod.nat_cast_val], }, },
      rw zer at hi', rw zero_smul at hi',
      simp only [linear_map.map_zero, norm_zero, finset.mem_range] at hi',
      rw hi'.symm at ha, rw ←ha,
      apply mul_nonneg, },
      --{ apply le_of_lt, apply Kpos, }, }, -/
    --apply norm_nonneg, },
    --sorry, -/
   end⟩
