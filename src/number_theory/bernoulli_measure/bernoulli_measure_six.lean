/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_measure.bernoulli_measure_five

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
 * `g_to_seq` replaced with `from_loc_const_to_seq`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {p : ℕ} [fact p.prime] {d : ℕ} (R : Type*) [normed_comm_ring R]
variables {c : ℕ} [fact (0 < d)]

set_option old_structure_cmd true

open_locale big_operators

open padic_int zmod nat locally_constant eventually_constant_seq

namespace clopen_from
lemma char_fn_eq {n : ℕ} (i : zmod (d * p^n)) :
  char_fn R (clopen_from.is_clopen (i.val : zmod (d * p^n))) =
  char_fn R (clopen_from.is_clopen i) := by { congr, rw [nat_cast_val, zmod.cast_id], }
end clopen_from

open clopen_from

lemma helper_3 (f : locally_constant ((zmod d) × ℤ_[p]) R) {n : ℕ} (i : zmod (d * p^n)) :
  (f (i.val)) • char_fn R (clopen_from.is_clopen (i.val : zmod (d * p^n))) =
  f i • char_fn R (clopen_from.is_clopen i) := by { rw [nat_cast_val, char_fn_eq], }

lemma s_nonempty' [normed_algebra ℚ_[p] R] (hc : c.coprime p) (hc' : c.coprime d)
  (h' : d.coprime p) (n : ℕ) (f : locally_constant ((zmod d) × ℤ_[p]) R) :
  {i : zmod (d * p^n) | ∥(loc_const_to_seq_limit R hc hc' h') (f ↑i •
  char_fn R (clopen_from.is_clopen i))∥ = ⨆ (i : zmod (d * p ^ n)),
  ∥(loc_const_to_seq_limit R hc hc' h') (f i • char_fn R (clopen_from.is_clopen i))∥ }.nonempty :=
begin
  have := set.nonempty.cSup_mem _ _,
  swap 4, { refine set.range (λ (i : zmod (d * p^n)), ∥((loc_const_to_seq_limit R hc hc' h'))
    (f ↑i • char_fn R (clopen_from.is_clopen i))∥), },
  { cases this with y hy,
    simp only [algebra.id.smul_eq_mul, linear_map.map_smul] at hy,
    refine ⟨y, _⟩,
    simp only [zmod.cast_id', algebra.id.smul_eq_mul, id.def, set.mem_set_of_eq,
      finset.mem_range, linear_map.map_smul, nat_cast_val, hy, Sup_range], },
  { apply_instance, },
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  { rw ←set.image_univ, apply set.finite.image, exact set.finite_univ, },
end

@[to_additive]
lemma prod_coe_to_finset {α : Type*} {β :Type*} [comm_monoid β] (s : set α) [fintype s] (f : α → β) :
  ∏ (i : α) in s.to_finset, f i = ∏ (i : s), f i :=
finset.prod_bij (λ t ht, ⟨t, set.mem_to_finset.1 ht⟩) (λ a ha, finset.mem_univ _)
  (λ a ha, by { simp only [subtype.coe_mk] }) (λ b c hb hc h, subtype.mk_eq_mk.1 h)
  (λ b hb, ⟨b.val, set.mem_to_finset.2 b.prop, by { simp }⟩)

lemma from_loc_const_to_seq [algebra ℚ_[p] R] {n : ℕ} (a : zmod (d * p^n)) (hc : c.coprime p)
  (hc' : c.coprime d) (h' : d.coprime p) :
  (from_loc_const R hc hc' (char_fn R (clopen_from.is_clopen a)) h').to_seq n =
  (algebra_map ℚ_[p] R) (E_c p d c n a) :=
begin
  rw from_loc_const_char_fn R a hc hc' h' (le_refl n),
  convert_to _ = ∑ (y : zmod (d * p^n)) in {a}, (algebra_map ℚ_[p] R) (E_c p d c n ↑y),
  { rw [finset.sum_singleton, zmod.cast_id], },
  { convert_to ∑ (y : zmod (d * p^n)) in (set.to_finset (equi_class n a)),
      (algebra_map ℚ_[p] R) (E_c p d c n ↑y) = _,
    { simp_rw [sum_coe_to_finset, zmod.cast_id], },
    { apply finset.sum_congr (finset.ext_iff.2 (λ y, _)) (λ x hx, rfl),
      { simp only [set.mem_to_finset, finset.mem_singleton, mem_equi_class, zmod.cast_id], }, }, },
end

lemma meas_E_c' [normed_algebra ℚ_[p] R] [norm_one_class R] {n : ℕ} {a : zmod (d * p^n)}
  (hc : c.coprime p) (hc' : c.coprime d) (h' : d.coprime p) : ∥(loc_const_to_seq_limit R hc hc' h')
  (char_fn R (clopen_from.is_clopen a))∥ ≤ 1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ :=
begin
  convert_to ∥(algebra_map ℚ_[p] R) (E_c p d c n a)∥ ≤ _,
  { rw [linear_map.coe_mk, sequence_limit_eq _ _ (seq_lim_from_loc_const_char_fn R a hc hc' h'),
      from_loc_const_to_seq], },
  obtain ⟨z, hz⟩ := helper_meas_E_c a hc' hc,
  rw [E_c], simp only,
  rw [ring_hom.map_add, norm_algebra_map'],
  apply le_trans (norm_add_le _ _) (add_le_add_right _ _),
  rw [hz, ring_hom.map_int_cast],
  apply padic_norm_e.norm_int_le_one z,
end

open loc_const_ind_fn

/-- Constructs a Bernoulli measure from `loc_const_to_seq_limit`. -/
-- we choose to work with `val` and `nat` because it gives common ground without having to use CRT
noncomputable def bernoulli_measure' [normed_algebra ℚ_[p] R] [norm_one_class R] [nontrivial R]
  (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (h' : d.gcd p = 1)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥) :
  measures (units (zmod d) × units ℤ_[p]) R :=
⟨ { to_fun := λ f, loc_const_to_seq_limit R hc hc' h' (loc_const_ind_fn f),
    map_add' := λ f1 f2, by { rw [add, linear_map.map_add], },
    map_smul' := λ m f, by { rw [smul R m f, linear_map.map_smul, ring_hom.id_apply], }, },
  begin
    set K := 1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ with hK,
    have Kpos : 0 < K,
    { rw [hK, add_comm],
      apply add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, },
    refine ⟨K, Kpos, λ f, _⟩,
    obtain ⟨n, hn⟩ := loc_const_eq_sum_char_fn R (loc_const_ind_fn f) h',
    change ∥loc_const_to_seq_limit R hc hc' h' (loc_const_ind_fn f)∥ ≤ _,
    rw [hn, linear_map.map_sum],
    apply le_trans (na (d * p^n) _) _,
    simp_rw [helper_3],
    set i := (s_nonempty' R hc hc' h' n (loc_const_ind_fn f)).some with hi,
    have hi' := (s_nonempty' R hc hc' h' n (loc_const_ind_fn f)).some_spec,
    change ∥loc_const_to_seq_limit R hc hc' h' ((loc_const_ind_fn f) ↑i •
      char_fn R (clopen_from.is_clopen i))∥ = ⨆ (i : zmod (d * p ^ n)),
      ∥loc_const_to_seq_limit R hc hc' h' (((loc_const_ind_fn f) ↑i) •
      char_fn R (clopen_from.is_clopen i))∥ at hi',
    by_cases is_unit (i : zmod d × ℤ_[p]).fst ∧ is_unit (i : zmod d × ℤ_[p]).snd,
    { suffices : (⨆ (i : zmod (d * p ^ n)), ∥loc_const_to_seq_limit R hc hc' h'
        (((loc_const_ind_fn f) ↑i) • char_fn R (clopen_from.is_clopen i))∥) ≤
        K * ∥(loc_const_ind_fn f) ↑i∥,
      { apply le_trans this ((mul_le_mul_left Kpos).2 _),
        rw continuous_map.norm_eq_supr_norm,
        refine le_cSup (set.finite.bdd_above (is_locally_constant.range_finite
          (is_locally_constant.comp f.is_locally_constant _))) ⟨(is_unit.unit h.1,
          is_unit.unit h.2), by { rw [loc_const_ind_fn_def, ind_fn.map_ind_fn_eq_fn _ h], refl, }⟩, },
      { rw [←hi', linear_map.map_smul, smul_eq_mul],
        apply le_trans (norm_mul_le _ _) _,
        rw mul_comm,
        refine mul_le_mul (meas_E_c' R hc hc' h') le_rfl (norm_nonneg _) (le_of_lt Kpos), }, },
    { rw [loc_const_ind_fn_def, ind_fn.map_ind_fn_eq_zero _ h, zero_smul, linear_map.map_zero,
        norm_zero] at hi',
      rw [←hi'],
      apply mul_nonneg (le_of_lt Kpos) (norm_nonneg _), }, end⟩
