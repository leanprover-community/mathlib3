/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.basic
import ring_theory.witt_vector.nice_poly
import ring_theory.witt_vector.witt_vector_preps

/-! ## Truncation ideals -/

namespace witt_vector

variables (p : ℕ) {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial
include hp

section coeff_witt_mul

lemma witt_mul_nice (n : ℕ) : (witt_mul p n).nice :=
begin
  apply nice.of_map_of_injective (int.cast_ring_hom ℚ) (int.cast_injective),
  rw [witt_mul, map_witt_structure_int, ring_hom.map_mul, map_X, map_X],
  apply nice.bind₁_left _ _ _ (constant_coeff_X_in_terms_of_W p ℚ n),
  intros i,
  rw [alg_hom.map_mul, bind₁_X_right, bind₁_X_right],
  intros d hd b,
  contrapose! hd,
  rw [coeff_mul, finset.sum_eq_zero],
  rintro ⟨x, y⟩ hxy,
  rw finsupp.mem_antidiagonal_support at hxy,
  subst hxy,
  contrapose! hd,
  have hx : ((rename (prod.mk tt)) (witt_polynomial p ℚ i)).coeff x ≠ 0,
  { intro H, simpa only [H, zero_mul, eq_self_iff_true, not_true, ne.def] using hd, },
  have hy : ((rename (prod.mk ff)) (witt_polynomial p ℚ i)).coeff y ≠ 0,
  { intro H, simpa only [H, mul_zero, eq_self_iff_true, not_true, ne.def] using hd, },
  obtain ⟨x, rfl⟩ := coeff_rename_ne_zero _ _ _ hx,
  obtain ⟨y, rfl⟩ := coeff_rename_ne_zero _ _ _ hy,
  clear hd, dsimp at *,
  rw coeff_rename_map_domain _ (prod_mk_injective _) at hx hy,
  have hx' : x.map_domain (prod.mk tt) = x.emb_domain ⟨prod.mk tt, prod_mk_injective _⟩,
  { rw [finsupp.emb_domain_eq_map_domain], refl },
  have hy' : y.map_domain (prod.mk ff) = y.emb_domain ⟨prod.mk ff, prod_mk_injective _⟩,
  { rw [finsupp.emb_domain_eq_map_domain], refl },
  rw [hx', hy', finsupp.support_add_eq, finsupp.support_emb_domain, finsupp.support_emb_domain];
  clear hx' hy',
  swap,
  { simp only [finsupp.support_emb_domain],
    intro a,
    erw [finset.mem_inter, finset.mem_map, finset.mem_map],
    rintro ⟨⟨k, hk, rfl⟩, ⟨l, hl, H⟩⟩,
    simpa only [prod.mk.inj_iff, function.embedding.coe_fn_mk, false_and] using H, },
  cases b,
  { obtain ⟨j, hj⟩ : y.support.nonempty,
    { rw [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty],
      rintro rfl,
      rw [← constant_coeff_eq, constant_coeff_witt_polynomial] at hy,
      contradiction },
    use j,
    rw finset.mem_union, right,
    rw finset.mem_map,
    exact ⟨j, hj, rfl⟩ },
  { obtain ⟨j, hj⟩ : x.support.nonempty,
    { rw [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty],
      rintro rfl,
      rw [← constant_coeff_eq, constant_coeff_witt_polynomial] at hx,
      contradiction },
    use j,
    rw finset.mem_union, left,
    rw finset.mem_map,
    exact ⟨j, hj, rfl⟩ }
end

lemma coeff_witt_mul' (n : ℕ) (d : bool × ℕ →₀ ℕ) (hd : (witt_mul p n).coeff d ≠ 0) (b : bool) :
  ∃ k, d ⟨b, k⟩ ≠ 0 :=
by { simp only [← finsupp.mem_support_iff], apply witt_mul_nice p n hd }

lemma coeff_witt_mul (n : ℕ) (d : bool × ℕ →₀ ℕ) (hd : (witt_mul p n).coeff d ≠ 0) (b : bool) :
  ∃ k ≤ n, d ⟨b, k⟩ ≠ 0 :=
begin
  obtain ⟨k, hk⟩ := coeff_witt_mul' p n d hd b,
  refine ⟨k, _, hk⟩,
  suffices : (b, k) ∈ (witt_mul p n).vars,
  { replace := witt_mul_vars p n this,
    simp only [fintype.univ_bool, finset.mem_insert, finset.mem_singleton,
      finset.mem_range, finset.mem_product] at this,
    exact nat.le_of_lt_succ this.2, },
  rw mem_vars,
  exact ⟨d, finsupp.mem_support_iff.mpr hd, finsupp.mem_support_iff.mpr hk⟩,
end

end coeff_witt_mul

section ideal

lemma mul_coeff_eq_zero (n : ℕ) (x : 𝕎 R) {y : 𝕎 R}
  (hy : ∀ (i : ℕ), i ≤ n → coeff i y = 0) :
  (x * y).coeff n = 0 :=
begin
  rw mul_coeff,
  apply aeval_eq_zero,
  intros d hd,
  obtain ⟨k, hk, hdk⟩ := coeff_witt_mul p n d hd ff,
  rw ← finsupp.mem_support_iff at hdk,
  exact ⟨⟨ff, k⟩, hdk, hy k hk⟩,
end

variables (p R)
noncomputable def ideal (n : ℕ) : ideal (𝕎 R) :=
{ carrier := {x | ∀ i < n, x.coeff i = 0},
  zero_mem' := by { intros i hi, rw zero_coeff },
  add_mem' :=
  begin
    intros x y hx hy i hi,
    rw [add_coeff, aeval_eq_constant_coeff_of_vars, constant_coeff_witt_add, ring_hom.map_zero],
    rintro ⟨⟨⟩, k⟩ hk,
    all_goals
    { replace hk := witt_add_vars p i hk,
      simp only [true_and, and_true, false_or, or_false, eq_self_iff_true, fintype.univ_bool,
        finset.mem_insert, finset.mem_singleton, finset.mem_range, finset.mem_product] at hk,
      apply_assumption,
      exact lt_of_lt_of_le hk hi }
  end,
  smul_mem' :=
  begin
    intros x y hy i hi,
    rw [smul_eq_mul],
    apply mul_coeff_eq_zero,
    intros j hj,
    apply hy _ (lt_of_le_of_lt hj hi),
  end }

lemma mem_ideal_iff {n : ℕ} {x : 𝕎 R} : x ∈ ideal p R n ↔ ∀ i < n, x.coeff i = 0 :=
iff.refl _

end ideal

end witt_vector
