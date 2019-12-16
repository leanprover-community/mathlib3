/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Casper Putz

Characteristic polynomials of matrices
-/

import data.polynomial linear_algebra.determinant tactic.interactive

/-!

# Charateristic polynomials

This file defines the characteristic polynomial of a square matrix
over a commutative ring. We prove that the characteristic polynomial
of an nxn-matrix is monic of degree n.

## Main definitions

char_polynomial

## Tags

matrix, char_polynomial

-/

open polynomial matrix finset

universes u v w

variables {α : Type u} [decidable_eq α]
variables {n : Type v} [decidable_eq n] [fintype n]

noncomputable def char_matrix [comm_ring α] (M : matrix n n α) : matrix n n (polynomial α) :=
diagonal (λ _:n, (X : polynomial α)) - (λ i j, C (M i j))

/-- The characteristic polynomial of the matrix `M` is the determinant of the matrix `IₙX - M`
where `X` is a variable and `Iₙ` is the n×n unit matrix. -/
noncomputable def char_polynomial [comm_ring α] (M : matrix n n α) : polynomial α :=
det (char_matrix M)

namespace characteristic_polynomial

variables (M : matrix n n α)

lemma char_matrix_apply [comm_ring α] (i j : n) : char_matrix M i j =
  if i = j then X - C (M i i) else -C (M i j) :=
by { unfold char_matrix diagonal, dsimp, split_ifs with h h, rw [h], rw [zero_add] }

/-- The evaluation of the characteristic polynomial of `M` at `b` is equal to `det (Iₙb - M)`.-/
lemma eval [comm_ring α] (b : α) : eval b (char_polynomial M) = det (diagonal (λ _, b) - M) :=
begin
  change (λ p : polynomial α, eval b p) (det (diagonal (λ _:n, X) - λ (i j : n), C (M i j))) = _,
  rw [det_map_hom (λ p : polynomial α, eval b p)],
  congr, ext, simp [diagonal],
  split_ifs,
  exact eval_X,
  exact eval_zero
end

/-- The constant coefficient of the characteristic polynomial of `M` is `±det M`. -/
lemma constant_coeff [comm_ring α] : coeff (char_polynomial M) 0 = (-1) ^ fintype.card n * det M :=
by rw [coeff_zero_eq_eval_zero, eval, diagonal_zero, zero_sub, det_neg]

/-
lemma degree_det_le [comm_ring α] {M : matrix n n (polynomial α)} {b : ℕ} (hM : ∀ i j, degree (M i j) ≤ b) :
  degree (det M) ≤ ↑(fintype.card n * b) :=
begin
  refine le_trans (degree_sum_le _ _) (sup_le _),
  intros p hp,
  rw [degree_mul_eq],
  rw [show degree ↑(equiv.perm.sign p : ℤ) = 0, from @degree_eq_zero_of_is_unit α _ _ (is_unit_of_mul_one _ _
    (by {rw [←int.cast_mul, ←units.coe_mul, ←pow_two, int.units_pow_two, units.coe_one, int.cast_one]}))],
  rw [zero_add, ←nat.cast_id (fintype.card n), ←add_monoid.smul_eq_mul, fintype.card, ←sum_const,
    with_bot.coe_sum, degree_prod],
  exact sum_le_sum (λ _ _, hM _ _)
end-/

lemma degree_prod [integral_domain α] {ι : Type*} [decidable_eq ι] (s : finset ι) (f : ι → polynomial α) :
  degree (s.prod f) = s.sum (λ i, degree (f i)) :=
finset.induction_on s
  (by { rw [prod_empty, sum_empty, degree_one] })
  (by { intros i s hs h, rw [sum_insert hs, prod_insert hs, degree_mul_eq, h] })

lemma cofactor_aux [comm_ring α] (i : n) (M : matrix n n α) :
  cofactor i i (diagonal (λ _:n, (X : polynomial α)) - (λ i j, C (M i j))) =
  char_polynomial (minor M (subtype.val : {k // k ≠ i} → n) subtype.val) := sorry

variable [integral_domain α]

lemma degree_det_le {M : matrix n n (polynomial α)} {b : ℕ} (hM : ∀ i j, degree (M i j) ≤ b) :
  degree (det M) ≤ ↑(fintype.card n * b) :=
begin
  refine le_trans (degree_sum_le _ _) (sup_le _),
  intros p hp,
  rw [degree_mul_eq],
  rw [show degree ↑(equiv.perm.sign p : ℤ) = 0, from @degree_eq_zero_of_is_unit α _ _ (is_unit_of_mul_one _ _
    (by {rw [←int.cast_mul, ←units.coe_mul, ←pow_two, int.units_pow_two, units.coe_one, int.cast_one]}))],
  rw [zero_add, ←nat.cast_id (fintype.card n), ←add_monoid.smul_eq_mul, fintype.card, ←sum_const,
    /-with_bot.coe_sum,-/ degree_prod],
  sorry--exact sum_le_sum (λ _ _, hM _ _)
end

lemma degree_aux (i : n) (hn : fintype.card n ≠ 0) :
  degree ((erase univ i).sum (λ j, char_matrix M j i * cofactor i j (char_matrix M))) < fintype.card n :=
begin
  have : (nat.pred $ fintype.card n : with_bot ℕ) < (fintype.card n),
    from with_bot.coe_lt_coe.mpr (nat.pred_lt hn),
  refine lt_of_le_of_lt (degree_sum_le _ _) (lt_of_le_of_lt (sup_le _) this),
  intros j hji, rw [mem_erase] at hji,
  rw [degree_mul_eq, char_matrix_apply, if_neg hji.1, degree_neg],
  by_cases h0 : M j i = 0, { rw [h0, C_0, degree_zero, with_bot.bot_add], exact lattice.bot_le },
  rw [degree_C h0, zero_add, cofactor, degree_mul_eq, equiv.perm.sign_swap (ne.symm hji.1)], simp,
  rw [show (nat.pred (fintype.card n) : with_bot ℕ) = ↑(fintype.card {k // k ≠ i} * 1),
      { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card, mul_one],
        intro, simp only [mem_erase, mem_univ, and_true] }],
  convert degree_det_le _,
  apply_instance,
  intros k l, change degree (char_matrix M (equiv.swap i j k.val) l.val) ≤ 1,
  rw [char_matrix_apply],
  split_ifs with h h,
  { rw [degree_X_sub_C], exact le_refl 1 },
  { rw [degree_neg], by_cases h0 : M (equiv.swap i j k.val) l.val = 0,
    { rw [h0, C_0, degree_zero], exact lattice.bot_le },
    { rw [degree_C h0, ←with_bot.coe_zero, ←with_bot.coe_one, with_bot.coe_le_coe], exact zero_le_one } }
end

lemma subtype_swap_self (i : n) : subtype_swap i i = id :=
begin rw [subtype_swap], conv { congr, congr, rw [equiv.swap_self, equiv.refl] }, exact subtype.map_id end

lemma cofactor_diag_apply (i : n) : cofactor i i (char_matrix M) =
  char_polynomial (minor M (subtype.val ∘ subtype_swap i i) subtype.val) :=
by { unfold cofactor char_polynomial,
  rw [subtype_swap_self, function.comp.right_id, equiv.swap_self, equiv.perm.sign_refl, units.coe_one, int.cast_one, one_mul],
  congr, funext k l,
  unfold minor, rw [char_matrix_apply, char_matrix_apply],
  simp only [subtype.ext], congr }

lemma char_polynomial_aux {β : Type*} [add_monoid β] (f : polynomial α → β)
  (hone : f 1 = 0)
  (hmul : ∀ p q, f (p * q) = f p + f q)
  (hadd : ∀ p q, degree q < degree p → f (q + p) = f p) :
  f (char_polynomial M) = f (X ^ fintype.card n) :=
begin
  unfreezeI,
  induction h : fintype.card n generalizing M n f β,
  { unfold char_polynomial det,
    have : (univ : finset n) = ∅, { rwa [←card_eq_zero, card_univ] },
    rw [this], conv { congr, congr, congr, skip, funext, rw [prod_empty, mul_one] },
    have : ∀ σ : equiv.perm n, σ = 1, from λ σ, equiv.perm.ext σ 1
      (λ i, absurd (by rw ←this; exact mem_univ i) (not_mem_empty i)),
    have : (univ : finset (equiv.perm n)) = finset.singleton 1, from finset.ext.2
      (λ _, ⟨λ _, by { rw [mem_singleton], exact this _ }, λ _, mem_univ _⟩), --make this a seperate lemma
    rw [this, sum_singleton, equiv.perm.sign_one], change f ↑1 = f 1, rw [nat.cast_one] },
  { unfold char_polynomial,
    -- n_1 is nonempty so we can get some row index i
    let i : n_1 := classical.choice (fintype.card_pos_iff.mp (eq.symm h ▸ nat.succ_pos n)),
    rw [cofactor_expansion _ i, ←insert_erase (mem_univ i), sum_insert (not_mem_erase i _), add_comm],
    have : fintype.card {k // k ≠ i} = n,
    { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card, h,
        nat.pred_succ], intro, simp only [mem_erase, mem_univ, and_true] },
    rw [hadd],
    { rw [pow_succ, hmul, hmul, char_matrix_apply, if_pos rfl, sub_eq_add_neg, add_comm, hadd,
        cofactor_diag_apply, ih _ f hone hmul hadd this],
      rw [degree_neg],
      refine lt_of_le_of_lt degree_C_le _,
      rw [degree_X, ←with_bot.coe_zero, ←with_bot.coe_one, with_bot.coe_lt_coe],
      exact zero_lt_one },
    { rw [cofactor_diag_apply, degree_mul_eq, char_matrix_apply, if_pos rfl, degree_X_sub_C],
      /-rw [ih _ degree degree_one (λ _ _, degree_mul_eq) (λ _ _, degree_add_eq_of_degree_lt) this],
      { rw [add_comm, degree_X_pow,  ←with_bot.coe_one, ←with_bot.coe_add, ←nat.succ_eq_add_one, h],
        refine degree_aux _ _ _, rw [←h], exact nat.succ_ne_zero _ }-/ sorry } }
end

--@[to_additive]
lemma char_polynomial_aux_mul {β : Type*} [monoid β] (f : polynomial α → β)
  (hone : f 1 = 1)
  (hmul : ∀ p q, f (p * q) = f p * f q)
  (hadd : ∀ p q, degree q < degree p → f (q + p) = f p) :
  f (char_polynomial M) = f (X ^ fintype.card n) :=
begin
  unfreezeI,
  induction h : fintype.card n generalizing M n f β,
  { unfold char_polynomial det,
    have : (univ : finset n) = ∅, { rwa [←card_eq_zero, card_univ] },
    rw [this], conv { congr, congr, congr, skip, funext, rw [prod_empty, mul_one] },
    have : ∀ σ : equiv.perm n, σ = 1, from λ σ, equiv.perm.ext σ 1
      (λ i, absurd (by rw ←this; exact mem_univ i) (not_mem_empty i)),
    have : (univ : finset (equiv.perm n)) = finset.singleton 1, from finset.ext.2
      (λ _, ⟨λ _, by { rw [mem_singleton], exact this _ }, λ _, mem_univ _⟩), --make this a seperate lemma
    rw [this, sum_singleton, equiv.perm.sign_one], change f ↑1 = f 1, rw [nat.cast_one] },
  { unfold char_polynomial,
    -- n_1 is nonempty so we can get some row index i
    let i : n_1 := classical.choice (fintype.card_pos_iff.mp (eq.symm h ▸ nat.succ_pos n)),
    rw [cofactor_expansion _ i, ←insert_erase (mem_univ i), sum_insert (not_mem_erase i _), add_comm],
    have : fintype.card {k // k ≠ i} = n,
    { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card, h,
        nat.pred_succ], intro, simp only [mem_erase, mem_univ, and_true] },
    rw [hadd],
    { rw [pow_succ, hmul, hmul, char_matrix_apply, if_pos rfl, sub_eq_add_neg, add_comm, hadd,
        cofactor_diag_apply, ih _ f hone hmul hadd this],
      rw [degree_neg],
      refine lt_of_le_of_lt degree_C_le _,
      rw [degree_X, ←with_bot.coe_zero, ←with_bot.coe_one, with_bot.coe_lt_coe],
      exact zero_lt_one },
    { rw [cofactor_diag_apply, degree_mul_eq, char_matrix_apply, if_pos rfl, degree_X_sub_C],
      /-rw [@ih _ _ _ _ (multiplicative $ with_bot ℕ) _ degree degree_one (λ _ _, degree_mul_eq)
        (λ _ _, degree_add_eq_of_degree_lt) this],
      rw [add_comm, degree_X_pow,  ←with_bot.coe_one, ←with_bot.coe_add, ←nat.succ_eq_add_one, h],
      refine degree_aux _ _ _, rw [←h], exact nat.succ_ne_zero _-/ sorry } }
end

/-- The degree of the characteristic polynomial of `M` is equal to its dimension. -/
lemma degree : degree (char_polynomial M) = fintype.card n :=
by { rw [←@degree_X_pow α], exact char_polynomial_aux M degree degree_one (λ _ _, degree_mul_eq)
    (λ _ _, degree_add_eq_of_degree_lt) }

/-- The characteristic polynomial of `M` is monic. -/
lemma monic : leading_coeff (char_polynomial M) = 1 :=
by { rw [←leading_coeff_X_pow (fintype.card n)], exact char_polynomial_aux_mul M leading_coeff
  leading_coeff_one leading_coeff_mul (λ _ _, leading_coeff_add_of_degree_lt) }

/-- The characteristic polynomial of `M` is nonzero. -/
lemma ne_zero (hn : fintype.card n > 0) : char_polynomial M ≠ 0 :=
ne_zero_of_degree_gt $ begin
  rw [degree M, with_bot.coe_lt_coe],
  exact nat.pred_lt (nat.pos_iff_ne_zero.mp hn)
end

/-
/-- The degree of the characteristic polynomial of `M` is equal to its dimension. -/
lemma degree : degree (char_polynomial M) = fintype.card n :=
begin
  unfreezeI,
  induction h : fintype.card n generalizing M n,
  { unfold char_polynomial det,
    have : (univ : finset n) = ∅, { rwa [←card_eq_zero, card_univ] },
    rw [this], conv { congr, congr, congr, skip, funext, rw [prod_empty, mul_one] },
    have : ∀ σ : equiv.perm n, σ = 1, from λ σ, equiv.perm.ext σ 1
      (λ i, absurd (by rw ←this; exact mem_univ i) (not_mem_empty i)),
    have : (univ : finset (equiv.perm n)) = finset.singleton 1, from finset.ext.2
      (λ _, ⟨λ _, by { rw [mem_singleton], exact this _ }, λ _, mem_univ _⟩), --make this a seperate lemma
    rw [this, sum_singleton, equiv.perm.sign_one, units.coe_one, int.cast_one, degree_one, with_bot.coe_zero] },
  { let h := eq.symm h,
    unfold char_polynomial,
  -- n_1 is nonempty so we can get some row index i
    let i : n_1 := classical.choice (fintype.card_pos_iff.mp (h ▸ nat.succ_pos n)),
    rw [cofactor_expansion _ i, ←insert_erase (mem_univ i), sum_insert (not_mem_erase i _), add_comm],
    have : fintype.card {k // k ≠ i} = n,
    { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card, ←h,
        nat.pred_succ], intro, simp only [mem_erase, mem_univ, and_true] },
    convert degree_add_eq_of_degree_lt _;
      rw [cofactor_diag_apply, degree_mul_eq, char_matrix_apply, if_pos rfl, degree_X_sub_C, ih _ this,
        add_comm, ←with_bot.coe_one, ←with_bot.coe_add, ←nat.succ_eq_add_one, h],
    { refine degree_aux _ _ _, rw [←h], exact nat.succ_ne_zero _ } }
end



/-- The characteristic polynomial of `M` is monic. -/
lemma monic : leading_coeff (char_polynomial M) = 1 :=
begin
  unfreezeI,
  induction h : fintype.card n generalizing M n,
  { unfold char_polynomial det,
    have : (univ : finset n) = ∅, { rwa [←card_eq_zero, card_univ] },
    rw [this], conv { congr, congr, congr, skip, funext, rw [prod_empty, mul_one] },
    have : ∀ σ : equiv.perm n, σ = 1, from λ σ, equiv.perm.ext σ 1
      (λ i, absurd (by rw ←this; exact mem_univ i) (not_mem_empty i)),
    have : (univ : finset (equiv.perm n)) = finset.singleton 1, from finset.ext.2
      (λ _, ⟨λ _, by { rw [mem_singleton], exact this _ }, λ _, mem_univ _⟩), --make this a seperate lemma
    rw [this, sum_singleton, equiv.perm.sign_one, units.coe_one, int.cast_one, leading_coeff_one] },
  { let h := eq.symm h,
    unfold char_polynomial,
  -- n_1 is nonempty so we can get some row index i
    let i : n_1 := classical.choice (fintype.card_pos_iff.mp (h ▸ nat.succ_pos n)),
    rw [cofactor_expansion _ i, ←insert_erase (mem_univ i), sum_insert (not_mem_erase i _), add_comm],
    have : fintype.card {k // k ≠ i} = n,
    { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card, ←h,
        nat.pred_succ], intro, simp only [mem_erase, mem_univ, and_true] },
    convert leading_coeff_add_of_degree_lt _,
    { rw [cofactor_diag_apply, leading_coeff_mul, char_matrix_apply, if_pos rfl,
        monic.def.mp (monic_X_sub_C _), one_mul, ih _ this] },
    { rw [cofactor_diag_apply, degree_mul_eq, char_matrix_apply, if_pos rfl, degree_X_sub_C, degree,
        this, add_comm, ←with_bot.coe_one, ←with_bot.coe_add, ←nat.succ_eq_add_one, h],
      refine degree_aux _ _ _, rw [←h], exact nat.succ_ne_zero _ } }
end
-/

end characteristic_polynomial
