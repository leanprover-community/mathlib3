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

universes u v

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

/-lemma degree : degree (char_polynomial M) = fintype.card n :=
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
{ unfold char_polynomial,
  -- n_1 is nonempty so we can get some row index i
  let i : n_1 := classical.choice (fintype.card_pos_iff.mp (eq.symm h ▸ nat.succ_pos n)),
  rw [cofactor_expansion _ i, ←insert_erase (mem_univ i), sum_insert (not_mem_erase i _), add_comm],
  have hs : ↑(nat.succ n) =
    degree
      ((diagonal (λ (_x : n_1), X) - λ (i j : n_1), C (M i j)) i i *
         cofactor i i (diagonal (λ (_x : n_1), X) - λ (i j : n_1), C (M i j))),
    { rw [degree_mul_eq], dsimp, rw [diagonal_val_eq, ←sub_eq_add_neg, degree_X_sub_C, add_comm],
      rw [nat.succ_eq_add_one, with_bot.coe_add, with_bot.coe_one],
      congr,
      rw [←sub_eq_add_neg, cofactor_aux, ih],
      rw [←nat.pred_succ n, ←h, ←@card_univ n_1, ←card_erase_of_mem (mem_univ i)],
      refine fintype.card_of_subtype _ (λ _, by simp only [mem_erase, mem_univ, iff_self, and_true]) },
  convert degree_add_eq_of_degree_lt _,
  rw [←hs],
  have : ∀ (m : with_bot ℕ) (n : ℕ), m ≤ n → m < nat.succ n,
    { intros m n h, refine lt_of_le_of_lt h _, rw [with_bot.coe_lt_coe], exact nat.lt_succ_self _ },
  refine this _ _ (le_trans (degree_sum_le _ _) (sup_le _)),
  intros j hj,
  rw [degree_mul_eq, diagonal],
  dsimp,
  rw [if_neg (ne_of_mem_erase hj), zero_add, degree_neg, ←zero_add ↑n],
  refine add_le_add' _ _,
  { by_cases h0 : M j i = 0, { rw [h0, C_0, degree_zero], exact lattice.bot_le }, { rw [degree_C h0], exact le_refl 0 } },
  { unfold cofactor,
    rw [degree_mul_eq, equiv.perm.sign_swap (ne.symm $ ne_of_mem_erase hj)], simp,
    rw [show (n : with_bot ℕ) = ↑(fintype.card {k // k ≠ i} * 1),
      { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card,
          h, nat.pred_succ, mul_one], intro, simp only [mem_erase, mem_univ, and_true] }],
    refine degree_det_le _,
    intros k l,
    change degree ((ite (equiv.swap i j k.val = l.val) X 0) + -C (M (equiv.swap i j k.val) l.val)) ≤ 1,
    split_ifs with h h,
    { rw [←sub_eq_add_neg, degree_X_sub_C], exact le_refl 1 },
    { rw [zero_add, degree_neg],
      by_cases h0 : M (equiv.swap i j k.val) l.val = 0,
      { rw [h0, C_0, degree_zero], exact lattice.bot_le },
      { rw [degree_C h0, ←with_bot.coe_zero, ←with_bot.coe_one, with_bot.coe_le_coe], exact zero_le_one } } } }
end-/

#check char_polynomial M

lemma degree_aux (i : n) :
  degree ((erase univ i).sum (λ j, char_matrix M j i * cofactor i j (char_matrix M))) < fintype.card n :=
begin
  have : (nat.pred $ fintype.card n : with_bot ℕ) < (fintype.card n), from sorry,
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
sorry
--begin rw [subtype_swap], unfold_coes, conv { congr, congr, congr, rw [equiv.swap_self] }, rw [subtype.map_id], end

lemma cofactor_diag_apply (i : n) : cofactor i i (char_matrix M) =
  char_polynomial (minor M (subtype.val ∘ subtype_swap i i) subtype.val) :=
by { unfold cofactor char_polynomial,
  rw [subtype_swap_self, function.comp.right_id, equiv.swap_self, equiv.perm.sign_refl, units.coe_one, int.cast_one, one_mul],
  congr, funext k l,
  unfold minor, rw [char_matrix_apply, char_matrix_apply],
  simp only [subtype.ext], congr }

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
        add_comm, ←with_bot.coe_one, ←with_bot.coe_add],
    { convert degree_aux _ _ } }
end

lemma leading_coeff : leading_coeff (char_polynomial M) = 1 :=
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
    rw [cofactor_diag_apply, leading_coeff_mul, char_matrix_apply, if_pos rfl,
      monic.def.mp (monic_X_sub_C _), one_mul, ih _ this],
    sorry
  }
end

lemma degree_coeff_aux : degree (char_polynomial M) = fintype.card n ∧ (leading_coeff (char_polynomial M)) = 1 :=
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
{ unfold char_polynomial,
  -- n_1 is nonempty so we can get some row index i
  let i : n_1 := classical.choice (fintype.card_pos_iff.mp (eq.symm h ▸ nat.succ_pos n)),
  rw [cofactor_expansion _ i, ←insert_erase (mem_univ i), sum_insert (not_mem_erase i _), add_comm],
  have hs : ↑(nat.succ n) =
    degree
      ((diagonal (λ (_x : n_1), X) - λ (i j : n_1), C (M i j)) i i *
         cofactor i i (diagonal (λ (_x : n_1), X) - λ (i j : n_1), C (M i j))),
    { rw [degree_mul_eq], dsimp, rw [diagonal_val_eq, ←sub_eq_add_neg, degree_X_sub_C, add_comm],
      rw [nat.succ_eq_add_one, with_bot.coe_add, with_bot.coe_one],
      congr,
      rw [←sub_eq_add_neg, cofactor_aux, ih],
      rw [←nat.pred_succ n, ←h, ←@card_univ n_1, ←card_erase_of_mem (mem_univ i)],
      refine fintype.card_of_subtype _ (λ _, by simp only [mem_erase, mem_univ, iff_self, and_true]) },
  convert degree_add_eq_of_degree_lt _,
  rw [←hs],
  have : ∀ (m : with_bot ℕ) (n : ℕ), m ≤ n → m < nat.succ n,
    { intros m n h, refine lt_of_le_of_lt h _, rw [with_bot.coe_lt_coe], exact nat.lt_succ_self _ },
  refine this _ _ (le_trans (degree_sum_le _ _) (sup_le _)),
  intros j hj,
  rw [degree_mul_eq, diagonal],
  dsimp,
  rw [if_neg (ne_of_mem_erase hj), zero_add, degree_neg, ←zero_add ↑n],
  refine add_le_add' _ _,
  { by_cases h0 : M j i = 0, { rw [h0, C_0, degree_zero], exact lattice.bot_le }, { rw [degree_C h0], exact le_refl 0 } },
  { unfold cofactor,
    rw [degree_mul_eq, equiv.perm.sign_swap (ne.symm $ ne_of_mem_erase hj)], simp,
    rw [show (n : with_bot ℕ) = ↑(fintype.card {k // k ≠ i} * 1),
      { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card,
          h, nat.pred_succ, mul_one], intro, simp only [mem_erase, mem_univ, and_true] }],
    refine degree_det_le _,
    intros k l,
    change degree ((ite (equiv.swap i j k.val = l.val) X 0) + -C (M (equiv.swap i j k.val) l.val)) ≤ 1,
    split_ifs with h h,
    { rw [←sub_eq_add_neg, degree_X_sub_C], exact le_refl 1 },
    { rw [zero_add, degree_neg],
      by_cases h0 : M (equiv.swap i j k.val) l.val = 0,
      { rw [h0, C_0, degree_zero], exact lattice.bot_le },
      { rw [degree_C h0, ←with_bot.coe_zero, ←with_bot.coe_one, with_bot.coe_le_coe], exact zero_le_one } } } }
end

--TODO: (re)move
/-instance with_bot.coe_is_add_monoid_hom : is_add_monoid_hom (λ n : ℕ, (n : with_bot ℕ)) :=
{ map_zero := with_bot.coe_zero,
  map_add := with_bot.coe_add }

--TODO: move
lemma with_bot.coe_sum {ι : Type*} (s : finset ι) (f : ι → ℕ) :
  (↑(s.sum f) : with_bot ℕ) = s.sum (λ x, ↑(f x)) :=
eq.symm $ sum_hom (λ n : ℕ, (n : with_bot ℕ))

lemma degree_prod {ι : Type*} [decidable_eq ι] (s : finset ι) (f : ι → polynomial α) :
  degree (s.prod f) = s.sum (λ i, degree (f i)) :=
finset.induction_on s
  (by { rw [sum_empty, prod_empty, degree_one] })
  (by { intros i s hs h, rw [sum_insert hs, prod_insert hs, degree_mul_eq, h] })

lemma degree_det_le {M : matrix n n (polynomial α)} {b : ℕ} (hM : ∀ i j, degree (M i j) ≤ b) :
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
end

lemma degree_monomial_le_aux (i j : n) (a : α) : degree (ite (i = j) X 0 + -C a) ≤ 1 :=
begin
  split_ifs,
  { rw [←sub_eq_add_neg, degree_X_sub_C], exact le_refl _ },
  { rw [zero_add, degree_neg], refine le_trans degree_C_le _,
    rw [←with_bot.coe_one, ←with_bot.coe_zero, with_bot.coe_le_coe], exact zero_le_one }
end

/-- The characteristic polynomial of `M` has degree ≤ n. -/
lemma degree_le : degree (char_polynomial M) ≤ fintype.card n :=
by { rw [←mul_one (fintype.card n)], exact degree_det_le (λ _ _, degree_monomial_le_aux _ _ _) }

lemma degree_lt_aux {p : equiv.perm n} {s : finset n} {j : n} (hj : j ∈ s) (hp : p j ≠ j) :
  degree (s.prod (λ i, diagonal (λ _:n, X) (p i) i + -C (M (p i) i))) < s.card :=
begin
  rw [←insert_erase hj, prod_insert (not_mem_erase _ _), degree_mul_eq, diagonal],
  dsimp,
  rw [if_neg hp, zero_add, degree_neg],
  by_cases hMj : M (p j) j = 0,
  { rw [hMj, C_0, degree_zero, with_bot.bot_add], exact with_bot.bot_lt_coe _ },
  { rw [degree_C hMj, zero_add, degree_prod],
    refine lt_of_le_of_lt (sum_le_sum (λ i _, show degree (ite (p i = i) X 0 + -C (M (p i) i)) ≤ 1, from _)) _,
    { exact degree_monomial_le_aux _ _ _ },
    { rw [sum_const, add_monoid.smul_one _, card_insert_of_not_mem (not_mem_erase _ _),
        ←nat.eq_cast _ with_bot.coe_zero with_bot.coe_one with_bot.coe_add _, with_bot.coe_lt_coe],
      exact nat.lt_succ_self _ } }
end-/

--TODO: move
instance leading_coeff_is_monoid_hom [integral_domain α] :
  is_monoid_hom (leading_coeff : polynomial α → α) :=
{ map_mul := leading_coeff_mul,
  map_one := leading_coeff_one }

lemma coeff_diagonal_aux {s : finset n} (hs : s.card > 0) :
  coeff (s.prod (λ i, diagonal (λ _:n, X) (equiv.refl n i) i + -C (M (equiv.refl n i) i))) s.card = 1 :=
suffices h : leading_coeff (s.prod (λ i, diagonal (λ _:n, X) (equiv.refl n i) i - C (M (equiv.refl n i) i))) = 1,
{ unfold leading_coeff at h,
  convert h,
  rw [←with_bot.coe_eq_coe, ←degree_eq_nat_degree],
  { rw [nat.eq_cast _ with_bot.coe_zero with_bot.coe_one with_bot.coe_add,
      ←add_monoid.smul_one s.card, ←sum_const],
    simp only [degree_prod, equiv.refl_apply, diagonal, if_pos rfl, degree_X_sub_C] },
  { rw [ne.def, prod_eq_zero_iff, not_exists], intro j, rw [not_exists], intro hj,
    dsimp [diagonal], rw [if_pos rfl, ←sub_eq_add_neg, ←degree_eq_bot, degree_X_sub_C],
    exact dec_trivial } },
begin
  rw [←prod_hom leading_coeff, ←@prod_const_one _ _ s, diagonal],
  congr,
  funext j,
  dsimp,
  rw [if_pos rfl, ←sub_eq_add_neg],
  exact monic_X_sub_C _,
  apply_instance
end

/-- The n-th coefficient (which is the leading coefficient) of `M` is 1. -/
/-lemma coeff_n (hn : fintype.card n > 0) : coeff (char_polynomial M) (fintype.card n) = 1 :=
begin
  unfold char_polynomial det,
  rw [finset_sum_coeff],
  rw [←show univ.sum (λ i, ite (equiv.refl n = i) (1:α) 0) = 1,
    { rw [←sum_subset (subset_univ (finset.singleton (equiv.refl n))) _],
      { convert sum_singleton, rw [if_pos rfl] },
      { intros _ _ h, rw [mem_singleton] at h, rw [if_neg $ ne.symm h], } }],
  congr,
  ext p,
  rw [int_cast_eq_C, coeff_C_mul],
  dsimp,
  split_ifs,
  { unfold fintype.card,
    rw [←h, coeff_diagonal_aux M hn, equiv.perm.sign_refl, mul_one, units.coe_one, int.cast_one] },
  { unfold fintype.card,
    have : ∃ j : n, p j ≠ (equiv.refl n) j, from (classical.not_forall.mp (λ hn, (ne.symm h) (equiv.ext _ _ hn))),
    cases this with j hj,
    rw [coeff_eq_zero_of_degree_lt (degree_lt_aux M (mem_univ j) hj), mul_zero] }
end

/-- The characteristic polynomial of `M` has degree the cardinality of n. -/
lemma degree (hn : fintype.card n > 0) : degree (char_polynomial M) = fintype.card n :=
le_antisymm (degree_le _)
  (le_of_not_gt (λ h, one_ne_zero $ begin
    rw [←coeff_n M hn],
    apply coeff_eq_zero_of_degree_lt,
    assumption end))
-/

/-- The characteristic polynomial of `M` is nonzero. -/
lemma ne_zero (hn : fintype.card n > 0) : char_polynomial M ≠ 0 :=
begin
  apply ne_zero_of_degree_gt,
  rw [degree M hn, with_bot.coe_lt_coe],
  exact nat.pred_lt (nat.pos_iff_ne_zero.mp hn)
end

/-- The characteristic polynomial of `M` is monic. -/
lemma monic (hn : fintype.card n > 0) : monic (char_polynomial M) :=
begin
  show coeff (char_polynomial M) (nat_degree (char_polynomial M)) = 1,
  convert coeff_n M hn,
  rw [←with_bot.coe_eq_coe, ←degree_eq_nat_degree (ne_zero M hn)],
  exact degree M hn
end

end characteristic_polynomial
