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

lemma degree_char_matrix_diag [nonzero_comm_ring α] (i : n) : degree (char_matrix M i i) = 1 :=
by { rw [char_matrix_apply, if_pos rfl, degree_X_sub_C] }

lemma degree_char_matrix [comm_ring α] {i j : n} (h : i ≠ j) : degree (char_matrix M i j) ≤ 0 :=
by { rw [char_matrix_apply, if_neg h, degree_neg], exact degree_C_le }

lemma degree_char_matrix_le [nonzero_comm_ring α] (i j : n) : degree (char_matrix M i j) ≤ 1 :=
classical.by_cases
  (λ h : i = j, h ▸ le_of_eq (degree_char_matrix_diag M i))
  (λ h, le_trans (degree_char_matrix M h)
    (by { rw [←with_bot.coe_zero, ←with_bot.coe_one, with_bot.coe_le_coe], exact zero_le_one }))

/-- The evaluation of the characteristic polynomial of `M` at `b` is equal to `det (Iₙb - M)`.-/
lemma eval [comm_ring α] (b : α) : eval b (char_polynomial M) = det (diagonal (λ _, b) - M) :=
begin
  change (λ p : polynomial α, eval b p) (det (diagonal (λ _:n, X) - λ (i j : n), C (M i j))) = _,
  rw [det_map_hom (λ p : polynomial α, eval b p)],
  congr, ext, dsimp [diagonal],
  split_ifs,
  rw [eval_add, eval_X, eval_neg, eval_C],
  rw [eval_add, eval_zero, eval_neg, eval_C]
end

/-- The constant coefficient of the characteristic polynomial of `M` is `±det M`. -/
lemma constant_coeff [comm_ring α] : coeff (char_polynomial M) 0 = (-1) ^ fintype.card n * det M :=
by rw [coeff_zero_eq_eval_zero, eval, diagonal_zero, zero_sub, det_neg]

--TODO: move
lemma degree_prod [integral_domain α] {ι : Type*} [decidable_eq ι] (s : finset ι) (f : ι → polynomial α) :
  degree (s.prod f) = s.sum (λ i, degree (f i)) :=
finset.induction_on s
  (by { rw [prod_empty, sum_empty, degree_one] })
  (λ _ _ hs h, by { rw [sum_insert hs, prod_insert hs, degree_mul_eq, h] })

--TODO: move
instance with_bot.is_add_monoid_hom {α : Type u} [add_monoid α] : is_add_monoid_hom (coe : α → with_bot α) :=
{ map_zero := with_bot.coe_zero, map_add := with_bot.coe_add }

variable [integral_domain α]

lemma degree_det_le {M : matrix n n (polynomial α)} {b : ℕ} (hM : ∀ i j, degree (M i j) ≤ b) :
  degree (det M) ≤ ↑(fintype.card n * b) :=
begin
  refine le_trans (degree_sum_le _ _) (sup_le (λ p hp, _)),
  rw [degree_mul_eq],
  rw [show degree ↑(equiv.perm.sign p : ℤ) = 0, from @degree_eq_zero_of_is_unit α _ _ (is_unit_of_mul_one _ _
    (by {rw [←int.cast_mul, ←units.coe_mul, ←pow_two, int.units_pow_two, units.coe_one, int.cast_one]}))],
  rw [zero_add, ←nat.cast_id (fintype.card n), ←add_monoid.smul_eq_mul, fintype.card, ←sum_const,
    degree_prod, ←sum_hom coe],
  exact sum_le_sum (λ _ _, hM _ _),
  convert with_bot.is_add_monoid_hom,
  sorry
end

lemma degree_aux (i : n) (hn : fintype.card n ≠ 0) :
  degree ((erase univ i).sum (λ j, char_matrix M i j * cofactor i j (char_matrix M))) < fintype.card n :=
begin
  have : (nat.pred $ fintype.card n : with_bot ℕ) < (fintype.card n),
    from with_bot.coe_lt_coe.mpr (nat.pred_lt hn),
  refine lt_of_le_of_lt (degree_sum_le _ _) (lt_of_le_of_lt (sup_le (λ j hji, _)) this),
  rw [mem_erase] at hji,
  rw [degree_mul_eq, ←zero_add (coe _)],
  refine add_le_add' (degree_char_matrix M hji.1.symm) _,
  rw [cofactor, degree_mul_eq, equiv.perm.sign_swap (ne.symm hji.1), units.coe_neg, int.cast_neg,
    degree_neg, units.coe_one, int.cast_one, degree_one, zero_add],
  convert degree_det_le (λ k l, (_ : _ ≤ ↑1)),
  { rw [fintype.card_of_subtype (erase univ j), card_erase_of_mem (mem_univ j), ←fintype.card, mul_one],
      intro, simp only [mem_erase, mem_univ, and_true] }, apply_instance,
  change degree (char_matrix M (equiv.swap i j k.val) l.val) ≤ 1,
  exact degree_char_matrix_le M _ _
end

lemma cofactor_diag_apply (i : n) : cofactor i i (char_matrix M) =
  char_polynomial (minor M (equiv.swap i i ∘ subtype.val) (subtype.val :  {k // k ≠ i} → n)) :=
by { unfold cofactor,
  rw [equiv.swap_self, equiv.perm.sign_refl, units.coe_one, int.cast_one, one_mul],
  congr, unfold minor, ext,
  finish [char_matrix_apply, subtype.ext] }

--TODO: move
instance ulift.add_monoid {β : Type w} [add_monoid β] : add_monoid (ulift β) :=
{ add := λ x y, ⟨x.down + y.down⟩,
  zero := ⟨0⟩,
  zero_add := λ x, ulift.ext _ _ (add_monoid.zero_add _),
  add_zero := λ x, ulift.ext _ _ (add_monoid.add_zero _),
  add_assoc := λ x y z, ulift.ext _ _ (add_monoid.add_assoc _ _ _) }

--TODO: move
lemma equiv.perm.empty (h0 : (univ : finset n) = ∅) :
  (univ : finset (equiv.perm n)) = finset.singleton 1 :=
finset.ext.2 (λ σ, ⟨λ _,
    by { rw [mem_singleton], ext i, exact absurd (by rw ←h0; exact mem_univ i) (not_mem_empty i) },
  λ _, mem_univ _⟩)

lemma char_polynomial_aux {β : Type w} [add_monoid β] (f : polynomial α → β)
  (hmul : ∀ p q, f (p * q) = f p + f q)
  (hadd : ∀ p q, degree q < degree p → f (q + p) = f p) :
  f (char_polynomial M) = f (X ^ fintype.card n) :=
begin
  unfreezeI,
  induction h : fintype.card n generalizing n β,
  { unfold char_polynomial det, congr,
    have h0 : (univ : finset n) = ∅, by { rwa [←card_eq_zero, card_univ] },
    rw [equiv.perm.empty h0, sum_singleton, equiv.perm.sign_one, h0, prod_empty, mul_one],
    exact nat.cast_one },
  { unfold char_polynomial,
    -- n_1 is nonempty so we can get some row index i
    let i : n_1 := classical.choice (fintype.card_pos_iff.mp (eq.symm h ▸ nat.succ_pos n)),
    rw [cofactor_expansion _ i, ←insert_erase (mem_univ i), sum_insert (not_mem_erase i _), add_comm],
    have : fintype.card {k // k ≠ i} = n,
    { rw [fintype.card_of_subtype (erase univ i), card_erase_of_mem (mem_univ i), ←fintype.card, h,
        nat.pred_succ], intro, simp only [mem_erase, mem_univ, and_true] },
    rw [hadd],
    { rw [pow_succ, hmul, hmul, char_matrix_apply, if_pos rfl, sub_eq_add_neg, add_comm, hadd,
        cofactor_diag_apply, ih _ f hmul hadd this],
      rw [degree_neg, degree_X],
      refine lt_of_le_of_lt degree_C_le _,
      rw [←with_bot.coe_one, ←with_bot.coe_zero, with_bot.coe_lt_coe],
      exact zero_lt_one },
    { rw [cofactor_diag_apply, degree_mul_eq, degree_char_matrix_diag],
      refine lt_of_lt_of_le (degree_aux _ _ _) (le_of_eq _), {rw [h], exact nat.succ_ne_zero _},
      rw [h, nat.succ_eq_add_one, with_bot.coe_add, with_bot.coe_one, add_comm], congr, symmetry,
      rw [←@degree_X_pow α _ n],
      refine ulift.up.inj.{w} (ih _ (ulift.up ∘ degree) _ _ this),
      finish [degree_mul_eq],
      finish using [degree_add_eq_of_degree_lt] } }
end

lemma char_polynomial_aux_mul {β : Type w} [monoid β] (f : polynomial α → β)
  (hmul : ∀ p q, f (p * q) = f p * f q)
  (hadd : ∀ p q, degree q < degree p → f (q + p) = f p) :
  f (char_polynomial M) = f (X ^ fintype.card n) :=
@char_polynomial_aux _ _ _ _ _ M _ (additive β) _ f hmul hadd


/-- The degree of the characteristic polynomial of `M` is equal to its dimension. -/
lemma degree : degree (char_polynomial M) = fintype.card n :=
by { rw [←@degree_X_pow α], exact char_polynomial_aux M degree (λ _ _, degree_mul_eq)
    (λ _ _, degree_add_eq_of_degree_lt) }

/-- The characteristic polynomial of `M` is monic. -/
lemma monic : leading_coeff (char_polynomial M) = 1 :=
by { rw [←leading_coeff_X_pow (fintype.card n)], exact char_polynomial_aux_mul M leading_coeff
  leading_coeff_mul (λ _ _, leading_coeff_add_of_degree_lt) }

/-- The characteristic polynomial of `M` is nonzero. -/
lemma ne_zero (hn : fintype.card n > 0) : char_polynomial M ≠ 0 :=
ne_zero_of_degree_gt $ begin
  rw [degree M, with_bot.coe_lt_coe],
  exact nat.pred_lt (nat.pos_iff_ne_zero.mp hn)
end

end characteristic_polynomial
