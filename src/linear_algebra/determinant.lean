/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen
-/
import data.matrix.pequiv
import data.fintype.card
import group_theory.perm.sign

universes u v
open equiv equiv.perm finset function

namespace matrix
open_locale matrix big_operators

variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

local notation `ε` σ:max := ((sign σ : ℤ ) : R)

/-- The determinant of a matrix given by the Leibniz formula. -/
definition det (M : matrix n n R) : R :=
∑ σ : perm n, ε σ * ∏ i, M (σ i) i

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i :=
begin
  refine (finset.sum_eq_single 1 _ _).trans _,
  { intros σ h1 h2,
    cases not_forall.1 (mt equiv.ext h2) with x h3,
    convert mul_zero _,
    apply finset.prod_eq_zero,
    { change x ∈ _, simp },
    exact if_neg h3 },
  { simp },
  { simp }
end

@[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = 0 :=
by rw [← diagonal_zero, det_diagonal, finset.prod_const, ← fintype.card,
  zero_pow (fintype.card_pos_iff.2 h)]

@[simp] lemma det_one : det (1 : matrix n n R) = 1 :=
by rw [← diagonal_one]; simp [-diagonal_one]

lemma det_eq_one_of_card_eq_zero {A : matrix n n R} (h : fintype.card n = 0) : det A = 1 :=
begin
  have perm_eq : (univ : finset (perm n)) = {1} :=
  univ_eq_singleton_of_card_one (1 : perm n) (by simp [card_univ, fintype.card_perm, h]),
  simp [det, card_eq_zero.mp h, perm_eq],
end

lemma det_mul_aux {M N : matrix n n R} {p : n → n} (H : ¬bijective p) :
  ∑ σ : perm n, (ε σ) * ∏ x, (M (σ x) (p x) * N (p x) x) = 0 :=
begin
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j,
  { rw [← fintype.injective_iff_bijective, injective] at H,
    push_neg at H,
    exact H },
  exact sum_involution
    (λ σ _, σ * swap i j)
    (λ σ _,
      have ∀ a, p (swap i j a) = p a := λ a, by simp only [swap_apply_def]; split_ifs; cc,
      have ∏ x, M (σ x) (p x) = ∏ x, M ((σ * swap i j) x) (p x),
        from prod_bij (λ a _, swap i j a) (λ _ _, mem_univ _) (by simp [this])
          (λ _ _ _ _ h, (swap i j).injective h)
          (λ b _, ⟨swap i j b, mem_univ _, by simp⟩),
      by simp [sign_mul, this, sign_swap hij, prod_mul_distrib])
    (λ σ _ _ h, hij (σ.injective $ by conv {to_lhs, rw ← h}; simp))
    (λ _ _, mem_univ _)
    (λ _ _, equiv.ext $ by simp)
end

@[simp] lemma det_mul (M N : matrix n n R) : det (M ⬝ N) = det M * det N :=
calc det (M ⬝ N) = ∑ p : n → n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  by simp only [det, mul_val, prod_univ_sum, mul_sum,
    fintype.pi_finset_univ]; rw [finset.sum_comm]
... = ∑ p in (@univ (n → n) _).filter bijective, ∑ σ : perm n,
    ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  eq.symm $ sum_subset (filter_subset _)
    (λ f _ hbij, det_mul_aux $ by simpa using hbij)
... = ∑ τ : perm n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (τ i) * N (τ i) i) :
  sum_bij (λ p h, equiv.of_bijective p (mem_filter.1 h).2) (λ _ _, mem_univ _)
    (λ _ _, rfl) (λ _ _ _ _ h, by injection h)
    (λ b _, ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩)
... = ∑ σ : perm n, ∑ τ : perm n, (∏ i, N (σ i) i) * ε τ * (∏ j, M (τ j) (σ j)) :
  by simp [mul_sum, det, mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
... = ∑ σ : perm n, ∑ τ : perm n, (((∏ i, N (σ i) i) * (ε σ * ε τ)) * ∏ i, M (τ i) i) :
  sum_congr rfl (λ σ _, sum_bij (λ τ _, τ * σ⁻¹) (λ _ _, mem_univ _)
    (λ τ _,
      have ∏ j, M (τ j) (σ j) = ∏ j, M ((τ * σ⁻¹) j) j,
        by rw ← finset.prod_equiv σ⁻¹; simp [mul_apply],
      have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
        calc ε σ * ε (τ * σ⁻¹) = ε ((τ * σ⁻¹) * σ) :
          by rw [mul_comm, sign_mul (τ * σ⁻¹)]; simp [sign_mul]
        ... = ε τ : by simp,
      by rw h; simp [this, mul_comm, mul_assoc, mul_left_comm])
    (λ _ _ _ _, mul_right_cancel) (λ τ _, ⟨τ * σ, by simp⟩))
... = det M * det N : by simp [det, mul_assoc, mul_sum, mul_comm, mul_left_comm]

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

/-- Transposing a matrix preserves the determinant. -/
@[simp] lemma det_transpose (M : matrix n n R) : Mᵀ.det = M.det :=
begin
  apply sum_bij (λ σ _, σ⁻¹),
  { intros σ _, apply mem_univ },
  { intros σ _,
    rw [sign_inv],
    congr' 1,
    apply prod_bij (λ i _, σ i),
    { intros i _, apply mem_univ },
    { intros i _, simp },
    { intros i j _ _ h, simp at h, assumption },
    { intros i _, use σ⁻¹ i, finish } },
  { intros σ σ' _ _ h, simp at h, assumption },
  { intros σ _, use σ⁻¹, finish }
end

/-- The determinant of a permutation matrix equals its sign. -/
@[simp] lemma det_permutation (σ : perm n) :
  matrix.det (σ.to_pequiv.to_matrix : matrix n n R) = σ.sign := begin
  suffices : matrix.det (σ.to_pequiv.to_matrix) = ↑σ.sign * det (1 : matrix n n R), { simp [this] },
  unfold det,
  rw mul_sum,
  apply sum_bij (λ τ _, σ * τ),
  { intros τ _, apply mem_univ },
  { intros τ _,
    conv_lhs { rw [←one_mul (sign τ), ←int.units_pow_two (sign σ)] },
    conv_rhs { rw [←mul_assoc, coe_coe, sign_mul, units.coe_mul, int.cast_mul, ←mul_assoc] },
    congr,
    { simp [pow_two] },
    { ext i, apply pequiv.equiv_to_pequiv_to_matrix } },
  { intros τ τ' _ _, exact (mul_right_inj σ).mp },
  { intros τ _, use σ⁻¹ * τ, use (mem_univ _), exact (mul_inv_cancel_left _ _).symm }
end

/-- Permuting the columns changes the sign of the determinant. -/
lemma det_permute (σ : perm n) (M : matrix n n R) : matrix.det (λ i, M (σ i)) = σ.sign * M.det :=
by rw [←det_permutation, ←det_mul, pequiv.to_pequiv_mul_matrix]

@[simp] lemma det_smul {A : matrix n n R} {c : R} : det (c • A) = c ^ fintype.card n * det A :=
calc det (c • A) = det (matrix.mul (diagonal (λ _, c)) A) : by rw [smul_eq_diagonal_mul]
             ... = det (diagonal (λ _, c)) * det A        : det_mul _ _
             ... = c ^ fintype.card n * det A             : by simp [card_univ]

section det_zero
/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/

lemma det_eq_zero_of_column_eq_zero {A : matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
begin
  rw [←det_transpose, det],
  convert @sum_const_zero _ _ (univ : finset (perm n)) _,
  ext σ,
  convert mul_zero ↑(sign σ),
  apply prod_eq_zero (mem_univ i),
  rw [transpose_val],
  apply h
end

/--
  `mod_swap i j` contains permutations up to swapping `i` and `j`.

  We use this to partition permutations in the expression for the determinant,
  such that each partitions sums up to `0`.
-/
def mod_swap {n : Type u} [decidable_eq n] (i j : n) : setoid (perm n) :=
⟨ λ σ τ, σ = τ ∨ σ = swap i j * τ,
  λ σ, or.inl (refl σ),
  λ σ τ h, or.cases_on h (λ h, or.inl h.symm) (λ h, or.inr (by rw [h, swap_mul_self_mul])),
  λ σ τ υ hστ hτυ, by cases hστ; cases hτυ; try {rw [hστ, hτυ, swap_mul_self_mul]}; finish⟩

instance (i j : n) : decidable_rel (mod_swap i j).r := λ σ τ, or.decidable

variables {M : matrix n n R} {i j : n}

/-- If a matrix has a repeated column, the determinant will be zero. -/
theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
begin
  have swap_invariant : ∀ k, M (swap i j k) = M k,
  { intros k,
    rw [swap_apply_def],
    by_cases k = i, { rw [if_pos h, h, ←hij] },
    rw [if_neg h],
    by_cases k = j, { rw [if_pos h, h, hij] },
    rw [if_neg h] },

  have : ∀ σ, _root_.disjoint {σ} {swap i j * σ},
  { intros σ,
    rw [disjoint_singleton, mem_singleton],
    exact (not_congr swap_mul_eq_iff).mpr i_ne_j },

  apply finset.sum_cancels_of_partition_cancels (mod_swap i j),
  intros σ _,
  erw [filter_or, filter_eq', filter_eq', if_pos (mem_univ σ), if_pos (mem_univ (swap i j * σ)),
    sum_union (this σ), sum_singleton, sum_singleton],
  convert add_right_neg (↑↑(sign σ) * ∏ i, M (σ i) i),
  rw [neg_mul_eq_neg_mul],
  congr,
  { rw [sign_mul, sign_swap i_ne_j], norm_num },
  ext j, rw [mul_apply, swap_invariant]
end

end det_zero

end matrix
