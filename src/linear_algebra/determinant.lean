/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import data.matrix.basic
import group_theory.perm.sign
import algebra.char_p

universes u v
open equiv equiv.perm finset function

namespace matrix

variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

local notation `ε` σ:max := ((sign σ : ℤ ) : R)

definition det (M : matrix n n R) : R :=
univ.sum (λ (σ : perm n), ε σ * univ.prod (λ i, M (σ i) i))

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = univ.prod d :=
begin
  refine (finset.sum_eq_single 1 _ _).trans _,
  { intros σ h1 h2,
    cases not_forall.1 (mt (equiv.ext _ _) h2) with x h3,
    convert ring.mul_zero _,
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

lemma det_mul_aux {M N : matrix n n R} {p : n → n} (H : ¬bijective p) :
  univ.sum (λ σ : perm n, (ε σ) * (univ.prod (λ x, M (σ x) (p x) * N (p x) x))) = 0 :=
begin
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j,
  { rw [← fintype.injective_iff_bijective, injective] at H,
    push_neg at H,
    exact H },
  exact sum_involution
    (λ σ _, σ * swap i j)
    (λ σ _,
      have ∀ a, p (swap i j a) = p a := λ a, by simp only [swap_apply_def]; split_ifs; cc,
      have univ.prod (λ x, M (σ x) (p x)) = univ.prod (λ x, M ((σ * swap i j) x) (p x)),
        from prod_bij (λ a _, swap i j a) (λ _ _, mem_univ _) (by simp [this])
          (λ _ _ _ _ h, (swap i j).injective h)
          (λ b _, ⟨swap i j b, mem_univ _, by simp⟩),
      by simp [sign_mul, this, sign_swap hij, prod_mul_distrib])
    (λ σ _ _ h, hij (σ.injective $ by conv {to_lhs, rw ← h}; simp))
    (λ _ _, mem_univ _)
    (λ _ _, equiv.ext _ _ $ by simp)
end

@[simp] lemma det_mul (M N : matrix n n R) : det (M * N) = det M * det N :=
calc det (M * N) = univ.sum (λ σ : perm n, (univ.pi (λ a, univ)).sum
    (λ (p : Π (a : n), a ∈ univ → n), ε σ *
    univ.attach.prod (λ i, M (σ i.1) (p i.1 (mem_univ _)) * N (p i.1 (mem_univ _)) i.1))) :
  by simp only [det, mul_val', prod_sum, mul_sum]
... = univ.sum (λ σ : perm n, univ.sum
    (λ p : n → n, ε σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  sum_congr rfl (λ σ _, sum_bij
    (λ f h i, f i (mem_univ _)) (λ _ _, mem_univ _)
    (by simp) (by simp [funext_iff]) (λ b _, ⟨λ i hi, b i, by simp⟩))
... = univ.sum (λ p : n → n, univ.sum
    (λ σ : perm n, ε σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  finset.sum_comm
... = ((@univ (n → n) _).filter bijective).sum (λ p : n → n, univ.sum
    (λ σ : perm n, ε σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  eq.symm $ sum_subset (filter_subset _) 
    (λ f _ hbij, det_mul_aux $ by simpa using hbij)
... = (@univ (perm n) _).sum (λ τ, univ.sum
    (λ σ : perm n, ε σ * univ.prod (λ i, M (σ i) (τ i) * N (τ i) i))) :
  sum_bij (λ p h, equiv.of_bijective (mem_filter.1 h).2) (λ _ _, mem_univ _)
    (λ _ _, rfl) (λ _ _ _ _ h, by injection h)
    (λ b _, ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, eq_of_to_fun_eq rfl⟩)
... = univ.sum (λ σ : perm n, univ.sum (λ τ : perm n,
    (univ.prod (λ i, N (σ i) i) * ε τ) * univ.prod (λ j, M (τ j) (σ j)))) :
  by simp [mul_sum, det, mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
... = univ.sum (λ σ : perm n, univ.sum (λ τ : perm n,
    (univ.prod (λ i, N (σ i) i) * (ε σ * ε τ)) *
    univ.prod (λ i, M (τ i) i))) :
  sum_congr rfl (λ σ _, sum_bij (λ τ _, τ * σ⁻¹) (λ _ _, mem_univ _)
    (λ τ _,
      have univ.prod (λ j, M (τ j) (σ j)) = univ.prod (λ j, M ((τ * σ⁻¹) j) j),
        by rw prod_univ_perm σ⁻¹; simp [mul_apply],
      have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
        calc ε σ * ε (τ * σ⁻¹) = ε ((τ * σ⁻¹) * σ) :
          by rw [mul_comm, sign_mul (τ * σ⁻¹)]; simp [sign_mul]
        ... = ε τ : by simp,
      by rw h; simp [this, mul_comm, mul_assoc, mul_left_comm])
    (λ _ _ _ _, (mul_right_inj _).1) (λ τ _, ⟨τ * σ, by simp⟩))
... = det M * det N : by simp [det, mul_assoc, mul_sum, mul_comm, mul_left_comm]

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

/-- Transposing a matrix preserves the determinant. -/
@[simp] lemma det_transpose (M : matrix n n R) : M.transpose.det = M.det :=
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
  { intros i _, use σ⁻¹ i, finish }
},
{ intros σ σ' _ _ h, simp at h, assumption },
{ intros σ _, use σ⁻¹, finish }
end

/-- Permuting the columns changes the sign of the determinant. -/
lemma det_permute (M : matrix n n R) (σ : perm n) : matrix.det (λ i, M (σ i)) = σ.sign * M.det :=
begin
unfold det,
rw mul_sum,
apply sum_bij (λ τ _, σ * τ),
{ intros τ _, apply mem_univ },
{ intros τ _,
  show
    ↑(sign τ) * finset.prod univ (λ i, M (σ.to_fun (τ.to_fun i)) i)
    = ↑(sign σ) * (↑(sign (σ * τ)) * finset.prod univ (λ i, M (σ.to_fun (τ.to_fun i)) i)),
  rw ←mul_assoc,
  congr,
  calc ε τ
       = ↑(sign σ * sign σ * sign τ) :
    by {conv_lhs {rw [←one_mul (sign τ), ←int.units_pow_two (sign σ)]}, norm_num}
  ... = ε σ * ε (σ * τ) :
    by simp only [mul_assoc, int.cast_mul, sign_mul, coe_coe, units.coe_mul] },
{ intros τ τ' _ _, exact (mul_left_inj σ).mp },
{ intros τ _, use σ⁻¹ * τ, use (mem_univ _), exact (mul_inv_cancel_left _ _).symm }
end

/-- The determinant is zero if the matrix contains a repeated column.

The proof shows `M.det = -M.det` and concludes `M.det = 0`,
so it doesn't work in characteristic `2`.
-/
lemma det_zero_of_column_eq_of_char_ne_two (char_ne_2 : ∀ (a : R), a = -a → a = 0)
{M : matrix n n R} {i j : n} (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
begin
suffices : M.det = - M.det, { apply char_ne_2, assumption },
have : (λ a, M (swap i j a)) = M,
{ ext a b,
  by_cases hi : a = i, { rw [hi, swap_apply_left, hij] },
  by_cases hj : a = j, { rw [hj, swap_apply_right, hij] },
  rw [swap_apply_of_ne_of_ne hi hj]
},
calc M.det = (-1 : units ℤ) * M.det : by rw [←sign_swap i_ne_j, ←det_permute M, this]
       ... = -det M : by norm_num
end

/-- 
  Helper function for `det_zero_of_column_eq_of_has_lt`:
  identifies two permutations that differ by a `swap i j` by mapping them to the same value.
-/
def identify_swaps [has_lt n] [decidable_rel ((<) : n → n → Prop)] (i j : n) (σ : perm n) : perm n :=
if σ⁻¹ i > σ⁻¹ j then swap i j * σ else σ

lemma identify_swaps_iff_aux [has_lt n] [decidable_rel ((<) : n → n → Prop)] {i j : n} {σ τ : perm n}
  (h : identify_swaps i j τ = identify_swaps i j σ) : τ = σ ∨ τ = swap i j * σ :=
begin
  unfold identify_swaps at h,
  by_cases hσ : σ⁻¹ i > σ⁻¹ j;
  try {rw [if_pos hσ] at h}; try {rw [if_neg hσ] at h};
  by_cases hτ : τ⁻¹ i > τ⁻¹ j;
  try {rw [if_pos hτ] at h}; try {rw [if_neg hτ] at h};
  try {finish},
  apply or.inr, rw [←h, swap_mul_self_mul]
end

lemma identify_swaps_iff [decidable_linear_order n] {i j : n} (σ τ : perm n)
  (i_ne_j : i ≠ j) : (identify_swaps i j τ = identify_swaps i j σ) ↔ (τ = σ ∨ τ = swap i j * σ) :=
begin
  split,
  { apply identify_swaps_iff_aux },
  { intros h, cases h; rw [h],
    unfold identify_swaps,
    have σswap_i : (σ⁻¹ * swap i j) i = σ⁻¹ j := by simp,
    have σswap_j : (σ⁻¹ * swap i j) j = σ⁻¹ i := by simp,
    rw [mul_inv_rev, swap_inv, σswap_i, σswap_j],
    by_cases σ⁻¹ i > σ⁻¹ j,
    { have : ¬(σ⁻¹ j > σ⁻¹ i) := assume i_lt_j, lt_asymm h i_lt_j, 
      rw [if_pos h, if_neg this] },
    { have : σ⁻¹ i ≠ σ⁻¹ j := assume eq, i_ne_j (injective_of_left_inverse σ.4 eq),
      have : σ⁻¹ j > σ⁻¹ i := lt_of_le_of_ne (le_of_not_lt h) this,
      rw [if_neg h, if_pos this, swap_mul_self_mul] },
  },
end

/--
  A version of `det_zero_of_column_eq_of_char_ne_two`
  which replaces the assumption on the ring `α` with one on the index set `n`.

  TODO: can we get rid of the `[decidable_linear_order n]` assumption,
  by choosing an arbitrary order (which should work because `n` is finite)?
-/
lemma det_zero_of_column_eq_of_lin [decidable_linear_order n]
  {M : matrix n n R} {i j : n} (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
begin
have swap_invariant : ∀ k l, M (swap i j k) l = M k l,
{ intros k l,
  rw [swap_apply_def],
  by_cases k = i, { rw [if_pos h, h, ←hij] },
  rw [if_neg h],
  by_cases k = j, { rw [if_pos h, h, hij] },
  rw [if_neg h] },

suffices : sum (univ.image (identify_swaps i j))
             (λ (σ : perm n),
                ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
                ε (swap i j * σ) * univ.prod (λ (k : n), M ((swap i j * σ).to_fun k) k)) =
           sum univ (λ (σ : perm n), ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k)),
{ calc det M
    = sum (univ.image (identify_swaps i j)) (λ (σ : perm n),
      ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
      ε (swap i j * σ) * univ.prod (λ (k : n), M ((swap i j * σ).to_fun k) k)) : symm this
... = sum (univ.image (identify_swaps i j)) (λ (σ : perm n),
      ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
      ε (swap i j * σ) * univ.prod (λ (k : n), M (swap i j (σ.to_fun k)) k)) : rfl
... = sum (univ.image (identify_swaps i j)) (λ (σ : perm n),
      ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
      -1 * ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k)) :
  by { congr, ext σ, congr,
    { rw [sign_mul, sign_swap i_ne_j], norm_cast },
    ext k, apply swap_invariant }
... = sum (univ.image (identify_swaps i j)) (λ (σ : perm n), 0) : by { congr, ext σ, ring }
... = 0 : sum_const_zero },

apply sum_image',
intros σ _,
rw [@filter_congr _ (λ τ, identify_swaps i j τ = identify_swaps i j σ) _ _ _ _
  (λ τ _, identify_swaps_iff σ τ i_ne_j)],
have : swap i j * σ ∉ finset.singleton σ :=
  (not_congr (mem_singleton.trans (swap_mul_eq_iff σ))).mpr i_ne_j,
simp only [filter_or, filter_eq', if_pos (mem_univ _), insert_empty_eq_singleton,
           sum_union (disjoint_singleton.mpr this), sum_singleton],

by_cases σ⁻¹ i > σ⁻¹ j,
{ rw [identify_swaps, if_pos h, swap_mul_self_mul], ring },
{ rw [identify_swaps, if_neg h] }
end

end matrix
