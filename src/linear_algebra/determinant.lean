/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen
-/
import data.matrix.basic
import group_theory.perm.sign

universes u v
open equiv equiv.perm finset function

namespace matrix

variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

local notation `ε` σ:max := ((sign σ : ℤ ) : R)

/-- The determinant of a matrix given by the Leibniz formula. -/
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

section det_zero
/-! ### `det_zero` section

  Prove that a matrix with a repeated column has determinant equal to zero.
-/

/--
  `mod_swap i j` contains permutations up to swapping `i` and `j`.

  We use this to partition permutations in the expression for the determinant,
  such that each partitions sums up to `0`.
-/
def mod_swap {n : Type u} [decidable_eq n] (i j : n) : setoid (perm n) :=
⟨ λ σ τ, σ = τ ∨ σ = swap i j * τ
, λ σ, or.inl (refl σ)
, λ σ τ h, or.cases_on h
(λ h, or.inl h.symm)
(λ h, or.inr (by rw [h, swap_mul_self_mul]))
, λ σ τ υ hστ hτυ, by cases hστ; cases hτυ; try {rw [hστ, hτυ, swap_mul_self_mul]}; finish
⟩

instance (i j : n) : decidable_rel (mod_swap i j).r := λ σ τ, or.decidable

variables {M : matrix n n R} {i j : n} (i_ne_j : i ≠ j) (hij : M i = M j)

include i_ne_j hij
/-- If a matrix has a repeated column, the determinant will be zero. -/
theorem det_zero_of_column_eq : M.det = 0 :=
begin
have swap_invariant : ∀ k, M (swap i j k) = M k,
{ intros k,
  rw [swap_apply_def],
  by_cases k = i, { rw [if_pos h, h, ←hij] },
  rw [if_neg h],
  by_cases k = j, { rw [if_pos h, h, hij] },
  rw [if_neg h] },

have : ∀ σ, _root_.disjoint (_root_.singleton σ) (_root_.singleton (swap i j * σ)),
{ intros σ,
  rw [finset.singleton_eq_singleton, finset.singleton_eq_singleton, disjoint_singleton],
  apply (not_congr mem_singleton).mpr,
  exact (not_congr (swap_mul_eq_iff σ)).mpr i_ne_j },

apply @finset.sum_cancels_of_partition_cancels _ _ _ _ _ (mod_swap i j),
intros σ _,
erw [filter_or, filter_eq', filter_eq', if_pos (mem_univ σ), if_pos (mem_univ (swap i j * σ)),
  sum_union (this σ), sum_singleton, sum_singleton],
convert add_right_neg (↑↑(sign σ) * finset.prod univ (λ (i : n), M (σ i) i)),
rw [neg_mul_eq_neg_mul],
congr,
{ rw [sign_mul, sign_swap i_ne_j], norm_num },
ext j, rw [mul_apply, swap_invariant]
end

end det_zero

end matrix
