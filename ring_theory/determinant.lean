/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import group_theory.subgroup group_theory.perm ring_theory.matrix

universes u v
open equiv equiv.perm finset function

namespace matrix

variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

definition det (M : matrix n n R) : R :=
univ.sum (λ (σ : perm n), sign σ * univ.prod (λ i, M (σ i) i))

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
  univ.sum (λ σ : perm n, (sign σ : R) * (univ.prod (λ x, M (σ x) (p x) * N (p x) x))) = 0 :=
let ⟨i, hi⟩ := classical.not_forall.1 (mt fintype.injective_iff_bijective.1 H) in
let ⟨j, hij'⟩ := classical.not_forall.1 hi in
have hij : p i = p j ∧ i ≠ j, from not_imp.1 hij',
sum_involution
  (λ σ _, σ * swap i j)
  (λ σ _,
    have ∀ a, p (swap i j a) = p a := λ a, by simp only [swap_apply_def]; split_ifs; cc,
    have univ.prod (λ x, M (σ x) (p x)) = univ.prod (λ x, M ((σ * swap i j) x) (p x)),
      from prod_bij (λ a _, swap i j a) (λ _ _, mem_univ _) (by simp [this])
        (λ _ _ _ _ h, (swap i j).bijective.1 h)
        (λ b _, ⟨swap i j b, mem_univ _, by simp⟩),
    by simp [sign_mul, this, sign_swap hij.2, prod_mul_distrib])
  (λ σ _ _ h, hij.2 (σ.bijective.1 $ by conv {to_lhs, rw ← h}; simp))
  (λ _ _, mem_univ _)
  (λ _ _, equiv.ext _ _ $ by simp)

@[simp] lemma det_mul (M N : matrix n n R) : det (M * N) = det M * det N :=
calc det (M * N) = univ.sum (λ σ : perm n, (univ.pi (λ a, univ)).sum
    (λ (p : Π (a : n), a ∈ univ → n), sign σ *
    univ.attach.prod (λ i, M (σ i.1) (p i.1 (mem_univ _)) * N (p i.1 (mem_univ _)) i.1))) :
  by simp only [det, mul_val', prod_sum, mul_sum]
... = univ.sum (λ σ : perm n, univ.sum
    (λ p : n → n, sign σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  sum_congr rfl (λ σ _, sum_bij
    (λ f h i, f i (mem_univ _)) (λ _ _, mem_univ _)
    (by simp) (by simp [funext_iff]) (λ b _, ⟨λ i hi, b i, by simp⟩))
... = univ.sum (λ p : n → n, univ.sum
    (λ σ : perm n, sign σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  finset.sum_comm
... = ((@univ (n → n) _).filter bijective ∪ univ.filter (λ p : n → n, ¬bijective p)).sum
    (λ p : n → n, univ.sum (λ σ : perm n, sign σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  finset.sum_congr (finset.ext.2 (by simp; tauto)) (λ _ _, rfl)
... = ((@univ (n → n) _).filter bijective).sum (λ p : n → n, univ.sum
    (λ σ : perm n, sign σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) +
    (univ.filter (λ p : n → n, ¬bijective p)).sum (λ p : n → n, univ.sum
    (λ σ : perm n, sign σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  finset.sum_union (by simp [finset.ext]; tauto)
... = ((@univ (n → n) _).filter bijective).sum (λ p : n → n, univ.sum
    (λ σ : perm n, sign σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) +
    (univ.filter (λ p : n → n, ¬bijective p)).sum (λ p, 0) :
  (add_left_inj _).2 (finset.sum_congr rfl $ λ p h, det_mul_aux (mem_filter.1 h).2)
... = ((@univ (n → n) _).filter bijective).sum (λ p : n → n, univ.sum
    (λ σ : perm n, sign σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) : by simp
... = (@univ (perm n) _).sum (λ τ, univ.sum
    (λ σ : perm n, sign σ * univ.prod (λ i, M (σ i) (τ i) * N (τ i) i))) :
  sum_bij (λ p h, equiv.of_bijective (mem_filter.1 h).2) (λ _ _, mem_univ _)
    (λ _ _, rfl) (λ _ _ _ _ h, by injection h)
    (λ b _, ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, eq_of_to_fun_eq rfl⟩)
... = univ.sum (λ σ : perm n, univ.sum (λ τ : perm n,
    (univ.prod (λ i, N (σ i) i) * sign τ) * univ.prod (λ j, M (τ j) (σ j)))) :
  by simp [mul_sum, det, mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
... = univ.sum (λ σ : perm n, univ.sum (λ τ : perm n,
    (univ.prod (λ i, N (σ i) i) * (sign σ * sign τ)) *
    univ.prod (λ i, M (τ i) i))) :
  sum_congr rfl (λ σ _, sum_bij (λ τ _, τ * σ⁻¹) (λ _ _, mem_univ _)
    (λ τ _,
      have univ.prod (λ j, M (τ j) (σ j)) = univ.prod (λ j, M ((τ * σ⁻¹) j) j),
        by rw prod_univ_perm σ⁻¹; simp [mul_apply],
      have h : (sign σ * sign (τ * σ⁻¹) : R) = sign τ :=
        calc (sign σ * sign (τ * σ⁻¹) : R) = sign ((τ * σ⁻¹) * σ) :
          by rw [mul_comm, sign_mul (τ * σ⁻¹)]; simp [sign_mul]
        ... = sign τ : by simp,
      by rw h; simp [this, mul_comm, mul_assoc, mul_left_comm])
    (λ _ _ _ _, (mul_right_inj _).1) (λ τ _, ⟨τ * σ, by simp⟩))
... = det M * det N : by simp [det, mul_assoc, mul_sum, mul_comm, mul_left_comm]

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

end matrix
