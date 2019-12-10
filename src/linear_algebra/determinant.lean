/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import data.matrix.basic
import group_theory.perm.sign

import data.polynomial

universes u v w
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

@[simp] lemma det_neg_one : det (-1 : matrix n n R) = (-1) ^ fintype.card n :=
by { rw [←diagonal_one, diagonal_neg, det_diagonal, finset.prod_const], refl }

@[simp] lemma det_neg (M : matrix n n R) : det (-M) = (-1) ^ fintype.card n * det M :=
by rw [neg_eq_neg_one_mul, det_mul, det_neg_one]

--TODO: move
lemma is_semiring_hom.map_nat_cast (a : ℕ) {S : Type w} [comm_ring S] (f : R → S) [hf : is_semiring_hom f] :
  f a = a :=
begin
induction a with _ hn,
{ rw_mod_cast [hf.map_zero] },
{ rw [nat.succ_eq_add_one, nat.cast_add, hf.map_add], rw_mod_cast [hf.map_one, hn], refl }
end

lemma det_map_hom {S : Type w} [comm_ring S] (f : R → S) [is_ring_hom f] (M : matrix n n R) :
  f (det M) = det (λ i j, f (M i j)) :=
begin
  unfold det,
  rw [←finset.sum_hom f],
  congr,
  ext,
  rw [is_ring_hom.map_mul f, ←finset.prod_hom f],
  congr,
  induction (sign x : ℤ) with _ n,
  { exact is_semiring_hom.map_nat_cast _ f },
  { rw [int.neg_succ_of_nat_eq, int.cast_neg, is_ring_hom.map_neg f],
    norm_cast,
    rw [is_semiring_hom.map_nat_cast _ f, int.cast_neg, int.cast_coe_nat] }
end

private def subtype_swap (i j : n) : {k // k ≠ i} → {k // k ≠ j} := subtype.map (swap j i)
  (λ a hi, by { by_cases hj : a ≠ j, rwa [swap_apply_of_ne_of_ne hj hi],
    rw [ne.def, not_not] at hj, symmetry, rw[hj] at hi, rwa [hj, swap_apply_left] })

/-- The `(i,j)`-th cofactor of `M` is (upto sign) the determinant of the submatrix of `M` obtained
by removing the `i`-th row and `j`-th column. -/
def cofactor (i j : n) (M : matrix n n R) : R :=
(sign (swap i j) : ℤ) * (det $ minor M (subtype.val ∘ subtype_swap j i) (subtype.val : {k : n // k ≠ j} → n))

lemma cofactor_expansion_aux (M : matrix n n R) (i j : n) :
  univ.sum (λ σ : { σ : perm n // σ.to_fun j = i }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
  M i j * cofactor i j M :=
have hσ : ∀ (σ : { σ : perm n // σ.to_fun j = i }) l, l ≠ j ↔ (equiv.trans σ.1 (swap i j)) l ≠ j,
  from λ σ l, by { rw [equiv.trans_apply, not_iff_not], unfold_coes,
  exact ⟨λ h, by {rw [h, σ.2], exact swap_apply_left i j },
    λ h, σ.val.injective $ (swap i j).injective $ eq.symm $
        by { unfold_coes, rw [h, σ.2], exact swap_apply_left i j }⟩ },
calc univ.sum (λ σ : { σ : perm n // σ.to_fun j = i }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
      M i j * univ.sum (λ σ : { σ : perm n // σ.to_fun j = i }, ε σ.val *
        (erase univ j).prod (λ l, M (equiv.swap i j $ equiv.swap i j $ σ l) l)) :
  begin
    simp only [mul_sum, swap_swap_apply], congr, funext σ,
    rw [←insert_erase (mem_univ j), prod_insert (not_mem_erase _ _), ←mul_assoc,
      mul_comm _ (M _ _), mul_assoc],
    congr, exact σ.2, exact eq.symm (insert_erase (mem_univ j)),
  end
... = M i j * (sign (swap i j) : ℤ) * univ.sum (λ τ : perm { k // k ≠ j }, ε τ * univ.prod (λ l, M (swap i j $ τ l) l)) :
  begin
    rw [mul_assoc, @mul_sum _ _ _ _ ↑(sign (swap i j) : ℤ)],
    apply congr_arg,
    refine sum_bij (λ σ _, subtype_congr (equiv.trans σ.1 (swap i j)) (hσ σ))
      (λ _ _, mem_univ _) _
      (λ σ₁ σ₂ _ _ h, by { rw [subtype.ext], ext l, by_cases hl : l = j,
        { unfold_coes, rw [hl, σ₁.2, σ₂.2] },
        { let h1 := congr_arg equiv.to_fun h,
          have h2 := congr_fun h1 ⟨l, hl⟩,
          have h3 := congr_arg (equiv.swap i j ∘ subtype.val) h2,
          change equiv.swap i j (equiv.swap i j (σ₁.val l)) = equiv.swap i j (equiv.swap i j (σ₂.val l)) at h3,
          rwa [swap_swap_apply, swap_swap_apply] at h3 } } )
      (λ τ _, ⟨⟨equiv.trans (of_subtype τ) (swap i j),
        begin change equiv.swap i j (of_subtype τ j) = i,
          rw [of_subtype_apply_of_not_mem, swap_apply_right], rw [ne.def, not_not] end⟩, mem_univ _,
          begin ext k, apply subtype.val_injective,
            change (τ k).val = equiv.swap i j (equiv.swap i j (of_subtype τ k.val)),
            rw [swap_swap_apply, of_subtype], dsimp, rw [dif_pos k.property],
            exact congr_arg _ (congr_arg _ $ eq.symm $ subtype.eta _ _) end ⟩),
    intros σ _,
    have hs : sign (swap i j * σ.val) = sign (subtype_congr (equiv.trans (σ.val) (swap i j)) (hσ σ) : perm {k // k ≠ j}),
    { refine sign_bij (λ k hk, subtype.mk k (λ h, by { rw [h, mul_apply] at hk, unfold_coes at hk, rw [σ.2] at hk, exact hk (swap_apply_left i j) }))
        (λ _ _ _, rfl) (λ _ _ _ _, congr_arg subtype.val)
        (λ k hk, ⟨k.val, by { revert hk, contrapose!, intro hk, exact subtype.val_injective hk },
          subtype.eta _ _⟩) },
    rw_mod_cast [←hs, sign_mul, ←mul_assoc, ←units.coe_mul, ←mul_assoc, ←sign_mul, equiv.swap_mul_self, sign_one, one_mul],
    exact congr_arg _ (prod_bij (λ l hl, ⟨l, (mem_erase.mp hl).1⟩) (λ _ _, mem_univ _) (λ _ _, rfl)
      (λ _ _ _ _, congr_arg subtype.val)
      (λ l _, ⟨l, mem_erase.mpr ⟨l.2, mem_univ _⟩, eq.symm (subtype.eta _ _)⟩))
  end
... = M i j * cofactor i j M : mul_assoc _ _ _

/-- The deteminant of `M` can be expanded as the sum over all elements `M i j` in a fixed column j
times the corresponding `cofactor i j M`. -/
lemma cofactor_expansion (M : matrix n n R) (j : n) : det M = univ.sum (λ i, M i j * cofactor i j M) :=
begin
  conv_rhs { congr, skip, funext, rw ←cofactor_expansion_aux },
  rw ←@sum_sigma _ _ _ (λ i, {σ : perm n // σ.to_fun j = i}) _ _ (λ σ, ε (σ.2.val) * univ.prod (λ l, M (σ.2 l) l)),
  symmetry, unfold det,
  refine sum_bij (λ σ _, σ.snd.val) (λ _ _, mem_univ _) (λ _ _, rfl) _
    (λ σ _, ⟨sigma.mk (σ j) (subtype.mk σ rfl), mem_univ _, rfl⟩),
  { intros σ1 σ2 _ _ h,
    have : σ1.fst = σ2.fst, { rw [←σ1.snd.property, ←σ2.snd.property, h] },
    refine sigma.eq this (subtype.val_injective _),
    { rw ←h, congr, { funext, exact (congr_arg _ $ eq.symm this) }, apply eq_rec_heq }}
end

open polynomial

lemma test1 (i : n) (M : matrix n n R) :
  minor (diagonal (λ _:n, (X : polynomial R)) - (λ k l, C (M k l))) (subtype.val ∘ subtype_swap i i) (subtype.val : {k : n // k ≠ i} → n) =
  (diagonal (λ _, X)) - (λ k l, C (M (swap i i k) l)) :=
begin
funext k l,
unfold minor subtype_swap,
simp [subtype.map],
dsimp,
rw [swap_self],
simp only [refl_apply, diagonal, subtype.ext],
congr
end

end matrix
