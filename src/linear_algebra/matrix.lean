/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Casper Putz

The equivalence between matrices and linear maps.
-/

import data.matrix
import linear_algebra.dimension linear_algebra.tensor_product linear_algebra.determinant
import data.polynomial

/-!

# Summary

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

Some results are proved about the linear map corresponding to a
diagonal matrix (range, ker and rank).

## Main definitions

to_lin, to_matrix, lin_equiv_matrix

## Tags

linear_map, matrix, linear_equiv, diagonal

-/

noncomputable theory

open set submodule

universes u v
variables {l m n : Type u} [fintype l] [fintype m] [fintype n]

namespace matrix

variables {α : Type v} [comm_ring α]
instance [decidable_eq m] [decidable_eq n] (α) [fintype α] : fintype (matrix m n α) :=
by unfold matrix; apply_instance

/-- Evaluation of matrices gives a linear map from matrix m n α to
linear maps (n → α) →ₗ[α] (m → α). -/
def eval : (matrix m n α) →ₗ[α] ((n → α) →ₗ[α] (m → α)) :=
begin
  refine linear_map.mk₂ α mul_vec _ _ _ _,
  { assume M N v, funext x,
    change finset.univ.sum (λy:n, (M x y + N x y) * v y) = _,
    simp only [_root_.add_mul, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change finset.univ.sum (λy:n, (c * M x y) * v y) = _,
    simp only [_root_.mul_assoc, finset.mul_sum.symm],
    refl },
  { assume M v w, funext x,
    change finset.univ.sum (λy:n, M x y * (v y + w y)) = _,
    simp [_root_.mul_add, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change finset.univ.sum (λy:n, M x y * (c * v y)) = _,
    rw [show (λy:n, M x y * (c * v y)) = (λy:n, c * (M x y * v y)), { funext n, ac_refl },
      ← finset.mul_sum],
    refl }
end

/-- Evaluation of matrices gives a map from matrix m n α to
linear maps (n → α) →ₗ[α] (m → α). -/
def to_lin : matrix m n α → (n → α) →ₗ[α] (m → α) := eval.to_fun

lemma to_lin_add (M N : matrix m n α) : (M + N).to_lin = M.to_lin + N.to_lin :=
matrix.eval.map_add M N

@[simp] lemma to_lin_zero : (0 : matrix m n α).to_lin = 0 :=
matrix.eval.map_zero

instance to_lin.is_linear_map :
  @is_linear_map α (matrix m n α) ((n → α) →ₗ[α] (m → α)) _ _ _ _ _ to_lin :=
matrix.eval.is_linear

instance to_lin.is_add_monoid_hom :
  @is_add_monoid_hom (matrix m n α) ((n → α) →ₗ[α] (m → α)) _ _ to_lin :=
{ map_zero := to_lin_zero, map_add := to_lin_add }

@[simp] lemma to_lin_apply (M : matrix m n α) (v : n → α) :
  (M.to_lin : (n → α) → (m → α)) v = mul_vec M v := rfl

lemma mul_to_lin [decidable_eq l] (M : matrix m n α) (N : matrix n l α) :
  (M.mul N).to_lin = M.to_lin.comp N.to_lin :=
begin
  ext v x,
  simp [to_lin_apply, mul_vec, matrix.mul, finset.sum_mul, finset.mul_sum],
  rw [finset.sum_comm],
  congr, funext x, congr, funext y,
  rw [mul_assoc]
end

end matrix

namespace linear_map

variables {α : Type v} [comm_ring α]

/-- The linear map from linear maps (n → α) →ₗ[α] (m → α) to matrix m n α. -/
def to_matrixₗ [decidable_eq n] : ((n → α) →ₗ[α] (m → α)) →ₗ[α] matrix m n α :=
begin
  refine linear_map.mk (λ f i j, f (λ n, ite (j = n) 1 0) i) _ _,
  { assume f g, simp only [add_apply], refl },
  { assume f g, simp only [smul_apply], refl }
end

/-- The map from linear maps (n → α) →ₗ[α] (m → α) to matrix m n α. -/
def to_matrix [decidable_eq n]: ((n → α) →ₗ[α] (m → α)) → matrix m n α := to_matrixₗ.to_fun

end linear_map

section lin_equiv_matrix

variables {α : Type v} [comm_ring α] [decidable_eq n]

open finsupp matrix linear_map

/-- to_lin is the left inverse of to_matrix. -/
lemma to_matrix_to_lin [decidable_eq α] {f : (n → α) →ₗ[α] (m → α)} :
  to_lin (to_matrix f) = f :=
begin
  ext : 1,
  -- Show that the two sides are equal by showing that they are equal on a basis
  convert linear_eq_on (set.range _) _ (is_basis.mem_span (@pi.is_basis_fun α _ n _ _ _) _),
  assume e he,
  rw [@std_basis_eq_single α _ _ _ _ 1] at he,
  cases (set.mem_range.mp he) with i h,
  ext j,
  change finset.univ.sum (λ k, (f.to_fun (single k 1).to_fun) j * (e k)) = _,
  rw [←h],
  conv_lhs { congr, skip, funext,
    rw [mul_comm, ←smul_eq_mul, ←pi.smul_apply, ←linear_map.smul, single_apply],
    rw [show f.to_fun (ite (i = k) (1:α) 0 • (single k 1).to_fun) = ite (i = k) (f.to_fun ((single k 1).to_fun)) 0,
      { split_ifs, { rw [one_smul] }, { rw [zero_smul], exact linear_map.map_zero f } }] },
  convert finset.sum_eq_single i _ _,
  { rw [if_pos rfl], refl },
  { assume _ _ hbi, rw [if_neg $ ne.symm hbi], refl },
  { assume hi, exact false.elim (hi $ finset.mem_univ i) }
end

/-- to_lin is the right inverse of to_matrix. -/
lemma to_lin_to_matrix {M : matrix m n α} : to_matrix (to_lin M) = M :=
begin
  ext,
  change finset.univ.sum (λ y, M i y * ite (j = y) 1 0) = M i j,
  have h1 : (λ y, M i y * ite (j = y) 1 0) = (λ y, ite (j = y) (M i y) 0),
    { ext, split_ifs, exact mul_one _, exact ring.mul_zero _ },
  have h2 : finset.univ.sum (λ y, ite (j = y) (M i y) 0) = (finset.singleton j).sum (λ y, ite (j = y) (M i y) 0),
    { refine (finset.sum_subset _ _).symm,
      { intros _ H, rwa finset.mem_singleton.1 H, exact finset.mem_univ _ },
      { exact λ _ _ H, if_neg (mt (finset.mem_singleton.2 ∘ eq.symm) H) } },
  rw [h1, h2, finset.sum_singleton],
  exact if_pos rfl
end

/-- Linear maps (n → α) →ₗ[α] (m → α) are linearly equivalent to matrix  m n α. -/
def lin_equiv_matrix' [decidable_eq α] : ((n → α) →ₗ[α] (m → α)) ≃ₗ[α] matrix m n α :=
{ to_fun := to_matrix,
  inv_fun := to_lin,
  right_inv := λ _, to_lin_to_matrix,
  left_inv := λ _, to_matrix_to_lin,
  add := to_matrixₗ.add,
  smul := to_matrixₗ.smul }

instance decidable_eq_fun (ι : Type*) [decidable_eq α] [fintype ι] : decidable_eq (ι → α)
  | f g := if h : _ then is_true $ funext h else is_false (mt congr_fun h)

/-- Given a basis of two modules β and γ over a commutative ring α, we get a linear equivalence
between linear maps β →ₗ γ and matrices over α indexed by the bases. -/
def lin_equiv_matrix {ι κ β γ : Type*} [decidable_eq α]
  [add_comm_group β] [decidable_eq β] [module α β]
  [add_comm_group γ] [decidable_eq γ] [module α γ]
  [fintype ι] [decidable_eq ι] [fintype κ] [decidable_eq κ]
  {v₁ : ι → β} {v₂ : κ → γ} (hv₁ : is_basis α v₁) (hv₂ : is_basis α v₂) :
  (β →ₗ[α] γ) ≃ₗ[α] matrix κ ι α :=
linear_equiv.trans (linear_equiv.arrow_congr (equiv_fun_basis hv₁) (equiv_fun_basis hv₂)) lin_equiv_matrix'

--TODO: universes
variables {ι₁ ι₂ ι₃ β₁ β₂ β₃ : Type u} [decidable_eq α]
variables [add_comm_group β₁] [decidable_eq β₁] [module α β₁]
variables [add_comm_group β₂] [decidable_eq β₂] [module α β₂]
variables [add_comm_group β₃] [decidable_eq β₃] [module α β₃]
variables [fintype ι₁] [decidable_eq ι₁] {v₁ : ι₁ → β₁} (hv₁ : is_basis α v₁)
variables [fintype ι₂] [decidable_eq ι₂] {v₂ : ι₂ → β₂} (hv₂ : is_basis α v₂)
variables [fintype ι₃] [decidable_eq ι₃] {v₃ : ι₃ → β₃} (hv₃ : is_basis α v₃)

lemma lin_equiv_matrix_comp (f : β₁ →ₗ[α] β₂) (g : β₂ →ₗ[α] β₃) :
  (lin_equiv_matrix hv₁ hv₃).to_fun (g.comp f) =
  ((lin_equiv_matrix hv₂ hv₃).to_fun g).mul ((lin_equiv_matrix hv₁ hv₂).to_fun f) := sorry

lemma lin_equiv_matrix_mul (M : matrix ι₂ ι₁ α) (N : matrix ι₃ ι₂ α) :
  (lin_equiv_matrix hv₁ hv₃).inv_fun (N.mul M) =
  ((lin_equiv_matrix hv₂ hv₃).inv_fun N).comp ((lin_equiv_matrix hv₁ hv₂).inv_fun M) := sorry

end lin_equiv_matrix

namespace matrix

section ring

variables {α : Type v} [comm_ring α]
open linear_map matrix

lemma proj_diagonal [decidable_eq m] (i : m) (w : m → α) :
  (proj i).comp (to_lin (diagonal w)) = (w i) • proj i :=
by ext j; simp [mul_vec_diagonal]

lemma diagonal_comp_std_basis [decidable_eq n] (w : n → α) (i : n) :
  (diagonal w).to_lin.comp (std_basis α (λ_:n, α) i) = (w i) • std_basis α (λ_:n, α) i :=
begin
  ext a j,
  simp only [linear_map.comp_apply, smul_apply, to_lin_apply, mul_vec_diagonal, smul_apply,
    pi.smul_apply, smul_eq_mul],
  by_cases i = j,
  { subst h },
  { rw [std_basis_ne α (λ_:n, α) _ _ (ne.symm h), _root_.mul_zero, _root_.mul_zero] }
end

end ring

section vector_space

variables {α : Type u} [discrete_field α] -- maybe try to relax the universe constraint

open linear_map matrix

lemma rank_vec_mul_vec [decidable_eq n] (w : m → α) (v : n → α) :
  rank (vec_mul_vec w v).to_lin ≤ 1 :=
begin
  rw [vec_mul_vec_eq, mul_to_lin],
  refine le_trans (rank_comp_le1 _ _) _,
  refine le_trans (rank_le_domain _) _,
  rw [dim_fun', ← cardinal.fintype_card],
  exact le_refl _
end

set_option class.instance_max_depth 100

lemma diagonal_to_lin [decidable_eq m] (w : m → α) :
  (diagonal w).to_lin = linear_map.pi (λi, w i • linear_map.proj i) :=
by ext v j; simp [mul_vec_diagonal]

lemma ker_diagonal_to_lin [decidable_eq m] (w : m → α) :
  ker (diagonal w).to_lin = (⨆i∈{i | w i = 0 }, range (std_basis α (λi, α) i)) :=
begin
  rw [← comap_bot, ← infi_ker_proj],
  simp only [comap_infi, (ker_comp _ _).symm, proj_diagonal, ker_smul'],
  have : univ ⊆ {i : m | w i = 0} ∪ -{i : m | w i = 0}, { rw set.union_compl_self },
  exact (supr_range_std_basis_eq_infi_ker_proj α (λi:m, α)
    (disjoint_compl {i | w i = 0}) this (finite.of_fintype _)).symm
end

lemma range_diagonal [decidable_eq m] (w : m → α) :
  (diagonal w).to_lin.range = (⨆ i ∈ {i | w i ≠ 0}, (std_basis α (λi, α) i).range) :=
begin
  dsimp only [mem_set_of_eq],
  rw [← map_top, ← supr_range_std_basis, map_supr],
  congr, funext i,
  rw [← linear_map.range_comp, diagonal_comp_std_basis, range_smul'],
end

lemma rank_diagonal [decidable_eq m] [decidable_eq α] (w : m → α) :
  rank (diagonal w).to_lin = fintype.card { i // w i ≠ 0 } :=
begin
  have hu : univ ⊆ - {i : m | w i = 0} ∪ {i : m | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : m | w i ≠ 0} {i : m | w i = 0} := (disjoint_compl {i | w i = 0}).symm,
  have h₁ := supr_range_std_basis_eq_infi_ker_proj α (λi:m, α) hd hu (finite.of_fintype _),
  have h₂ := @infi_ker_proj_equiv α _ _ (λi:m, α) _ _ _ _ (by simp; apply_instance) hd hu,
  rw [rank, range_diagonal, h₁, ←@dim_fun' α],
  apply linear_equiv.dim_eq,
  apply h₂,
end

end vector_space

end matrix


open polynomial matrix

variables {α : Type v} [decidable_eq α] [comm_ring α]
variables [decidable_eq n]

def char_polynomial (M : matrix n n α) : polynomial α :=
det (diagonal (λ _:n, (X : polynomial α)) - (λ i j, C (M i j)))

namespace char_polynomial

variables (M : matrix n n α)

lemma eval (b : α) : eval b (char_polynomial M) = det (diagonal (λ _, b) - M) :=
begin
  change (λ p : polynomial α, eval b p) (det (diagonal (λ _:n, X) - λ (i j : n), C (M i j))) = _,
  rw [det_map_hom (λ p : polynomial α, eval b p)],
  congr,
  ext,
  simp,
  unfold diagonal,
  split_ifs,
  exact eval_X,
  exact eval_zero
end

lemma constant_coeff : coeff (char_polynomial M) 0 = (-1) ^ fintype.card n * det M :=
by rw [coeff_zero_eq_eval_zero, eval, diagonal_zero, zero_sub, det_neg]

lemma coeff_sum {ι : Type*} (s : finset ι) (f : ι → polynomial α) (n : ℕ) :
  coeff (s.sum f) n = s.sum (λ i:ι, coeff (f i) n) := sorry

lemma sum_ite_zero {ι β : Type*} [add_comm_monoid β] (s : finset ι) (f : ι → β) (r : ι → Prop) [decidable_pred r] :
  s.sum (λ i, ite (r i) (f i) 0) = (s.filter r).sum f := eq.symm $ sum_filter r f

lemma degree_prod {ι : Type*} (s : finset ι) (f : ι → polynomial α) :
  degree (s.prod f) = s.sum (λ i, degree (f i)) := sorry

--TODO: move and define leading_coeff to be a monoid_hom?
instance leading_coeff_is_monoid_hom :
  is_monoid_hom (leading_coeff : polynomial α → α) := sorry --true if α is an integral_domain
--{ map_mul := leading_coeff_mul,
--  map_one := leading_coeff_one }

lemma leading_coeff_prod {ι : Type*} (s : finset ι) (f : ι → polynomial α) :
  leading_coeff (s.prod f) = s.prod (λ i, leading_coeff (f i)) := eq.symm $ finset.prod_hom (leading_coeff : polynomial α → α)

lemma with_bot.lt_one_of_le_zero {a : with_bot ℕ} (ha : a ≤ 0) : a < ↑1 := begin
  by_cases h : a = ⊥,
  { rw [h], exact with_bot.bot_lt_coe _ },
  { rw [←ne.def, option.ne_none_iff_is_some, option.is_some_iff_exists] at h,
    cases h with n hn,
    rw [←with_bot.coe_zero, hn, with_bot.some_eq_coe, with_bot.coe_le_coe] at ha,
    rwa [hn, with_bot.some_eq_coe, with_bot.coe_lt_coe, nat.lt_succ_iff] }
end

lemma coeff_n : coeff (char_polynomial M) (fintype.card n) = 1 :=
begin
change coeff (finset.univ.sum (λ (b : equiv.perm n),
  (↑(equiv.perm.sign b : ℤ) * finset.univ.prod (λ i:n, (ite (b i = i) X 0) - C (M (b i) i))))) (fintype.card n) = 1,
rw [coeff_sum],
have hd : nat_degree (finset.univ.prod (λ (j : n), X - C (M j j))) = fintype.card n, from sorry,
/-have hd2 : ∀ i : equiv.perm n, degree (finset.prod finset.univ (λ (j : n), ite (i j = j) X 0 - C (M (i j) j))) = finset.card (finset.univ.filter (λ j : n, i j = j)), from
  begin
    intro b,
    rw [degree_prod],
    conv_lhs {congr, skip, funext,
      rw [show degree (ite (b i = i) X 0 - C (M (b i) i)) = ite (b i = i) 1 (degree (C (M (b i) i))), from
      begin
        split_ifs,
        sorry, -- degree_X_sub_C _, --α should be an integral_domain
        rw [zero_sub, degree_neg]
      end],

    },
  end,-/
conv_lhs {congr, skip, funext, rw [int_cast_eq_C, coeff_C_mul],
  rw [show (coeff (finset.prod finset.univ (λ j:n, ite (i j = j) X 0 - C (M (i j) j))) (fintype.card n)) = ite (i = equiv.refl n) 1 0, from
  begin
    split_ifs with h h,
    { rw [h, ←hd],
      conv_lhs { congr, congr, skip, funext, rw [equiv.refl_apply, if_pos rfl] },
      change leading_coeff (finset.univ.prod (λ (j : n), X - C (M j j))) = 1,
      rw [←finset.prod_hom leading_coeff],
      conv_lhs { congr, skip, funext, rw [monic.def.mp $ monic_X_sub_C _] },
      exact finset.prod_const_one,
      apply_instance },
    { have : ∃ j : n, i j ≠ (equiv.refl n) j, from classical.not_forall.mp (λ hn, h (equiv.ext _ _ hn)),
      cases this with j hj,
      rw [equiv.refl_apply] at hj,
      apply coeff_eq_zero_of_degree_lt,
      suffices hs : ∀ s : finset n, j ∈ s → degree (s.prod (λ j:n, ite (i j = j) X 0 - C (M (i j) j))) < ↑s.card,
        { rw [fintype.card], exact hs finset.univ (finset.mem_univ j) },
      intros s hjs,
      have h0 : finset.card s > 0, from finset.card_pos.mpr (finset.ne_empty_of_mem hjs),
      induction hs : nat.pred (finset.card s),
      { have h1 : finset.card s = 1, from nat.succ_pred_eq_of_pos h0 ▸ congr_arg nat.succ hs,
        rw [h1],
        rw [finset.card_eq_one] at h1,
        cases h1 with k hk,
        rw [hk, finset.mem_singleton] at hjs,
        rw [hk, finset.prod_singleton, ←hjs, if_neg hj, zero_sub, degree_neg],
        exact with_bot.lt_one_of_le_zero degree_C_le },
      { have hn_1 : finset.card s = nat.succ (nat.succ n_1), from nat.succ_pred_eq_of_pos h0 ▸ congr_arg nat.succ hs,
        have hf : s = finset.singleton j ∪ (s \ finset.singleton j), from
          eq.symm (finset.union_sdiff_of_subset
            (by { rw [finset.subset_iff], intros _ h, rw [finset.mem_singleton] at h, rwa [h] })),
        rw [hf, finset.prod_union (finset.inter_sdiff_self _ _), finset.prod_singleton],

       }
     }
  end]
},
end

/-lemma degree_prod (s : finset α) (f : α → polynomial α) :
  degree (s.prod (λ i, f i)) = s.sum (λ i, degree (f i)) :=
sorry

lemma degree (α2 : Type v) [integral_domain α2] [decidable_eq α2] (M : matrix n n α2):
  degree (char_polynomial M) = fintype.card n :=
begin
  unfold char_polynomial,
  unfold det,
  convert degree_sum_le _ _,
  --(λ i:n, (if (b i = i) then X else 0) - C (M (b i) i))
  --(λ (i : n), (diagonal (λ (_x : n), X) - λ (i j : n), C (M i j)) (⇑b i) i)
  --(λ (i : n), (diagonal (λ (_x : n), X) - λ (i j : n), C (M i j)) (⇑b i) i)
  change _ = finset.univ.sup (λ (b : equiv.perm n), degree (_ *
    finset.univ.prod (λ (i : n), _ (b i) i))),
  have : ∀ b : equiv.perm n, ((equiv.perm.sign b : ℤ) : α2) ≠ 0, from sorry,
  conv_rhs { congr, skip, funext,
    rw [degree_mul_eq, int_cast_eq_C, degree_C (this b), zero_add,
      degree_prod _],  },
end-/

lemma monic : monic (char_polynomial M) := sorry

end char_polynomial
