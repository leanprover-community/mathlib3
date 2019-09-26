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

variables {α : Type v} [decidable_eq α] [integral_domain α]
variables [decidable_eq n]

def char_polynomial (M : matrix n n α) : polynomial α :=
det (diagonal (λ _:n, (X : polynomial α)) - (λ i j, C (M i j)))

namespace char_polynomial

variables (M : matrix n n α)

lemma eval (b : α) : eval b (char_polynomial M) = det (diagonal (λ _, b) - M) :=
begin
  change (λ p : polynomial α, eval b p) (det (diagonal (λ _:n, X) - λ (i j : n), C (M i j))) = _,
  rw [det_map_hom (λ p : polynomial α, eval b p)],
  congr, ext, simp [diagonal],
  split_ifs,
  exact eval_X,
  exact eval_zero
end

lemma constant_coeff : coeff (char_polynomial M) 0 = (-1) ^ fintype.card n * det M :=
by rw [coeff_zero_eq_eval_zero, eval, diagonal_zero, zero_sub, det_neg]

lemma coeff_sum {ι : Type*} (s : finset ι) (f : ι → polynomial α) (n : ℕ) :
  coeff (s.sum f) n = s.sum (λ i:ι, coeff (f i) n) := sorry

lemma degree_prod {ι : Type*} (s : finset ι) (f : ι → polynomial α) :
  degree (s.prod f) = s.sum (λ i, degree (f i)) := sorry

lemma degree_prod_le {ι : Type*} (s : finset ι) (f : ι → polynomial α) (g : ι → with_bot ℕ)
  (h : ∀ i ∈ s, degree (f i) ≤ g i) : degree (s.prod f) ≤ s.sum g := sorry

lemma degree_sum_le {ι : Type*} (s : finset ι) (f : ι → polynomial α) (b : with_bot ℕ)
  (h : ∀ i ∈ s, degree (f i) ≤ b) : degree (s.sum f) ≤ b := sorry

--TODO: move and define leading_coeff to be a monoid_hom?
instance leading_coeff_is_monoid_hom :
  is_monoid_hom (leading_coeff : polynomial α → α) :=
{ map_mul := leading_coeff_mul,
  map_one := leading_coeff_one }

--TODO: move
lemma with_bot.nat_cast_eq_coe (n : ℕ) : (nat.cast n : with_bot ℕ) = ↑n :=
nat.rec_on n rfl (λ m hm,
  by { rw [nat.succ_eq_add_one, with_bot.coe_add, with_bot.coe_one, ←hm], exact nat.cast_add_one _ })

lemma degree_aux :
  char_polynomial M = (char_polynomial M - X ^ fintype.card n) + X ^ fintype.card n ∧
  degree (char_polynomial M - X ^ fintype.card n) < degree ((X : polynomial α) ^ fintype.card n) :=
⟨by { rw [add_comm, add_sub, add_comm, ←add_sub, sub_self, add_zero] },
begin
  sorry
end⟩

lemma degree : degree (char_polynomial M) = fintype.card n :=
begin
  rw [←degree_X_pow (fintype.card n), (degree_aux M).1],
  exact degree_add_eq_of_degree_lt (degree_aux M).2
end

lemma monic : monic (char_polynomial M) :=
begin
  rw [monic.def, (degree_aux M).1],
  convert leading_coeff_add_of_degree_lt (degree_aux M).2,
  exact eq.symm (leading_coeff_X_pow _)
end


lemma degree_eq_aux (s : finset n) :
  degree (s.prod (λ i, diagonal (λ _:n, X) (equiv.refl n i) i - C (M (equiv.refl n i) i))) = s.card :=
begin
  rw [←with_bot.nat_cast_eq_coe, ←show _ = nat.cast _, from add_monoid.smul_one s.card, ←finset.sum_const],
  rw [degree_prod],
  congr,
  funext j,
  rw [equiv.refl_apply, diagonal],
  dsimp,
  rw [if_pos rfl, ←sub_eq_add_neg, degree_X_sub_C]
end

lemma coeff_aux {s : finset n} (hs : s.card > 0) :
  coeff (s.prod (λ i, diagonal (λ _:n, X) (equiv.refl n i) i - C (M (equiv.refl n i) i))) s.card = 1 :=
suffices h : leading_coeff (s.prod (λ i, diagonal (λ _:n, X) (equiv.refl n i) i - C (M (equiv.refl n i) i))) = 1,
{ unfold leading_coeff at h,
  convert h,
  rw [←with_bot.coe_eq_coe, ←degree_eq_nat_degree],
  { symmetry, exact degree_eq_aux _ _ },
  { refine @ne_zero_of_degree_gt _ _ _ _ 0 _,
    rw [diagonal, degree_prod], dsimp,
    conv_rhs { congr, skip, funext, rw [if_pos rfl, ←sub_eq_add_neg, degree_X_sub_C] },
    rw [finset.sum_const, show _ = nat.cast _, from add_monoid.smul_one _, with_bot.nat_cast_eq_coe],
    rwa [←with_bot.coe_zero, with_bot.coe_lt_coe] } },
begin
  rw [←finset.prod_hom leading_coeff, ←@finset.prod_const_one _ _ s, diagonal],
  congr,
  funext j,
  dsimp,
  rw [if_pos rfl, ←sub_eq_add_neg],
  exact monic_X_sub_C _,
  apply_instance
end

lemma degree_lt_aux {p : equiv.perm n} {s : finset n} {j : n} (hj : j ∈ s) (hp : p j ≠ j) :
  degree (s.prod (λ i, diagonal (λ _:n, X) (p i) i - C (M (p i) i))) < s.card :=
begin
  have : finset.singleton j ⊆ s,
    { rw [finset.subset_iff], intros _ h, rw [finset.mem_singleton] at h, rwa [h] },
  have hf : s = finset.singleton j ∪ (s \ finset.singleton j), from
    eq.symm (finset.union_sdiff_of_subset this),
  rw [hf, finset.prod_union (finset.inter_sdiff_self _ _), degree_mul_eq, finset.prod_singleton, diagonal],
  dsimp,
  rw [if_neg hp, zero_add, degree_neg],
  by_cases hMj : M (p j) j = 0,
  { rw [hMj, C_0, degree_zero, with_bot.bot_add], exact with_bot.bot_lt_coe _ },
  { rw [degree_C hMj, zero_add],
    refine lt_of_le_of_lt (degree_prod_le (s \ finset.singleton j) _ (λ _, 1) _) _,
    { intros i hi, split_ifs,
      { rw [←sub_eq_add_neg, degree_X_sub_C], exact le_refl _ },
      { rw [zero_add, degree_neg],
        refine le_trans degree_C_le _,
        rw [←with_bot.coe_one, ←with_bot.coe_zero, with_bot.coe_le_coe],
        exact zero_le_one } },
    { rw [finset.sum_const, show _ = nat.cast _, from add_monoid.smul_one _,
        with_bot.nat_cast_eq_coe _, with_bot.coe_lt_coe],
      refine finset.card_lt_card _,
      rw [finset.ssubset_iff],
      existsi j,
      split,
      { rw [finset.mem_sdiff, not_and, not_not, finset.mem_singleton], intro, refl },
      { rw [finset.insert_eq], dsimp, rw[←hf], exact finset.subset.refl _ } } }
end

lemma degree_le : degree (char_polynomial M) ≤ fintype.card n :=
suffices h : degree (char_polynomial M) ≤ finset.univ.sum (λ i:n, 1),
  { rw [finset.sum_const, add_monoid.smul_one] at h, rwa [←with_bot.nat_cast_eq_coe] },
begin
  convert degree_sum_le _ _ _ _,
  intros i hi,
  rw [degree_mul_eq],
  rw [show degree ↑(equiv.perm.sign i : ℤ) = 0,
    { have : (equiv.perm.sign i : ℤ) = 1 ∨ (equiv.perm.sign i : ℤ) = -1,
        { rw [←units.coe_one, ←units.coe_neg, ←units.ext_iff, ←units.ext_iff],
          exact int.units_eq_one_or (equiv.perm.sign i) },
      cases this with h h,
      { rw [h, int.cast_one, degree_one] },
      { rw [h, int.cast_neg, int.cast_one, ←@degree_one α, ←degree_neg] } }],
  rw [zero_add],
  refine degree_prod_le _ _ _ _,
  intros j hj,
  rw [diagonal],
  dsimp,
  split_ifs,
  { rw [←sub_eq_add_neg, degree_X_sub_C], exact le_refl _ },
  { rw [zero_add, degree_neg],
    by_cases hM :  M (i j) j = 0,
    { rw [hM, C_0, degree_zero], exact le_of_lt (with_bot.bot_lt_coe _) },
    { rw [degree_C hM, ←with_bot.coe_zero, ←with_bot.coe_one, with_bot.coe_le_coe],
      exact le_of_lt nat.zero_lt_one } }
end

lemma coeff_n (hn : fintype.card n > 0) : coeff (char_polynomial M) (fintype.card n) = 1 :=
begin
  unfold char_polynomial,
  unfold det,
  rw [coeff_sum],
  rw [←show finset.univ.sum (λ i, ite (equiv.refl n = i) (1:α) 0) = 1,
    { rw [←finset.sum_subset (finset.subset_univ (finset.singleton (equiv.refl n))) _],
      { convert finset.sum_singleton, rw [if_pos rfl] },
      { intros _ _ h, rw [finset.mem_singleton] at h, rw [if_neg $ ne.symm h], } }],
  congr,
  ext p,
  rw [int_cast_eq_C, coeff_C_mul],
  dsimp, conv_lhs {congr, skip, congr, congr, skip, funext, rw [←sub_eq_add_neg]},
  split_ifs,
  { unfold fintype.card,
    rw [←h, coeff_aux M hn, equiv.perm.sign_refl, mul_one, units.coe_one, int.cast_one] },
  { unfold fintype.card,
    have : ∃ j : n, p j ≠ (equiv.refl n) j, from (classical.not_forall.mp (λ hn, (ne.symm h) (equiv.ext _ _ hn))),
    cases this with j hj,
    rw [coeff_eq_zero_of_degree_lt (degree_lt_aux M (finset.mem_univ j) hj), mul_zero] }
end

lemma degree (hn : fintype.card n > 0) : degree (char_polynomial M) = fintype.card n :=
le_antisymm (degree_le M)
  (le_of_not_gt (λ h, begin
    apply @one_ne_zero α,
    rw [←coeff_n M hn],
    apply coeff_eq_zero_of_degree_lt,
    assumption end))

lemma ne_zero (hn : fintype.card n > 0) : char_polynomial M ≠ 0 :=
begin
  apply @ne_zero_of_degree_gt _ _ _ _ ↑(fintype.card n - 1),
  rw [degree M hn, with_bot.coe_lt_coe],
  exact nat.pred_lt (nat.pos_iff_ne_zero.mp hn)
end

lemma monic (hn : fintype.card n > 0) : monic (char_polynomial M) :=
begin
  unfold monic leading_coeff,
  convert coeff_n M hn,
  rw [←with_bot.coe_eq_coe, ←degree_eq_nat_degree (ne_zero M hn)],
  exact degree M hn
end

end char_polynomial
