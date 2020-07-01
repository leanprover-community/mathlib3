/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Casper Putz
-/
import linear_algebra.finite_dimensional
import linear_algebra.nonsingular_inverse

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

Some results are proved about the linear map corresponding to a
diagonal matrix (range, ker and rank).

## Main definitions

to_lin, to_matrix, linear_equiv_matrix

## Tags

linear_map, matrix, linear_equiv, diagonal

-/

noncomputable theory

open set submodule
open_locale big_operators

universes u v w
variables {l m n : Type u} [fintype l] [fintype m] [fintype n]

namespace matrix

variables {R : Type v} [comm_ring R]
instance [decidable_eq m] [decidable_eq n] (R) [fintype R] : fintype (matrix m n R) :=
by unfold matrix; apply_instance

/-- Evaluation of matrices gives a linear map from matrix m n R to
linear maps (n → R) →ₗ[R] (m → R). -/
def eval : (matrix m n R) →ₗ[R] ((n → R) →ₗ[R] (m → R)) :=
begin
  refine linear_map.mk₂ R mul_vec _ _ _ _,
  { assume M N v, funext x,
    change ∑ y : n, (M x y + N x y) * v y = _,
    simp only [_root_.add_mul, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change ∑ y : n, (c * M x y) * v y = _,
    simp only [_root_.mul_assoc, finset.mul_sum.symm],
    refl },
  { assume M v w, funext x,
    change ∑ y : n, M x y * (v y + w y) = _,
    simp [_root_.mul_add, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change ∑ y : n, M x y * (c * v y) = _,
    rw [show (λy:n, M x y * (c * v y)) = (λy:n, c * (M x y * v y)), { funext n, ac_refl },
      ← finset.mul_sum],
    refl }
end

/-- Evaluation of matrices gives a map from matrix m n R to
linear maps (n → R) →ₗ[R] (m → R). -/
def to_lin : matrix m n R → (n → R) →ₗ[R] (m → R) := eval.to_fun

theorem to_lin_of_equiv {p q : Type*} [fintype p] [fintype q] (e₁ : m ≃ p) (e₂ : n ≃ q)
  (f : matrix p q R) : to_lin (λ i j, f (e₁ i) (e₂ j) : matrix m n R) =
    linear_equiv.arrow_congr
      (linear_map.fun_congr_left R R e₂)
      (linear_map.fun_congr_left R R e₁)
      (to_lin f) :=
linear_map.ext $ λ v, funext $ λ i,
calc  ∑ j : n, f (e₁ i) (e₂ j) * v j
    = ∑ j : n, f (e₁ i) (e₂ j) * v (e₂.symm (e₂ j)) : by simp_rw e₂.symm_apply_apply
... = ∑ k : q, f (e₁ i) k * v (e₂.symm k) : finset.sum_equiv e₂ (λ k, f (e₁ i) k * v (e₂.symm k))

lemma to_lin_add (M N : matrix m n R) : (M + N).to_lin = M.to_lin + N.to_lin :=
matrix.eval.map_add M N

@[simp] lemma to_lin_zero : (0 : matrix m n R).to_lin = 0 :=
matrix.eval.map_zero

@[simp] lemma to_lin_neg (M : matrix m n R) : (-M).to_lin = -M.to_lin :=
@linear_map.map_neg _ _ ((n → R) →ₗ[R] m → R) _ _ _ _ _ matrix.eval M

instance to_lin.is_add_monoid_hom :
  @is_add_monoid_hom (matrix m n R) ((n → R) →ₗ[R] (m → R)) _ _ to_lin :=
{ map_zero := to_lin_zero, map_add := to_lin_add }

@[simp] lemma to_lin_apply (M : matrix m n R) (v : n → R) :
  (M.to_lin : (n → R) → (m → R)) v = mul_vec M v := rfl

lemma mul_to_lin (M : matrix m n R) (N : matrix n l R) :
  (M.mul N).to_lin = M.to_lin.comp N.to_lin :=
by { ext, simp }

@[simp] lemma to_lin_one [decidable_eq n] : (1 : matrix n n R).to_lin = linear_map.id :=
by { ext, simp }

end matrix

namespace linear_map

variables {R : Type v} [comm_ring R]

/-- The linear map from linear maps (n → R) →ₗ[R] (m → R) to matrix m n R. -/
def to_matrixₗ [decidable_eq n] : ((n → R) →ₗ[R] (m → R)) →ₗ[R] matrix m n R :=
begin
  refine linear_map.mk (λ f i j, f (λ n, ite (j = n) 1 0) i) _ _,
  { assume f g, simp only [add_apply], refl },
  { assume f g, simp only [smul_apply], refl }
end

/-- The map from linear maps (n → R) →ₗ[R] (m → R) to matrix m n R. -/
def to_matrix [decidable_eq n] : ((n → R) →ₗ[R] (m → R)) → matrix m n R := to_matrixₗ.to_fun

@[simp] lemma to_matrix_id [decidable_eq n] :
  (@linear_map.id _ (n → R) _ _ _).to_matrix = 1 :=
by { ext, simp [to_matrix, to_matrixₗ, matrix.one_val, eq_comm] }

theorem to_matrix_of_equiv {p q : Type*} [fintype p] [fintype q] [decidable_eq n] [decidable_eq q]
  (e₁ : m ≃ p) (e₂ : n ≃ q) (f : (q → R) →ₗ[R] (p → R)) (i j) :
  to_matrix f (e₁ i) (e₂ j) = to_matrix (linear_equiv.arrow_congr
      (linear_map.fun_congr_left R R e₂)
      (linear_map.fun_congr_left R R e₁) f) i j :=
show f (λ k : q, ite (e₂ j = k) 1 0) (e₁ i) = f (λ k : q, ite (j = e₂.symm k) 1 0) (e₁ i),
by { congr' 1, ext, congr' 1, rw equiv.eq_symm_apply }

end linear_map

section linear_equiv_matrix

variables {R : Type v} [comm_ring R] [decidable_eq n]

open finsupp matrix linear_map

/-- to_lin is the left inverse of to_matrix. -/
lemma to_matrix_to_lin {f : (n → R) →ₗ[R] (m → R)} :
  to_lin (to_matrix f) = f :=
begin
  ext : 1,
  -- Show that the two sides are equal by showing that they are equal on a basis
  convert linear_eq_on (set.range _) _ (is_basis.mem_span (@pi.is_basis_fun R n _ _) _),
  assume e he,
  rw [@std_basis_eq_single R _ _ _ 1] at he,
  cases (set.mem_range.mp he) with i h,
  ext j,
  change ∑ k, (f (λ l, ite (k = l) 1 0)) j * (e k) = _,
  rw [←h],
  conv_lhs { congr, skip, funext,
    rw [mul_comm, ←smul_eq_mul, ←pi.smul_apply, ←linear_map.map_smul],
    rw [show _ = ite (i = k) (1:R) 0, by convert single_apply],
    rw [show f (ite (i = k) (1:R) 0 • (λ l, ite (k = l) 1 0)) = ite (i = k) (f _) 0,
      { split_ifs, { rw [one_smul] }, { rw [zero_smul], exact linear_map.map_zero f } }] },
  convert finset.sum_eq_single i _ _,
  { rw [if_pos rfl], convert rfl, ext, congr },
  { assume _ _ hbi, rw [if_neg $ ne.symm hbi], refl },
  { assume hi, exact false.elim (hi $ finset.mem_univ i) }
end

/-- to_lin is the right inverse of to_matrix. -/
lemma to_lin_to_matrix {M : matrix m n R} : to_matrix (to_lin M) = M :=
begin
  ext,
  change ∑ y, M i y * ite (j = y) 1 0 = M i j,
  have h1 : (λ y, M i y * ite (j = y) 1 0) = (λ y, ite (j = y) (M i y) 0),
    { ext, split_ifs, exact mul_one _, exact ring.mul_zero _ },
  have h2 : ∑ y, ite (j = y) (M i y) 0 = ∑ y in {j}, ite (j = y) (M i y) 0,
    { refine (finset.sum_subset _ _).symm,
      { intros _ H, rwa finset.mem_singleton.1 H, exact finset.mem_univ _ },
      { exact λ _ _ H, if_neg (mt (finset.mem_singleton.2 ∘ eq.symm) H) } },
  rw [h1, h2, finset.sum_singleton],
  exact if_pos rfl
end

/-- Linear maps (n → R) →ₗ[R] (m → R) are linearly equivalent to matrix  m n R. -/
def linear_equiv_matrix' : ((n → R) →ₗ[R] (m → R)) ≃ₗ[R] matrix m n R :=
{ to_fun := to_matrix,
  inv_fun := to_lin,
  right_inv := λ _, to_lin_to_matrix,
  left_inv := λ _, to_matrix_to_lin,
  map_add' := to_matrixₗ.map_add,
  map_smul' := to_matrixₗ.map_smul }

@[simp] lemma linear_equiv_matrix'_apply (f : (n → R) →ₗ[R] (m → R)) :
  linear_equiv_matrix' f = to_matrix f := rfl

/-- Given a basis of two modules M₁ and M₂ over a commutative ring R, we get a linear equivalence
between linear maps M₁ →ₗ M₂ and matrices over R indexed by the bases. -/
def linear_equiv_matrix {ι κ M₁ M₂ : Type*}
  [add_comm_group M₁] [module R M₁]
  [add_comm_group M₂] [module R M₂]
  [fintype ι] [decidable_eq ι] [fintype κ]
  {v₁ : ι → M₁} {v₂ : κ → M₂} (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂) :
  (M₁ →ₗ[R] M₂) ≃ₗ[R] matrix κ ι R :=
linear_equiv.trans (linear_equiv.arrow_congr (equiv_fun_basis hv₁) (equiv_fun_basis hv₂)) linear_equiv_matrix'

open_locale classical

theorem linear_equiv_matrix_range {ι κ M₁ M₂ : Type*}
  [add_comm_group M₁] [module R M₁]
  [add_comm_group M₂] [module R M₂]
  [fintype ι] [fintype κ]
  {v₁ : ι → M₁} {v₂ : κ → M₂} (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂) (f : M₁ →ₗ[R] M₂) (k i) :
  linear_equiv_matrix hv₁.range hv₂.range f ⟨v₂ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_equiv_matrix hv₁ hv₂ f k i :=
if H : (0 : R) = 1 then @subsingleton.elim _ (subsingleton_of_zero_eq_one R H) _ _ else
begin
  simp_rw [linear_equiv_matrix, linear_equiv.trans_apply, linear_equiv_matrix'_apply,
    ← equiv.of_injective_apply _ (hv₁.injective H), ← equiv.of_injective_apply _ (hv₂.injective H),
    to_matrix_of_equiv, ← linear_equiv.trans_apply, linear_equiv.arrow_congr_trans], congr' 3;
  refine function.left_inverse.injective linear_equiv.symm_symm _; ext x;
  simp_rw [linear_equiv.symm_trans_apply, equiv_fun_basis_symm_apply, fun_congr_left_symm,
    fun_congr_left_apply, fun_left_apply],
  convert (finset.sum_equiv (equiv.of_injective _ (hv₁.injective H)) _).symm,
  simp_rw [equiv.symm_apply_apply, equiv.of_injective_apply, subtype.coe_mk],
  convert (finset.sum_equiv (equiv.of_injective _ (hv₂.injective H)) _).symm,
  simp_rw [equiv.symm_apply_apply, equiv.of_injective_apply, subtype.coe_mk]
end

end linear_equiv_matrix

namespace matrix
open_locale matrix

lemma comp_to_matrix_mul {R : Type v} [comm_ring R] [decidable_eq l] [decidable_eq m]
  (f : (m → R) →ₗ[R] (n → R)) (g : (l → R) →ₗ[R] (m → R)) :
  (f.comp g).to_matrix = f.to_matrix ⬝ g.to_matrix :=
suffices (f.comp g) = (f.to_matrix ⬝ g.to_matrix).to_lin, by rw [this, to_lin_to_matrix],
by rw [mul_to_lin, to_matrix_to_lin, to_matrix_to_lin]

lemma linear_equiv_matrix_comp {R ι κ μ M₁ M₂ M₃ : Type*} [comm_ring R]
  [add_comm_group M₁] [module R M₁]
  [add_comm_group M₂] [module R M₂]
  [add_comm_group M₃] [module R M₃]
  [fintype ι] [decidable_eq ι] [fintype κ] [decidable_eq κ] [fintype μ]
  {v₁ : ι → M₁} {v₂ : κ → M₂} {v₃ : μ → M₃}
  (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂) (hv₃ : is_basis R v₃)
  (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
  linear_equiv_matrix hv₁ hv₃ (f.comp g) =
  linear_equiv_matrix hv₂ hv₃ f ⬝ linear_equiv_matrix hv₁ hv₂ g :=
by simp_rw [linear_equiv_matrix, linear_equiv.trans_apply, linear_equiv_matrix'_apply,
    linear_equiv.arrow_congr_comp _ (equiv_fun_basis hv₂), comp_to_matrix_mul]

lemma linear_equiv_matrix_mul {R M ι : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [fintype ι] [decidable_eq ι]
  {b : ι → M} (hb : is_basis R b) (f g : M →ₗ[R] M) :
  linear_equiv_matrix hb hb (f * g) = linear_equiv_matrix hb hb f * linear_equiv_matrix hb hb g :=
linear_equiv_matrix_comp hb hb hb f g

section trace

variables {R : Type v} {M : Type w} [ring R] [add_comm_group M] [module R M]

/--
The diagonal of a square matrix.
-/
def diag (n : Type u) (R : Type v) (M : Type w)
  [ring R] [add_comm_group M] [module R M] [fintype n] : (matrix n n M) →ₗ[R] n → M :=
{ to_fun    := λ A i, A i i,
  map_add'  := by { intros, ext, refl, },
  map_smul' := by { intros, ext, refl, } }

@[simp] lemma diag_apply (A : matrix n n M) (i : n) : diag n R M A i = A i i := rfl

@[simp] lemma diag_one [decidable_eq n] :
  diag n R R 1 = λ i, 1 := by { dunfold diag, ext, simp [one_val_eq] }

@[simp] lemma diag_transpose (A : matrix n n M) : diag n R M Aᵀ = diag n R M A := rfl

/--
The trace of a square matrix.
-/
def trace (n : Type u) (R : Type v) (M : Type w)
  [ring R] [add_comm_group M] [module R M] [fintype n] : (matrix n n M) →ₗ[R] M :=
{ to_fun    := λ A, ∑ i, diag n R M A i,
  map_add'  := by { intros, apply finset.sum_add_distrib, },
  map_smul' := by { intros, simp [finset.smul_sum], } }

@[simp] lemma trace_diag (A : matrix n n M) : trace n R M A = ∑ i, diag n R M A i := rfl

@[simp] lemma trace_one [decidable_eq n] :
  trace n R R 1 = fintype.card n :=
have h : trace n R R 1 = ∑ i, diag n R R 1 i := rfl,
by simp_rw [h, diag_one, finset.sum_const, nsmul_one]; refl

@[simp] lemma trace_transpose (A : matrix n n M) : trace n R M Aᵀ = trace n R M A := rfl

@[simp] lemma trace_transpose_mul (A : matrix m n R) (B : matrix n m R) :
  trace n R R (Aᵀ ⬝ Bᵀ) = trace m R R (A ⬝ B) := finset.sum_comm

lemma trace_mul_comm {S : Type v} [comm_ring S] (A : matrix m n S) (B : matrix n m S) :
  trace n S S (B ⬝ A) = trace m S S (A ⬝ B) :=
by rw [←trace_transpose, ←trace_transpose_mul, transpose_mul]

end trace

section ring

variables {R : Type v} [comm_ring R] [decidable_eq n]
open linear_map matrix

lemma proj_diagonal (i : n) (w : n → R) :
  (proj i).comp (to_lin (diagonal w)) = (w i) • proj i :=
by ext j; simp [mul_vec_diagonal]

lemma diagonal_comp_std_basis (w : n → R) (i : n) :
  (diagonal w).to_lin.comp (std_basis R (λ_:n, R) i) = (w i) • std_basis R (λ_:n, R) i :=
begin
  ext a j,
  simp only [linear_map.comp_apply, smul_apply, to_lin_apply, mul_vec_diagonal, smul_apply,
    pi.smul_apply, smul_eq_mul],
  by_cases i = j,
  { subst h },
  { rw [std_basis_ne R (λ_:n, R) _ _ (ne.symm h), _root_.mul_zero, _root_.mul_zero] }
end

lemma diagonal_to_lin (w : n → R) :
  (diagonal w).to_lin = linear_map.pi (λi, w i • linear_map.proj i) :=
by ext v j; simp [mul_vec_diagonal]

/-- An invertible matrix yields a linear equivalence from the free module to itself. -/
def to_linear_equiv (P : matrix n n R) (h : is_unit P) : (n → R) ≃ₗ[R] (n → R) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
{ inv_fun   := P⁻¹.to_lin,
  left_inv  := λ v,
    show (P⁻¹.to_lin.comp P.to_lin) v = v,
    by rw [←matrix.mul_to_lin, P.nonsing_inv_mul h', matrix.to_lin_one, linear_map.id_apply],
  right_inv := λ v,
    show (P.to_lin.comp P⁻¹.to_lin) v = v,
    by rw [←matrix.mul_to_lin, P.mul_nonsing_inv h', matrix.to_lin_one, linear_map.id_apply],
  ..P.to_lin }

@[simp] lemma to_linear_equiv_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv h) : module.End R (n → R)) = P.to_lin := rfl

@[simp] lemma to_linear_equiv_symm_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv h).symm : module.End R (n → R)) = P⁻¹.to_lin := rfl

end ring

section vector_space

variables {K : Type u} [field K] -- maybe try to relax the universe constraint

open linear_map matrix

lemma rank_vec_mul_vec (w : m → K) (v : n → K) :
  rank (vec_mul_vec w v).to_lin ≤ 1 :=
begin
  rw [vec_mul_vec_eq, mul_to_lin],
  refine le_trans (rank_comp_le1 _ _) _,
  refine le_trans (rank_le_domain _) _,
  rw [dim_fun', ← cardinal.fintype_card],
  exact le_refl _
end

lemma ker_diagonal_to_lin [decidable_eq m] (w : m → K) :
  ker (diagonal w).to_lin = (⨆i∈{i | w i = 0 }, range (std_basis K (λi, K) i)) :=
begin
  rw [← comap_bot, ← infi_ker_proj],
  simp only [comap_infi, (ker_comp _ _).symm, proj_diagonal, ker_smul'],
  have : univ ⊆ {i : m | w i = 0} ∪ {i : m | w i = 0}ᶜ, { rw set.union_compl_self },
  exact (supr_range_std_basis_eq_infi_ker_proj K (λi:m, K)
    (disjoint_compl {i | w i = 0}) this (finite.of_fintype _)).symm
end

lemma range_diagonal [decidable_eq m] (w : m → K) :
  (diagonal w).to_lin.range = (⨆ i ∈ {i | w i ≠ 0}, (std_basis K (λi, K) i).range) :=
begin
  dsimp only [mem_set_of_eq],
  rw [← map_top, ← supr_range_std_basis, map_supr],
  congr, funext i,
  rw [← linear_map.range_comp, diagonal_comp_std_basis, ← range_smul']
end

lemma rank_diagonal [decidable_eq m] [decidable_eq K] (w : m → K) :
  rank (diagonal w).to_lin = fintype.card { i // w i ≠ 0 } :=
begin
  have hu : univ ⊆ {i : m | w i = 0}ᶜ ∪ {i : m | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : m | w i ≠ 0} {i : m | w i = 0} := (disjoint_compl {i | w i = 0}).symm,
  have h₁ := supr_range_std_basis_eq_infi_ker_proj K (λi:m, K) hd hu (finite.of_fintype _),
  have h₂ := @infi_ker_proj_equiv K _ _ (λi:m, K) _ _ _ _ (by simp; apply_instance) hd hu,
  rw [rank, range_diagonal, h₁, ←@dim_fun' K],
  apply linear_equiv.dim_eq,
  apply h₂,
end

end vector_space

section finite_dimensional

variables {R : Type v} [field R]

instance : finite_dimensional R (matrix m n R) :=
linear_equiv.finite_dimensional (linear_equiv.uncurry R m n).symm

/--
The dimension of the space of finite dimensional matrices
is the product of the number of rows and columns.
-/
@[simp] lemma findim_matrix :
  finite_dimensional.findim R (matrix m n R) = fintype.card m * fintype.card n :=
by rw [@linear_equiv.findim_eq R (matrix m n R) _ _ _ _ _ _ (linear_equiv.uncurry R m n),
       finite_dimensional.findim_fintype_fun_eq_card, fintype.card_prod]

end finite_dimensional

end matrix

namespace linear_map

open_locale matrix

/-- The trace of an endomorphism given a basis. -/
def trace_aux (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] [decidable_eq ι] {b : ι → M} (hb : is_basis R b) :
  (M →ₗ[R] M) →ₗ[R] R :=
(matrix.trace ι R R).comp $ linear_equiv_matrix hb hb

@[simp] lemma trace_aux_def (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] [decidable_eq ι] {b : ι → M} (hb : is_basis R b) (f : M →ₗ[R] M) :
  trace_aux R hb f = matrix.trace ι R R (linear_equiv_matrix hb hb f) :=
rfl

theorem trace_aux_eq' (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] [decidable_eq ι] {b : ι → M} (hb : is_basis R b)
  {κ : Type w} [fintype κ] [decidable_eq κ] {c : κ → M} (hc : is_basis R c) :
  trace_aux R hb = trace_aux R hc :=
linear_map.ext $ λ f,
calc  matrix.trace ι R R (linear_equiv_matrix hb hb f)
    = matrix.trace ι R R (linear_equiv_matrix hb hb ((linear_map.id.comp f).comp linear_map.id)) :
  by rw [linear_map.id_comp, linear_map.comp_id]
... = matrix.trace ι R R (linear_equiv_matrix hc hb linear_map.id ⬝
        linear_equiv_matrix hc hc f ⬝
        linear_equiv_matrix hb hc linear_map.id) :
  by rw [matrix.linear_equiv_matrix_comp _ hc, matrix.linear_equiv_matrix_comp _ hc]
... = matrix.trace κ R R (linear_equiv_matrix hc hc f ⬝
        linear_equiv_matrix hb hc linear_map.id ⬝
        linear_equiv_matrix hc hb linear_map.id) :
  by rw [matrix.mul_assoc, matrix.trace_mul_comm]
... = matrix.trace κ R R (linear_equiv_matrix hc hc ((f.comp linear_map.id).comp linear_map.id)) :
  by rw [matrix.linear_equiv_matrix_comp _ hb, matrix.linear_equiv_matrix_comp _ hc]
... = matrix.trace κ R R (linear_equiv_matrix hc hc f) :
  by rw [linear_map.comp_id, linear_map.comp_id]

open_locale classical

theorem trace_aux_range (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] {b : ι → M} (hb : is_basis R b) :
  trace_aux R hb.range = trace_aux R hb :=
linear_map.ext $ λ f, if H : 0 = 1 then @subsingleton.elim _ (subsingleton_of_zero_eq_one R H) _ _ else
begin
  change ∑ i : set.range b, _ = ∑ i : ι, _, simp_rw [matrix.diag_apply], symmetry,
  convert finset.sum_equiv (equiv.of_injective _ $ hb.injective H) _, ext i,
  exact (linear_equiv_matrix_range hb hb f i i).symm
end

/-- where `ι` and `κ` can reside in different universes -/
theorem trace_aux_eq (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type*} [fintype ι] [decidable_eq ι] {b : ι → M} (hb : is_basis R b)
  {κ : Type*} [fintype κ] [decidable_eq κ] {c : κ → M} (hc : is_basis R c) :
  trace_aux R hb = trace_aux R hc :=
calc  trace_aux R hb
    = trace_aux R hb.range : by { rw trace_aux_range R hb, congr }
... = trace_aux R hc.range : trace_aux_eq' _ _ _
... = trace_aux R hc : by { rw trace_aux_range R hc, congr }

/-- Trace of an endomorphism independent of basis. -/
def trace (R : Type u) [comm_ring R] (M : Type v) [add_comm_group M] [module R M] :
  (M →ₗ[R] M) →ₗ[R] R :=
if H : ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M)
then trace_aux R (classical.some_spec H)
else 0

theorem trace_eq_matrix_trace (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] {b : ι → M} (hb : is_basis R b) (f : M →ₗ[R] M) :
  trace R M f = matrix.trace ι R R (linear_equiv_matrix hb hb f) :=
have ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M),
from ⟨finset.univ.image b,
  by { rw [finset.coe_image, finset.coe_univ, set.image_univ], exact hb.range }⟩,
by { rw [trace, dif_pos this, ← trace_aux_def], congr' 1, apply trace_aux_eq }

theorem trace_mul_comm (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) :=
if H : ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M) then let ⟨s, hb⟩ := H in
by { simp_rw [trace_eq_matrix_trace R hb, matrix.linear_equiv_matrix_mul], apply matrix.trace_mul_comm }
else by rw [trace, dif_neg H, linear_map.zero_apply, linear_map.zero_apply]

end linear_map

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def alg_equiv_matrix' {R : Type v} [comm_ring R] [decidable_eq n] :
  module.End R (n → R) ≃ₐ[R] matrix n n R :=
{ map_mul'  := matrix.comp_to_matrix_mul,
  map_add'  := linear_equiv_matrix'.map_add,
  commutes' := λ r, by { change (r • (linear_map.id : module.End R _)).to_matrix = r • 1,
                         rw ←linear_map.to_matrix_id, refl, },
  ..linear_equiv_matrix' }

/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def linear_equiv.alg_conj {R : Type v} [comm_ring R] {M₁ M₂ : Type*}
  [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] (e : M₁ ≃ₗ[R] M₂) :
  module.End R M₁ ≃ₐ[R] module.End R M₂ :=
{ map_mul'  := λ f g, by apply e.arrow_congr_comp,
  map_add'  := e.conj.map_add,
  commutes' := λ r, by { change e.conj (r • linear_map.id) = r • linear_map.id,
                         rw [linear_equiv.map_smul, linear_equiv.conj_id], },
  ..e.conj }

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def alg_equiv_matrix {R : Type v} {M : Type w}
  [comm_ring R] [add_comm_group M] [module R M] [decidable_eq n] {b : n → M} (h : is_basis R b) :
  module.End R M ≃ₐ[R] matrix n n R :=
(equiv_fun_basis h).alg_conj.trans alg_equiv_matrix'
