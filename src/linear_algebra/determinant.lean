/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.finite_dimensional
import linear_algebra.general_linear_group
import linear_algebra.matrix.reindex
import tactic.field_simp
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.basis

/-!
# Determinant of families of vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the determinant of an endomorphism, and of a family of vectors
with respect to some basis. For the determinant of a matrix, see the file
`linear_algebra.matrix.determinant`.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `basis.det`: the determinant of a family of vectors with respect to a basis,
   as a multilinear map
 * `linear_map.det`: the determinant of an endomorphism `f : End R M` as a
   multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
   result is `1` instead)
 * `linear_equiv.det`: the determinant of an isomorphism `f : M ≃ₗ[R] M` as a
   multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
   result is `1` instead)

## Tags

basis, det, determinant
-/

noncomputable theory

open_locale big_operators
open_locale matrix

open linear_map
open submodule

universes u v w

open linear_map matrix set function

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {M' : Type*} [add_comm_group M'] [module R M']
variables {ι : Type*} [decidable_eq ι] [fintype ι]
variables (e : basis ι R M)

section conjugate

variables {A : Type*} [comm_ring A]
variables {m n : Type*} [fintype m] [fintype n]

/-- If `R^m` and `R^n` are linearly equivalent, then `m` and `n` are also equivalent. -/
def equiv_of_pi_lequiv_pi {R : Type*} [comm_ring R] [nontrivial R]
  (e : (m → R) ≃ₗ[R] (n → R)) : m ≃ n :=
basis.index_equiv (basis.of_equiv_fun e.symm) (pi.basis_fun _ _)

namespace matrix

/-- If `M` and `M'` are each other's inverse matrices, they are square matrices up to
equivalence of types. -/
def index_equiv_of_inv [nontrivial A] [decidable_eq m] [decidable_eq n]
  {M : matrix m n A} {M' : matrix n m A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  m ≃ n :=
equiv_of_pi_lequiv_pi (to_lin'_of_inv hMM' hM'M)

lemma det_comm [decidable_eq n] (M N : matrix n n A) : det (M ⬝ N) = det (N ⬝ M) :=
by rw [det_mul, det_mul, mul_comm]

/-- If there exists a two-sided inverse `M'` for `M` (indexed differently),
then `det (N ⬝ M) = det (M ⬝ N)`. -/
lemma det_comm' [decidable_eq m] [decidable_eq n]
  {M : matrix n m A} {N : matrix m n A} {M' : matrix m n A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  det (M ⬝ N) = det (N ⬝ M) :=
begin
  nontriviality A,
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := index_equiv_of_inv hMM' hM'M,
  rw [← det_submatrix_equiv_self e, ← submatrix_mul_equiv _ _ _ (equiv.refl n) _, det_comm,
    submatrix_mul_equiv, equiv.coe_refl, submatrix_id_id]
end

/-- If `M'` is a two-sided inverse for `M` (indexed differently), `det (M ⬝ N ⬝ M') = det N`.

See `matrix.det_conj` and `matrix.det_conj'` for the case when `M' = M⁻¹` or vice versa. -/
lemma det_conj_of_mul_eq_one [decidable_eq m] [decidable_eq n]
  {M : matrix m n A} {M' : matrix n m A} {N : matrix n n A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  det (M ⬝ N ⬝ M') = det N :=
by rw [← det_comm' hM'M hMM', ← matrix.mul_assoc, hM'M, matrix.one_mul]

end matrix

end conjugate

namespace linear_map

/-! ### Determinant of a linear map -/

variables {A : Type*} [comm_ring A] [module A M]
variables {κ : Type*} [fintype κ]

/-- The determinant of `linear_map.to_matrix` does not depend on the choice of basis. -/
lemma det_to_matrix_eq_det_to_matrix [decidable_eq κ]
  (b : basis ι A M) (c : basis κ A M) (f : M →ₗ[A] M) :
  det (linear_map.to_matrix b b f) = det (linear_map.to_matrix c c f) :=
by rw [← linear_map_to_matrix_mul_basis_to_matrix c b c,
       ← basis_to_matrix_mul_linear_map_to_matrix b c b,
       matrix.det_conj_of_mul_eq_one]; rw [basis.to_matrix_mul_to_matrix, basis.to_matrix_self]

/-- The determinant of an endomorphism given a basis.

See `linear_map.det` for a version that populates the basis non-computably.

Although the `trunc (basis ι A M)` parameter makes it slightly more convenient to switch bases,
there is no good way to generalize over universe parameters, so we can't fully state in `det_aux`'s
type that it does not depend on the choice of basis. Instead you can use the `det_aux_def'` lemma,
or avoid mentioning a basis at all using `linear_map.det`.
-/
@[irreducible] def det_aux : trunc (basis ι A M) → (M →ₗ[A] M) →* A :=
trunc.lift
  (λ b : basis ι A M,
    (det_monoid_hom).comp (to_matrix_alg_equiv b : (M →ₗ[A] M) →* matrix ι ι A))
  (λ b c, monoid_hom.ext $ det_to_matrix_eq_det_to_matrix b c)

/-- Unfold lemma for `det_aux`.

See also `det_aux_def'` which allows you to vary the basis.
-/
lemma det_aux_def (b : basis ι A M) (f : M →ₗ[A] M) :
  linear_map.det_aux (trunc.mk b) f = matrix.det (linear_map.to_matrix b b f) :=
by  { rw [det_aux], refl }

lemma det_aux_def' {ι' : Type*} [fintype ι'] [decidable_eq ι']
  (tb : trunc $ basis ι A M) (b' : basis ι' A M) (f : M →ₗ[A] M) :
  linear_map.det_aux tb f = matrix.det (linear_map.to_matrix b' b' f) :=
by { apply trunc.induction_on tb, intro b, rw [det_aux_def, det_to_matrix_eq_det_to_matrix b b'] }

@[simp]
lemma det_aux_id (b : trunc $ basis ι A M) : linear_map.det_aux b (linear_map.id) = 1 :=
(linear_map.det_aux b).map_one

@[simp]
lemma det_aux_comp (b : trunc $ basis ι A M) (f g : M →ₗ[A] M) :
  linear_map.det_aux b (f.comp g) = linear_map.det_aux b f * linear_map.det_aux b g :=
(linear_map.det_aux b).map_mul f g

section
open_locale classical

-- Discourage the elaborator from unfolding `det` and producing a huge term by marking it
-- as irreducible.
/-- The determinant of an endomorphism independent of basis.

If there is no finite basis on `M`, the result is `1` instead.
-/
@[irreducible] protected def det : (M →ₗ[A] M) →* A :=
if H : ∃ (s : finset M), nonempty (basis s A M)
then linear_map.det_aux (trunc.mk H.some_spec.some)
else 1

lemma coe_det [decidable_eq M] : ⇑(linear_map.det : (M →ₗ[A] M) →* A) =
  if H : ∃ (s : finset M), nonempty (basis s A M)
  then linear_map.det_aux (trunc.mk H.some_spec.some)
  else 1 :=
by { ext, unfold linear_map.det,
     split_ifs,
     { congr }, -- use the correct `decidable_eq` instance
     refl }

end

-- Auxiliary lemma, the `simp` normal form goes in the other direction
-- (using `linear_map.det_to_matrix`)
lemma det_eq_det_to_matrix_of_finset [decidable_eq M]
  {s : finset M} (b : basis s A M) (f : M →ₗ[A] M) :
  f.det = matrix.det (linear_map.to_matrix b b f) :=
have ∃ (s : finset M), nonempty (basis s A M),
from ⟨s, ⟨b⟩⟩,
by rw [linear_map.coe_det, dif_pos, det_aux_def' _ b]; assumption

@[simp] lemma det_to_matrix
  (b : basis ι A M) (f : M →ₗ[A] M) :
  matrix.det (to_matrix b b f) = f.det :=
by { haveI := classical.dec_eq M,
     rw [det_eq_det_to_matrix_of_finset b.reindex_finset_range, det_to_matrix_eq_det_to_matrix b] }

@[simp] lemma det_to_matrix' {ι : Type*} [fintype ι] [decidable_eq ι]
  (f : (ι → A) →ₗ[A] (ι → A)) :
  det f.to_matrix' = f.det :=
by simp [← to_matrix_eq_to_matrix']

@[simp] lemma det_to_lin (b : basis ι R M) (f : matrix ι ι R) :
  linear_map.det (matrix.to_lin b b f) = f.det :=
by rw [← linear_map.det_to_matrix b, linear_map.to_matrix_to_lin]

@[simp] lemma det_to_lin' (f : matrix ι ι R) :
  linear_map.det (f.to_lin') = f.det :=
by simp only [← to_lin_eq_to_lin', det_to_lin]

/-- To show `P f.det` it suffices to consider `P (to_matrix _ _ f).det` and `P 1`. -/
@[elab_as_eliminator]
lemma det_cases [decidable_eq M] {P : A → Prop} (f : M →ₗ[A] M)
  (hb : ∀ (s : finset M) (b : basis s A M), P (to_matrix b b f).det) (h1 : P 1) :
  P f.det :=
begin
  unfold linear_map.det,
  split_ifs with h,
  { convert hb _ h.some_spec.some,
    apply det_aux_def' },
  { exact h1 }
end

@[simp]
lemma det_comp (f g : M →ₗ[A] M) : (f.comp g).det = f.det * g.det :=
linear_map.det.map_mul f g

@[simp]
lemma det_id : (linear_map.id : M →ₗ[A] M).det = 1 :=
linear_map.det.map_one

/-- Multiplying a map by a scalar `c` multiplies its determinant by `c ^ dim M`. -/
@[simp] lemma det_smul {𝕜 : Type*} [field 𝕜] {M : Type*} [add_comm_group M] [module 𝕜 M]
  (c : 𝕜) (f : M →ₗ[𝕜] M) :
  linear_map.det (c • f) = c ^ (finite_dimensional.finrank 𝕜 M) * linear_map.det f :=
begin
  by_cases H : ∃ (s : finset M), nonempty (basis s 𝕜 M),
  { haveI : finite_dimensional 𝕜 M,
    { rcases H with ⟨s, ⟨hs⟩⟩, exact finite_dimensional.of_fintype_basis hs },
    simp only [← det_to_matrix (finite_dimensional.fin_basis 𝕜 M), linear_equiv.map_smul,
              fintype.card_fin, det_smul] },
  { classical,
    have : finite_dimensional.finrank 𝕜 M = 0 := finrank_eq_zero_of_not_exists_basis H,
    simp [coe_det, H, this] }
end

lemma det_zero' {ι : Type*} [finite ι] [nonempty ι] (b : basis ι A M) :
  linear_map.det (0 : M →ₗ[A] M) = 0 :=
by { haveI := classical.dec_eq ι, casesI nonempty_fintype ι,
     rwa [← det_to_matrix b, linear_equiv.map_zero, det_zero] }

/-- In a finite-dimensional vector space, the zero map has determinant `1` in dimension `0`,
and `0` otherwise. We give a formula that also works in infinite dimension, where we define
the determinant to be `1`. -/
@[simp] lemma det_zero {𝕜 : Type*} [field 𝕜] {M : Type*} [add_comm_group M] [module 𝕜 M] :
  linear_map.det (0 : M →ₗ[𝕜] M) = (0 : 𝕜) ^ (finite_dimensional.finrank 𝕜 M) :=
by simp only [← zero_smul 𝕜 (1 : M →ₗ[𝕜] M), det_smul, mul_one, monoid_hom.map_one]

lemma det_eq_one_of_subsingleton [subsingleton M] (f : M →ₗ[R] M) : (f : M →ₗ[R] M).det = 1 :=
begin
  have b : basis (fin 0) R M := basis.empty M,
  rw ← f.det_to_matrix b,
  exact matrix.det_is_empty,
end

lemma det_eq_one_of_finrank_eq_zero {𝕜 : Type*} [field 𝕜] {M : Type*} [add_comm_group M]
  [module 𝕜 M] (h : finite_dimensional.finrank 𝕜 M = 0) (f : M →ₗ[𝕜] M) :
  (f : M →ₗ[𝕜] M).det = 1 :=
begin
  classical,
  refine @linear_map.det_cases M  _ 𝕜 _ _ _ (λ t, t = 1) f _ rfl,
  intros s b,
  haveI : is_empty s,
  { rw ← fintype.card_eq_zero_iff,
    exact (finite_dimensional.finrank_eq_card_basis b).symm.trans h },
  exact matrix.det_is_empty
end

/-- Conjugating a linear map by a linear equiv does not change its determinant. -/
@[simp] lemma det_conj {N : Type*} [add_comm_group N] [module A N]
  (f : M →ₗ[A] M) (e : M ≃ₗ[A] N) :
  linear_map.det ((e : M →ₗ[A] N) ∘ₗ (f ∘ₗ (e.symm : N →ₗ[A] M))) = linear_map.det f :=
begin
  classical,
  by_cases H : ∃ (s : finset M), nonempty (basis s A M),
  { rcases H with ⟨s, ⟨b⟩⟩,
    rw [← det_to_matrix b f, ← det_to_matrix (b.map e), to_matrix_comp (b.map e) b (b.map e),
        to_matrix_comp (b.map e) b b, ← matrix.mul_assoc, matrix.det_conj_of_mul_eq_one],
    { rw [← to_matrix_comp, linear_equiv.comp_coe, e.symm_trans_self,
          linear_equiv.refl_to_linear_map, to_matrix_id] },
    { rw [← to_matrix_comp, linear_equiv.comp_coe, e.self_trans_symm,
          linear_equiv.refl_to_linear_map, to_matrix_id] } },
  { have H' : ¬ (∃ (t : finset N), nonempty (basis t A N)),
    { contrapose! H,
      rcases H with ⟨s, ⟨b⟩⟩,
      exact ⟨_, ⟨(b.map e.symm).reindex_finset_range⟩⟩ },
    simp only [coe_det, H, H', pi.one_apply, dif_neg, not_false_iff] }
end

/-- If a linear map is invertible, so is its determinant. -/
lemma is_unit_det {A : Type*} [comm_ring A] [module A M]
  (f : M →ₗ[A] M) (hf : is_unit f) : is_unit f.det :=
begin
  obtain ⟨g, hg⟩ : ∃ g, f.comp g = 1 := hf.exists_right_inv,
  have : linear_map.det f * linear_map.det g = 1,
    by simp only [← linear_map.det_comp, hg, monoid_hom.map_one],
  exact is_unit_of_mul_eq_one _ _ this,
end

/-- If a linear map has determinant different from `1`, then the space is finite-dimensional. -/
lemma finite_dimensional_of_det_ne_one {𝕜 : Type*} [field 𝕜] [module 𝕜 M]
  (f : M →ₗ[𝕜] M) (hf : f.det ≠ 1) : finite_dimensional 𝕜 M :=
begin
  by_cases H : ∃ (s : finset M), nonempty (basis s 𝕜 M),
  { rcases H with ⟨s, ⟨hs⟩⟩, exact finite_dimensional.of_fintype_basis hs },
  { classical,
    simp [linear_map.coe_det, H] at hf,
    exact hf.elim }
end

/-- If the determinant of a map vanishes, then the map is not onto. -/
lemma range_lt_top_of_det_eq_zero {𝕜 : Type*} [field 𝕜] [module 𝕜 M]
  {f : M →ₗ[𝕜] M} (hf : f.det = 0) : f.range < ⊤ :=
begin
  haveI : finite_dimensional 𝕜 M, by simp [f.finite_dimensional_of_det_ne_one, hf],
  contrapose hf,
  simp only [lt_top_iff_ne_top, not_not, ← is_unit_iff_range_eq_top] at hf,
  exact is_unit_iff_ne_zero.1 (f.is_unit_det hf)
end

/-- If the determinant of a map vanishes, then the map is not injective. -/
lemma bot_lt_ker_of_det_eq_zero {𝕜 : Type*} [field 𝕜] [module 𝕜 M]
  {f : M →ₗ[𝕜] M} (hf : f.det = 0) : ⊥ < f.ker :=
begin
  haveI : finite_dimensional 𝕜 M, by simp [f.finite_dimensional_of_det_ne_one, hf],
  contrapose hf,
  simp only [bot_lt_iff_ne_bot, not_not, ← is_unit_iff_ker_eq_bot] at hf,
  exact is_unit_iff_ne_zero.1 (f.is_unit_det hf)
end

end linear_map

namespace linear_equiv

/-- On a `linear_equiv`, the domain of `linear_map.det` can be promoted to `Rˣ`. -/
protected def det : (M ≃ₗ[R] M) →* Rˣ :=
(units.map (linear_map.det : (M →ₗ[R] M) →* R)).comp
  (linear_map.general_linear_group.general_linear_equiv R M).symm.to_monoid_hom

@[simp] lemma coe_det (f : M ≃ₗ[R] M) : ↑f.det = linear_map.det (f : M →ₗ[R] M) := rfl
@[simp] lemma coe_inv_det (f : M ≃ₗ[R] M) : ↑(f.det⁻¹) = linear_map.det (f.symm : M →ₗ[R] M) := rfl

@[simp] lemma det_refl : (linear_equiv.refl R M).det = 1 := units.ext $ linear_map.det_id

@[simp] lemma det_trans (f g : M ≃ₗ[R] M) : (f.trans g).det = g.det * f.det := map_mul _ g f

@[simp] lemma det_symm (f : M ≃ₗ[R] M) : f.symm.det = f.det⁻¹ := map_inv _ f

/-- Conjugating a linear equiv by a linear equiv does not change its determinant. -/
@[simp] lemma det_conj (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M') :
  ((e.symm.trans f).trans e).det = f.det :=
by rw [←units.eq_iff, coe_det, coe_det, ←comp_coe, ←comp_coe, linear_map.det_conj]

end linear_equiv

/-- The determinants of a `linear_equiv` and its inverse multiply to 1. -/
@[simp] lemma linear_equiv.det_mul_det_symm {A : Type*} [comm_ring A] [module A M]
  (f : M ≃ₗ[A] M) : (f : M →ₗ[A] M).det * (f.symm : M →ₗ[A] M).det = 1 :=
by simp [←linear_map.det_comp]

/-- The determinants of a `linear_equiv` and its inverse multiply to 1. -/
@[simp] lemma linear_equiv.det_symm_mul_det {A : Type*} [comm_ring A] [module A M]
  (f : M ≃ₗ[A] M) : (f.symm : M →ₗ[A] M).det * (f : M →ₗ[A] M).det = 1 :=
by simp [←linear_map.det_comp]

-- Cannot be stated using `linear_map.det` because `f` is not an endomorphism.
lemma linear_equiv.is_unit_det (f : M ≃ₗ[R] M') (v : basis ι R M) (v' : basis ι R M') :
  is_unit (linear_map.to_matrix v v' f).det :=
begin
  apply is_unit_det_of_left_inverse,
  simpa using (linear_map.to_matrix_comp v v' v f.symm f).symm
end

/-- Specialization of `linear_equiv.is_unit_det` -/
lemma linear_equiv.is_unit_det' {A : Type*} [comm_ring A] [module A M]
  (f : M ≃ₗ[A] M) : is_unit (linear_map.det (f : M →ₗ[A] M)) :=
is_unit_of_mul_eq_one _ _ f.det_mul_det_symm

/-- The determinant of `f.symm` is the inverse of that of `f` when `f` is a linear equiv. -/
lemma linear_equiv.det_coe_symm {𝕜 : Type*} [field 𝕜] [module 𝕜 M]
  (f : M ≃ₗ[𝕜] M) : (f.symm : M →ₗ[𝕜] M).det = (f : M →ₗ[𝕜] M).det ⁻¹ :=
by field_simp [is_unit.ne_zero f.is_unit_det']

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
@[simps]
def linear_equiv.of_is_unit_det {f : M →ₗ[R] M'} {v : basis ι R M} {v' : basis ι R M'}
  (h : is_unit (linear_map.to_matrix v v' f).det) : M ≃ₗ[R] M' :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := f.map_smul,
  inv_fun := to_lin v' v (to_matrix v v' f)⁻¹,
  left_inv := λ x,
    calc to_lin v' v (to_matrix v v' f)⁻¹ (f x)
        = to_lin v v ((to_matrix v v' f)⁻¹ ⬝ to_matrix v v' f) x :
      by { rw [to_lin_mul v v' v, to_lin_to_matrix, linear_map.comp_apply] }
    ... = x : by simp [h],
  right_inv := λ x,
    calc f (to_lin v' v (to_matrix v v' f)⁻¹ x)
        = to_lin v' v' (to_matrix v v' f ⬝ (to_matrix v v' f)⁻¹) x :
      by { rw [to_lin_mul v' v v', linear_map.comp_apply, to_lin_to_matrix v v'] }
    ... = x : by simp [h] }

@[simp] lemma linear_equiv.coe_of_is_unit_det {f : M →ₗ[R] M'} {v : basis ι R M} {v' : basis ι R M'}
  (h : is_unit (linear_map.to_matrix v v' f).det) :
  (linear_equiv.of_is_unit_det h : M →ₗ[R] M') = f :=
by { ext x, refl }

/-- Builds a linear equivalence from a linear map on a finite-dimensional vector space whose
determinant is nonzero. -/
@[reducible] def linear_map.equiv_of_det_ne_zero
  {𝕜 : Type*} [field 𝕜] {M : Type*} [add_comm_group M] [module 𝕜 M]
  [finite_dimensional 𝕜 M] (f : M →ₗ[𝕜] M) (hf : linear_map.det f ≠ 0) :
  M ≃ₗ[𝕜] M :=
have is_unit (linear_map.to_matrix (finite_dimensional.fin_basis 𝕜 M)
  (finite_dimensional.fin_basis 𝕜 M) f).det :=
    by simp only [linear_map.det_to_matrix, is_unit_iff_ne_zero.2 hf],
linear_equiv.of_is_unit_det this

lemma linear_map.associated_det_of_eq_comp (e : M ≃ₗ[R] M) (f f' : M →ₗ[R] M)
  (h : ∀ x, f x = f' (e x)) : associated f.det f'.det :=
begin
  suffices : associated (f' ∘ₗ ↑e).det f'.det,
  { convert this using 2, ext x, exact h x },
  rw [← mul_one f'.det, linear_map.det_comp],
  exact associated.mul_left _ (associated_one_iff_is_unit.mpr e.is_unit_det')
end

lemma linear_map.associated_det_comp_equiv {N : Type*} [add_comm_group N] [module R N]
  (f : N →ₗ[R] M) (e e' : M ≃ₗ[R] N) :
  associated (f ∘ₗ ↑e).det (f ∘ₗ ↑e').det :=
begin
  refine linear_map.associated_det_of_eq_comp (e.trans e'.symm) _ _ _,
  intro x,
  simp only [linear_map.comp_apply, linear_equiv.coe_coe, linear_equiv.trans_apply,
             linear_equiv.apply_symm_apply],
end

/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
def basis.det : alternating_map R M R ι :=
{ to_fun := λ v, det (e.to_matrix v),
  map_add' := begin
    intros inst v i x y,
    cases subsingleton.elim inst ‹_›,
    simp only [e.to_matrix_update, linear_equiv.map_add, finsupp.coe_add],
    exact det_update_column_add _ _ _ _,
  end,
  map_smul' := begin
    intros inst u i c x,
    cases subsingleton.elim inst ‹_›,
    simp only [e.to_matrix_update, algebra.id.smul_eq_mul, linear_equiv.map_smul],
    apply det_update_column_smul
  end,
  map_eq_zero_of_eq' := begin
    intros v i j h hij,
    rw [←function.update_eq_self i v, h, ←det_transpose, e.to_matrix_update,
        ←update_row_transpose, ←e.to_matrix_transpose_apply],
    apply det_zero_of_row_eq hij,
    rw [update_row_ne hij.symm, update_row_self],
  end }

lemma basis.det_apply (v : ι → M) : e.det v = det (e.to_matrix v) := rfl

lemma basis.det_self : e.det e = 1 :=
by simp [e.det_apply]

@[simp] lemma basis.det_is_empty [is_empty ι] : e.det = alternating_map.const_of_is_empty R M 1 :=
begin
  ext v,
  exact matrix.det_is_empty,
end

/-- `basis.det` is not the zero map. -/
lemma basis.det_ne_zero [nontrivial R] : e.det ≠ 0 :=
λ h, by simpa [h] using e.det_self

lemma is_basis_iff_det {v : ι → M} :
  linear_independent R v ∧ span R (set.range v) = ⊤ ↔ is_unit (e.det v) :=
begin
  split,
  { rintro ⟨hli, hspan⟩,
    set v' := basis.mk hli hspan.ge with v'_eq,
    rw e.det_apply,
    convert linear_equiv.is_unit_det (linear_equiv.refl _ _) v' e using 2,
    ext i j,
    simp },
  { intro h,
    rw [basis.det_apply, basis.to_matrix_eq_to_matrix_constr] at h,
    set v' := basis.map e (linear_equiv.of_is_unit_det h) with v'_def,
    have : ⇑ v' = v,
    { ext i, rw [v'_def, basis.map_apply, linear_equiv.of_is_unit_det_apply, e.constr_basis] },
    rw ← this,
    exact ⟨v'.linear_independent, v'.span_eq⟩ },
end

lemma basis.is_unit_det (e' : basis ι R M) : is_unit (e.det e') :=
(is_basis_iff_det e).mp ⟨e'.linear_independent, e'.span_eq⟩

/-- Any alternating map to `R` where `ι` has the cardinality of a basis equals the determinant
map with respect to that basis, multiplied by the value of that alternating map on that basis. -/
lemma alternating_map.eq_smul_basis_det (f : alternating_map R M R ι) : f = f e • e.det :=
begin
  refine basis.ext_alternating e (λ i h, _),
  let σ : equiv.perm ι := equiv.of_bijective i (finite.injective_iff_bijective.1 h),
  change f (e ∘ σ) = (f e • e.det) (e ∘ σ),
  simp [alternating_map.map_perm, basis.det_self]
end

@[simp] lemma alternating_map.map_basis_eq_zero_iff {ι : Type*} [finite ι]
  (e : basis ι R M) (f : alternating_map R M R ι) :
  f e = 0 ↔ f = 0 :=
⟨λ h, begin
  casesI nonempty_fintype ι,
  letI := classical.dec_eq ι,
  simpa [h] using f.eq_smul_basis_det e
end, λ h, h.symm ▸ alternating_map.zero_apply _⟩

lemma alternating_map.map_basis_ne_zero_iff {ι : Type*} [finite ι]
  (e : basis ι R M) (f : alternating_map R M R ι) :
  f e ≠ 0 ↔ f ≠ 0 :=
not_congr $ f.map_basis_eq_zero_iff e

variables {A : Type*} [comm_ring A] [module A M]

@[simp] lemma basis.det_comp (e : basis ι A M) (f : M →ₗ[A] M) (v : ι → M) :
  e.det (f ∘ v) = f.det * e.det v :=
by { rw [basis.det_apply, basis.det_apply, ← f.det_to_matrix e, ← matrix.det_mul,
         e.to_matrix_eq_to_matrix_constr (f ∘ v), e.to_matrix_eq_to_matrix_constr v,
         ← to_matrix_comp, e.constr_comp] }

@[simp] lemma basis.det_comp_basis [module A M']
  (b : basis ι A M) (b' : basis ι A M') (f : M →ₗ[A] M') :
  b'.det (f ∘ b) = linear_map.det (f ∘ₗ (b'.equiv b (equiv.refl ι) : M' →ₗ[A] M)) :=
begin
  rw [basis.det_apply, ← linear_map.det_to_matrix b', linear_map.to_matrix_comp _ b,
      matrix.det_mul, linear_map.to_matrix_basis_equiv, matrix.det_one, mul_one],
  congr' 1, ext i j,
  rw [basis.to_matrix_apply, linear_map.to_matrix_apply]
end

lemma basis.det_reindex {ι' : Type*} [fintype ι'] [decidable_eq ι']
  (b : basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
  (b.reindex e).det v = b.det (v ∘ e) :=
by rw [basis.det_apply, basis.to_matrix_reindex', det_reindex_alg_equiv, basis.det_apply]

lemma basis.det_reindex_symm {ι' : Type*} [fintype ι'] [decidable_eq ι']
  (b : basis ι R M) (v : ι → M) (e : ι' ≃ ι) :
  (b.reindex e.symm).det (v ∘ e) = b.det v :=
by rw [basis.det_reindex, function.comp.assoc, e.self_comp_symm, function.comp.right_id]

@[simp]
lemma basis.det_map (b : basis ι R M) (f : M ≃ₗ[R] M') (v : ι → M') :
  (b.map f).det v = b.det (f.symm ∘ v) :=
by { rw [basis.det_apply, basis.to_matrix_map, basis.det_apply] }

lemma basis.det_map' (b : basis ι R M) (f : M ≃ₗ[R] M') :
  (b.map f).det = b.det.comp_linear_map f.symm :=
alternating_map.ext $ b.det_map f

@[simp] lemma pi.basis_fun_det : (pi.basis_fun R ι).det = matrix.det_row_alternating :=
begin
  ext M,
  rw [basis.det_apply, basis.coe_pi_basis_fun.to_matrix_eq_transpose, det_transpose],
end

/-- If we fix a background basis `e`, then for any other basis `v`, we can characterise the
coordinates provided by `v` in terms of determinants relative to `e`. -/
lemma basis.det_smul_mk_coord_eq_det_update {v : ι → M}
  (hli : linear_independent R v) (hsp : ⊤ ≤ span R (range v)) (i : ι) :
  (e.det v) • (basis.mk hli hsp).coord i = e.det.to_multilinear_map.to_linear_map v i :=
begin
  apply (basis.mk hli hsp).ext,
  intros k,
  rcases eq_or_ne k i with rfl | hik;
  simp only [algebra.id.smul_eq_mul, basis.coe_mk, linear_map.smul_apply, linear_map.coe_mk,
    multilinear_map.to_linear_map_apply],
  { rw [basis.mk_coord_apply_eq, mul_one, update_eq_self], congr, },
  { rw [basis.mk_coord_apply_ne hik, mul_zero, eq_comm],
    exact e.det.map_eq_zero_of_eq _ (by simp [hik, function.update_apply]) hik, },
end

/-- If a basis is multiplied columnwise by scalars `w : ι → Rˣ`, then the determinant with respect
to this basis is multiplied by the product of the inverse of these scalars. -/
lemma basis.det_units_smul (e : basis ι R M) (w : ι → Rˣ) :
  (e.units_smul w).det = (↑(∏ i, w i)⁻¹ : R) • e.det :=
begin
  ext f,
  change matrix.det (λ i j, (e.units_smul w).repr (f j) i)
    = (↑(∏ i, w i)⁻¹ : R) • matrix.det (λ i j, e.repr (f j) i),
  simp only [e.repr_units_smul],
  convert matrix.det_mul_column (λ i, (↑((w i)⁻¹) : R)) (λ i j, e.repr (f j) i),
  simp [← finset.prod_inv_distrib]
end

/-- The determinant of a basis constructed by `units_smul` is the product of the given units. -/
@[simp] lemma basis.det_units_smul_self (w : ι → Rˣ) : e.det (e.units_smul w) = ∏ i, w i :=
by simp [basis.det_apply]

/-- The determinant of a basis constructed by `is_unit_smul` is the product of the given units. -/
@[simp] lemma basis.det_is_unit_smul {w : ι → R} (hw : ∀ i, is_unit (w i)) :
  e.det (e.is_unit_smul hw) = ∏ i, w i :=
e.det_units_smul_self _
