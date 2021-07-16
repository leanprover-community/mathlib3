/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.char_poly.coeff
import linear_algebra.determinant
import ring_theory.power_basis

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/

universes u v w

variables {R S T : Type*} [integral_domain R] [integral_domain S] [integral_domain T]
variables [algebra R S] [algebra R T]
variables {K L F : Type*} [field K] [field L] [field F]
variables [algebra K L] [algebra L F] [algebra K F]
variables {ι : Type w} [fintype ι]

open finite_dimensional
open linear_map
open matrix

open_locale big_operators
open_locale matrix

namespace algebra

variables (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
linear_map.det.comp (lmul R S).to_ring_hom.to_monoid_hom

@[simp] lemma norm_apply (x : S) : norm R x = linear_map.det (lmul R S x) := rfl

lemma norm_eq_one_of_not_exists_basis
  (h : ¬ ∃ (s : finset S), nonempty (basis s R S)) (x : S) : norm R x = 1 :=
by { rw [norm_apply, linear_map.det], split_ifs with h, refl }

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma norm_eq_matrix_det [decidable_eq ι] (b : basis ι R S) (s : S) :
  norm R s = matrix.det (algebra.left_mul_matrix b s) :=
by rw [norm_apply, ← linear_map.det_to_matrix b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`. -/
lemma norm_algebra_map_of_basis (b : basis ι R S) (x : R) :
  norm R (algebra_map R S x) = x ^ fintype.card ι :=
begin
  haveI := classical.dec_eq ι,
  rw [norm_apply, ← det_to_matrix b, lmul_algebra_map],
  convert @det_diagonal _ _ _ _ _ (λ (i : ι), x),
  { ext i j, rw [to_matrix_lsmul, matrix.diagonal] },
  { rw [finset.prod_const, finset.card_univ] }
end

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
lemma norm_algebra_map (x : K) : norm K (algebra_map K L x) = x ^ finrank K L :=
begin
  by_cases H : ∃ (s : finset L), nonempty (basis s K L),
  { rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some] },
  { rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zero],
    rintros ⟨s, ⟨b⟩⟩,
    exact H ⟨s, ⟨b⟩⟩ },
end

section eq_prod_roots

lemma norm_gen_eq_prod_roots [algebra K S] (pb : power_basis K S)
  (hf : (minpoly K pb.gen).splits (algebra_map K F)) :
  algebra_map K F (norm K pb.gen) =
    ((minpoly K pb.gen).map (algebra_map K F)).roots.prod :=
begin
  -- Write the LHS as the 0'th coefficient of `minpoly K pb.gen`
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_char_poly_coeff, char_poly_left_mul_matrix,
      ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_neg, ring_hom.map_one,
      ← polynomial.coeff_map, fintype.card_fin],
  -- Rewrite `minpoly K pb.gen` as a product over the roots.
  conv_lhs { rw polynomial.eq_prod_roots_of_splits hf },
  rw [polynomial.coeff_C_mul, polynomial.coeff_zero_multiset_prod, multiset.map_map,
      (minpoly.monic pb.is_integral_gen).leading_coeff, ring_hom.map_one, one_mul],
  -- Incorporate the `-1` from the `char_poly` back into the product.
  rw [← multiset.prod_repeat (-1 : F), ← pb.nat_degree_minpoly,
      polynomial.nat_degree_eq_card_roots hf, ← multiset.map_const, ← multiset.prod_map_mul],
  -- And conclude that both sides are the same.
  congr, convert multiset.map_id _, ext f, simp
end

end eq_prod_roots

end algebra
