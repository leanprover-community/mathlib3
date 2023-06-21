/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.matrix.bilinear_form
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.determinant
import linear_algebra.finite_dimensional
import linear_algebra.vandermonde
import linear_algebra.trace
import field_theory.is_alg_closed.algebraic_closure
import field_theory.primitive_element
import field_theory.galois
import ring_theory.power_basis

/-!
# Trace for (finite) ring extensions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

 * `algebra.trace R S x`: the trace of an element `s` of an `R`-algebra `S`
 * `algebra.trace_form R S`: bilinear form sending `x`, `y` to the trace of `x * y`
 * `algebra.trace_matrix R b`: the matrix whose `(i j)`-th element is the trace of `b i * b j`.
 * `algebra.embeddings_matrix A C b : matrix κ (B →ₐ[A] C) C` is the matrix whose
   `(i, σ)` coefficient is `σ (b i)`.
 * `algebra.embeddings_matrix_reindex A C b e : matrix κ κ C` is the matrix whose `(i, j)`
   coefficient is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ`
   given by a bijection `e : κ ≃ (B →ₐ[A] C)`.

## Main results

 * `trace_algebra_map_of_basis`, `trace_algebra_map`: if `x : K`, then `Tr_{L/K} x = [L : K] x`
 * `trace_trace_of_basis`, `trace_trace`: `Tr_{L/K} (Tr_{F/L} x) = Tr_{F/K} x`
 * `trace_eq_sum_roots`: the trace of `x : K(x)` is the sum of all conjugate roots of `x`
 * `trace_eq_sum_embeddings`: the trace of `x : K(x)` is the sum of all embeddings of `x` into an
   algebraically closed field
 * `trace_form_nondegenerate`: the trace form over a separable extension is a nondegenerate
   bilinear form

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.left_mul_matrix`,
i.e. `linear_map.mul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/

universes u v w z

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables {K L : Type*} [field K] [field L] [algebra K L]
variables {ι κ : Type w} [fintype ι]

open finite_dimensional
open linear_map
open matrix

open_locale big_operators
open_locale matrix

namespace algebra

variables (b : basis ι R S)

variables (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R :=
(linear_map.trace R S).comp (lmul R S).to_linear_map

variables {S}

-- Not a `simp` lemma since there are more interesting ways to rewrite `trace R S x`,
-- for example `trace_trace`
lemma trace_apply (x) : trace R S x = linear_map.trace R S (lmul R S x) := rfl

lemma trace_eq_zero_of_not_exists_basis
  (h : ¬ ∃ (s : finset S), nonempty (basis s R S)) : trace R S = 0 :=
by { ext s, simp [trace_apply, linear_map.trace, h] }

include b

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma trace_eq_matrix_trace [decidable_eq ι] (b : basis ι R S) (s : S) :
  trace R S s = matrix.trace (algebra.left_mul_matrix b s) :=
by { rw [trace_apply, linear_map.trace_eq_matrix_trace _ b, ←to_matrix_lmul_eq], refl }

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
lemma trace_algebra_map_of_basis (x : R) :
  trace R S (algebra_map R S x) = fintype.card ι • x :=
begin
  haveI := classical.dec_eq ι,
  rw [trace_apply, linear_map.trace_eq_matrix_trace R b, matrix.trace],
  convert finset.sum_const _,
  ext i,
  simp [-coe_lmul_eq_mul],
end
omit b

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
lemma trace_algebra_map (x : K) : trace K L (algebra_map K L x) = finrank K L • x :=
begin
  by_cases H : ∃ (s : finset L), nonempty (basis s K L),
  { rw [trace_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some] },
  { simp [trace_eq_zero_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis_finset H] }
end

lemma trace_trace_of_basis [algebra S T] [is_scalar_tower R S T] {ι κ : Type*} [finite ι] [finite κ]
  (b : basis ι R S) (c : basis κ S T) (x : T) :
  trace R S (trace S T x) = trace R T x :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq κ,
  casesI nonempty_fintype ι,
  casesI nonempty_fintype κ,
  rw [trace_eq_matrix_trace (b.smul c), trace_eq_matrix_trace b, trace_eq_matrix_trace c,
      matrix.trace, matrix.trace, matrix.trace,
      ← finset.univ_product_univ, finset.sum_product],
  refine finset.sum_congr rfl (λ i _, _),
  simp only [alg_hom.map_sum, smul_left_mul_matrix, finset.sum_apply, matrix.diag,
      -- The unifier is not smart enough to apply this one by itself:
      finset.sum_apply i _ (λ y, left_mul_matrix b (left_mul_matrix c x y y))]
end

lemma trace_comp_trace_of_basis [algebra S T] [is_scalar_tower R S T] {ι κ : Type*} [finite ι]
  [fintype κ] (b : basis ι R S) (c : basis κ S T) :
  (trace R S).comp ((trace S T).restrict_scalars R) = trace R T :=
by { ext, rw [linear_map.comp_apply, linear_map.restrict_scalars_apply, trace_trace_of_basis b c] }

@[simp]
lemma trace_trace [algebra K T] [algebra L T] [is_scalar_tower K L T]
  [finite_dimensional K L] [finite_dimensional L T] (x : T) :
  trace K L (trace L T x) = trace K T x :=
trace_trace_of_basis (basis.of_vector_space K L) (basis.of_vector_space L T) x

@[simp]
lemma trace_comp_trace [algebra K T] [algebra L T] [is_scalar_tower K L T]
  [finite_dimensional K L] [finite_dimensional L T] :
  (trace K L).comp ((trace L T).restrict_scalars K) = trace K T :=
by { ext, rw [linear_map.comp_apply, linear_map.restrict_scalars_apply, trace_trace] }

@[simp]
lemma trace_prod_apply
  [module.free R S] [module.free R T] [module.finite R S] [module.finite R T]
  (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T x.snd :=
begin
  nontriviality R,
  let f := (lmul R S).to_linear_map.prod_map (lmul R T).to_linear_map,
  have : (lmul R (S × T)).to_linear_map = (prod_map_linear R S T S T R).comp f :=
    linear_map.ext₂ prod.mul_def,
  simp_rw [trace, this],
  exact trace_prod_map' _ _,
end

lemma trace_prod
  [module.free R S] [module.free R T] [module.finite R S] [module.finite R T] :
  trace R (S × T) = (trace R S).coprod (trace R T) :=
linear_map.ext $ λ p, by rw [coprod_apply, trace_prod_apply]

section trace_form

variables (R S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : bilin_form R S :=
(linear_map.compr₂ (lmul R S).to_linear_map (trace R S)).to_bilin

variables {S}

-- This is a nicer lemma than the one produced by `@[simps] def trace_form`.
@[simp] lemma trace_form_apply (x y : S) : trace_form R S x y = trace R S (x * y) := rfl

lemma trace_form_is_symm : (trace_form R S).is_symm :=
λ x y, congr_arg (trace R S) (mul_comm _ _)

lemma trace_form_to_matrix [decidable_eq ι] (i j) :
  bilin_form.to_matrix b (trace_form R S) i j = trace R S (b i * b j) :=
by rw [bilin_form.to_matrix_apply, trace_form_apply]

lemma trace_form_to_matrix_power_basis (h : power_basis R S) :
  bilin_form.to_matrix h.basis (trace_form R S) = of (λ i j, trace R S (h.gen ^ (↑i + ↑j : ℕ))) :=
by { ext, rw [trace_form_to_matrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow] }

end trace_form

end algebra

section eq_sum_roots

open algebra polynomial

variables {F : Type*} [field F]
variables [algebra K S] [algebra K F]

/-- Given `pb : power_basis K S`, the trace of `pb.gen` is `-(minpoly K pb.gen).next_coeff`. -/
lemma power_basis.trace_gen_eq_next_coeff_minpoly [nontrivial S] (pb : power_basis K S) :
  algebra.trace K S pb.gen = -(minpoly K pb.gen).next_coeff :=
begin
  have d_pos : 0 < pb.dim := power_basis.dim_pos pb,
  have d_pos' : 0 < (minpoly K pb.gen).nat_degree, { simpa },
  haveI : nonempty (fin pb.dim) := ⟨⟨0, d_pos⟩⟩,
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_left_mul_matrix,
      ← pb.nat_degree_minpoly, fintype.card_fin, ← next_coeff_of_pos_nat_degree _ d_pos']
end

/-- Given `pb : power_basis K S`, then the trace of `pb.gen` is
`((minpoly K pb.gen).map (algebra_map K F)).roots.sum`. -/
lemma power_basis.trace_gen_eq_sum_roots [nontrivial S] (pb : power_basis K S)
  (hf : (minpoly K pb.gen).splits (algebra_map K F)) :
  algebra_map K F (trace K S pb.gen) =
    ((minpoly K pb.gen).map (algebra_map K F)).roots.sum :=
begin
  rw [power_basis.trace_gen_eq_next_coeff_minpoly, ring_hom.map_neg, ← next_coeff_map
    (algebra_map K F).injective, sum_roots_eq_next_coeff_of_monic_of_split
      ((minpoly.monic (power_basis.is_integral_gen _)).map _)
      ((splits_id_iff_splits _).2 hf), neg_neg]
end

namespace intermediate_field.adjoin_simple

open intermediate_field

lemma trace_gen_eq_zero {x : L} (hx : ¬ is_integral K x) :
  algebra.trace K K⟮x⟯ (adjoin_simple.gen K x) = 0 :=
begin
  rw [trace_eq_zero_of_not_exists_basis, linear_map.zero_apply],
  contrapose! hx,
  obtain ⟨s, ⟨b⟩⟩ := hx,
  refine is_integral_of_mem_of_fg (K⟮x⟯).to_subalgebra _ x _,
  { exact (submodule.fg_iff_finite_dimensional _).mpr (finite_dimensional.of_fintype_basis b) },
  { exact subset_adjoin K _ (set.mem_singleton x) }
end

lemma trace_gen_eq_sum_roots (x : L)
  (hf : (minpoly K x).splits (algebra_map K F)) :
  algebra_map K F (trace K K⟮x⟯ (adjoin_simple.gen K x)) =
    ((minpoly K x).map (algebra_map K F)).roots.sum :=
begin
  have injKxL := (algebra_map K⟮x⟯ L).injective,
  by_cases hx : is_integral K x, swap,
  { simp [minpoly.eq_zero hx, trace_gen_eq_zero hx], },
  have hx' : is_integral K (adjoin_simple.gen K x),
  { rwa [← is_integral_algebra_map_iff injKxL, adjoin_simple.algebra_map_gen],
    apply_instance },
  rw [← adjoin.power_basis_gen hx, (adjoin.power_basis hx).trace_gen_eq_sum_roots];
    rw [adjoin.power_basis_gen hx, minpoly.eq_of_algebra_map_eq injKxL hx'];
    try { simp only [adjoin_simple.algebra_map_gen _ _] },
  exact hf
end

end intermediate_field.adjoin_simple

open intermediate_field

variables (K)

lemma trace_eq_trace_adjoin [finite_dimensional K L] (x : L) :
  algebra.trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (adjoin_simple.gen K x) :=
begin
  rw ← @trace_trace _ _ K K⟮x⟯ _ _ _ _ _ _ _ _ x,
  conv in x { rw ← intermediate_field.adjoin_simple.algebra_map_gen K x },
  rw [trace_algebra_map, linear_map.map_smul_of_tower],
end

variables {K}

lemma trace_eq_sum_roots [finite_dimensional K L]
  {x : L} (hF : (minpoly K x).splits (algebra_map K F)) :
  algebra_map K F (algebra.trace K L x) =
    finrank K⟮x⟯ L • ((minpoly K x).map (algebra_map K _)).roots.sum :=
by rw [trace_eq_trace_adjoin K x, algebra.smul_def, ring_hom.map_mul, ← algebra.smul_def,
    intermediate_field.adjoin_simple.trace_gen_eq_sum_roots _ hF, is_scalar_tower.algebra_map_smul]

end eq_sum_roots

variables {F : Type*} [field F]
variables [algebra R L] [algebra L F] [algebra R F] [is_scalar_tower R L F]

open polynomial

lemma algebra.is_integral_trace [finite_dimensional L F] {x : F} (hx : is_integral R x) :
  is_integral R (algebra.trace L F x) :=
begin
  have hx' : is_integral L x := is_integral_of_is_scalar_tower hx,
  rw [← is_integral_algebra_map_iff (algebra_map L (algebraic_closure F)).injective,
      trace_eq_sum_roots],
  { refine (is_integral.multiset_sum _).nsmul _,
    intros y hy,
    rw mem_roots_map (minpoly.ne_zero hx') at hy,
    use [minpoly R x, minpoly.monic hx],
    rw ← aeval_def at ⊢ hy,
    exact minpoly.aeval_of_is_scalar_tower R x y hy },
  { apply is_alg_closed.splits_codomain },
  { apply_instance }
end

section eq_sum_embeddings

variables [algebra K F] [is_scalar_tower K L F]

open algebra intermediate_field

variables (F) (E : Type*) [field E] [algebra K E]

lemma trace_eq_sum_embeddings_gen
  (pb : power_basis K L)
  (hE : (minpoly K pb.gen).splits (algebra_map K E)) (hfx : (minpoly K pb.gen).separable) :
  algebra_map K E (algebra.trace K L pb.gen) =
    (@@finset.univ (power_basis.alg_hom.fintype pb)).sum (λ σ, σ pb.gen) :=
begin
  letI := classical.dec_eq E,
  rw [pb.trace_gen_eq_sum_roots hE, fintype.sum_equiv pb.lift_equiv', finset.sum_mem_multiset,
      finset.sum_eq_multiset_sum, multiset.to_finset_val,
      multiset.dedup_eq_self.mpr _, multiset.map_id],
  { exact nodup_roots ((separable_map _).mpr hfx) },
  { intro x, refl },
  { intro σ, rw [power_basis.lift_equiv'_apply_coe, id.def] }
end

variables [is_alg_closed E]

lemma sum_embeddings_eq_finrank_mul [finite_dimensional K F] [is_separable K F]
  (pb : power_basis K L) :
  ∑ σ : F →ₐ[K] E, σ (algebra_map L F pb.gen) =
    finrank L F • (@@finset.univ (power_basis.alg_hom.fintype pb)).sum
      (λ σ : L →ₐ[K] E, σ pb.gen) :=
begin
  haveI : finite_dimensional L F := finite_dimensional.right K L F,
  haveI : is_separable L F := is_separable_tower_top_of_is_separable K L F,
  letI : fintype (L →ₐ[K] E) := power_basis.alg_hom.fintype pb,
  letI : ∀ (f : L →ₐ[K] E), fintype (@@alg_hom L F E _ _ _ _ f.to_ring_hom.to_algebra) :=
    _, -- will be solved by unification
  rw [fintype.sum_equiv alg_hom_equiv_sigma (λ (σ : F →ₐ[K] E), _) (λ σ, σ.1 pb.gen),
      ← finset.univ_sigma_univ, finset.sum_sigma, ← finset.sum_nsmul],
  refine finset.sum_congr rfl (λ σ _, _),
  { letI : algebra L E := σ.to_ring_hom.to_algebra,
    simp only [finset.sum_const, finset.card_univ],
    rw alg_hom.card L F E },
  { intros σ,
    simp only [alg_hom_equiv_sigma, equiv.coe_fn_mk, alg_hom.restrict_domain, alg_hom.comp_apply,
         is_scalar_tower.coe_to_alg_hom'] }
end

lemma trace_eq_sum_embeddings [finite_dimensional K L] [is_separable K L]
  {x : L} : algebra_map K E (algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x :=
begin
  have hx := is_separable.is_integral K x,
  rw [trace_eq_trace_adjoin K x, algebra.smul_def, ring_hom.map_mul, ← adjoin.power_basis_gen hx,
      trace_eq_sum_embeddings_gen E (adjoin.power_basis hx) (is_alg_closed.splits_codomain _),
      ← algebra.smul_def, algebra_map_smul],
  { exact (sum_embeddings_eq_finrank_mul L E (adjoin.power_basis hx)).symm },
  { haveI := is_separable_tower_bot_of_is_separable K K⟮x⟯ L,
    exact is_separable.separable K _ }
end

lemma trace_eq_sum_automorphisms (x : L) [finite_dimensional K L] [is_galois K L] :
  algebra_map K L (algebra.trace K L x) = ∑ (σ : L ≃ₐ[K] L), σ x :=
begin
  apply no_zero_smul_divisors.algebra_map_injective L (algebraic_closure L),
  rw map_sum (algebra_map L (algebraic_closure L)),
  rw ← fintype.sum_equiv (normal.alg_hom_equiv_aut K (algebraic_closure L) L),
  { rw ←trace_eq_sum_embeddings (algebraic_closure L),
    { simp only [algebra_map_eq_smul_one, smul_one_smul] },
    { exact is_galois.to_is_separable } },
  { intro σ,
    simp only [normal.alg_hom_equiv_aut, alg_hom.restrict_normal', equiv.coe_fn_mk,
               alg_equiv.coe_of_bijective, alg_hom.restrict_normal_commutes, id.map_eq_id,
               ring_hom.id_apply] },
end

end eq_sum_embeddings

section det_ne_zero

namespace algebra

variables (A : Type u) {B : Type v} (C : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B] [comm_ring C] [algebra A C]

open finset

/-- Given an `A`-algebra `B` and `b`, an `κ`-indexed family of elements of `B`, we define
`trace_matrix A b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
noncomputable
def trace_matrix (b : κ → B) : matrix κ κ A :=
of $ λ i j, trace_form A B (b i) (b j)

-- TODO: set as an equation lemma for `trace_matrix`, see mathlib4#3024
@[simp]
lemma trace_matrix_apply (b : κ → B) (i j) :
  trace_matrix A b i j = trace_form A B (b i) (b j) :=
rfl

lemma trace_matrix_reindex {κ' : Type*} (b : basis κ A B) (f : κ ≃ κ') :
  trace_matrix A (b.reindex f) = reindex f f (trace_matrix A b) :=
by {ext x y, simp}

variables {A}

lemma trace_matrix_of_matrix_vec_mul [fintype κ] (b : κ → B) (P : matrix κ κ A) :
  trace_matrix A ((P.map (algebra_map A B)).vec_mul b) = Pᵀ ⬝ (trace_matrix A b) ⬝ P :=
begin
  ext α β,
  rw [trace_matrix_apply, vec_mul, dot_product, vec_mul, dot_product, matrix.mul_apply,
    bilin_form.sum_left, fintype.sum_congr _ _ (λ (i : κ), @bilin_form.sum_right _ _ _ _ _ _ _ _
    (b i * P.map (algebra_map A B) i α) (λ (y : κ), b y * P.map (algebra_map A B) y β)), sum_comm],
  congr, ext x,
  rw [matrix.mul_apply, sum_mul],
  congr, ext y,
  rw [map_apply, trace_form_apply, mul_comm (b y), ← smul_def],
  simp only [id.smul_eq_mul, ring_hom.id_apply, map_apply, transpose_apply, linear_map.map_smulₛₗ,
    trace_form_apply, algebra.smul_mul_assoc],
  rw [mul_comm (b x), ← smul_def],
  ring_nf,
  simp [mul_comm],
end

lemma trace_matrix_of_matrix_mul_vec [fintype κ] (b : κ → B) (P : matrix κ κ A) :
  trace_matrix A ((P.map (algebra_map A B)).mul_vec b) = P ⬝ (trace_matrix A b) ⬝ Pᵀ :=
begin
  refine add_equiv.injective (transpose_add_equiv _ _ _) _,
  rw [transpose_add_equiv_apply, transpose_add_equiv_apply, ← vec_mul_transpose,
    ← transpose_map, trace_matrix_of_matrix_vec_mul, transpose_transpose, transpose_mul,
    transpose_transpose, transpose_mul]
end

lemma trace_matrix_of_basis [fintype κ] [decidable_eq κ] (b : basis κ A B) :
  trace_matrix A b = bilin_form.to_matrix b (trace_form A B) :=
begin
  ext i j,
  rw [trace_matrix_apply, trace_form_apply, trace_form_to_matrix]
end

lemma trace_matrix_of_basis_mul_vec (b : basis ι A B) (z : B) :
  (trace_matrix A b).mul_vec (b.equiv_fun z) = (λ i, trace A B (z * (b i))) :=
begin
  ext i,
  rw [← col_apply ((trace_matrix A b).mul_vec (b.equiv_fun z)) i unit.star, col_mul_vec,
    matrix.mul_apply, trace_matrix],
  simp only [col_apply, trace_form_apply],
  conv_lhs
  { congr, skip, funext,
    rw [mul_comm _ (b.equiv_fun z _), ← smul_eq_mul, of_apply, ← linear_map.map_smul] },
    rw [← linear_map.map_sum],
    congr,
    conv_lhs
    { congr, skip, funext,
      rw [← mul_smul_comm] },
    rw [← finset.mul_sum, mul_comm z],
    congr,
    rw [b.sum_equiv_fun ]
end

variable (A)
/-- `embeddings_matrix A C b : matrix κ (B →ₐ[A] C) C` is the matrix whose `(i, σ)` coefficient is
  `σ (b i)`. It is mostly useful for fields when `fintype.card κ = finrank A B` and `C` is
  algebraically closed. -/
def embeddings_matrix (b : κ → B) : matrix κ (B →ₐ[A] C) C :=
of $ λ i (σ : B →ₐ[A] C), σ (b i)

-- TODO: set as an equation lemma for `embeddings_matrix`, see mathlib4#3024
@[simp] lemma embeddings_matrix_apply (b : κ → B) (i) (σ : B →ₐ[A] C) :
  embeddings_matrix A C b i σ = σ (b i) := rfl

/-- `embeddings_matrix_reindex A C b e : matrix κ κ C` is the matrix whose `(i, j)` coefficient
  is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ` given by a
  bijection `e : κ ≃ (B →ₐ[A] C)`. It is mostly useful for fields and `C` is algebraically closed.
  In this case, in presence of `h : fintype.card κ = finrank A B`, one can take
  `e := equiv_of_card_eq ((alg_hom.card A B C).trans h.symm)`. -/
def embeddings_matrix_reindex (b : κ → B) (e : κ ≃ (B →ₐ[A] C)) :=
reindex (equiv.refl κ) e.symm (embeddings_matrix A C b)

variable {A}

lemma embeddings_matrix_reindex_eq_vandermonde (pb : power_basis A B)
  (e : fin pb.dim ≃ (B →ₐ[A] C)) :
  embeddings_matrix_reindex A C pb.basis e = (vandermonde (λ i, e i pb.gen))ᵀ :=
by { ext i j, simp [embeddings_matrix_reindex, embeddings_matrix] }

section field

variables (K) {L} (E : Type z) [field E]
variables [algebra K E]
variables [module.finite K L] [is_separable K L] [is_alg_closed E]
variables (b : κ → L) (pb : power_basis K L)

lemma trace_matrix_eq_embeddings_matrix_mul_trans :
  (trace_matrix K b).map (algebra_map K E) =
  (embeddings_matrix K E b) ⬝ (embeddings_matrix K E b)ᵀ :=
by { ext i j, simp [trace_eq_sum_embeddings, embeddings_matrix, matrix.mul_apply] }

lemma trace_matrix_eq_embeddings_matrix_reindex_mul_trans [fintype κ]
  (e : κ ≃ (L →ₐ[K] E)) : (trace_matrix K b).map (algebra_map K E) =
  (embeddings_matrix_reindex K E b e) ⬝ (embeddings_matrix_reindex K E b e)ᵀ :=
by rw [trace_matrix_eq_embeddings_matrix_mul_trans, embeddings_matrix_reindex, reindex_apply,
  transpose_submatrix, ← submatrix_mul_transpose_submatrix, ← equiv.coe_refl, equiv.refl_symm]

end field

end algebra

open algebra

variables (pb : power_basis K L)

lemma det_trace_matrix_ne_zero' [is_separable K L] :
  det (trace_matrix K pb.basis) ≠ 0 :=
begin
  suffices : algebra_map K (algebraic_closure L) (det (trace_matrix K pb.basis)) ≠ 0,
  { refine mt (λ ht, _) this,
    rw [ht, ring_hom.map_zero] },
  haveI : finite_dimensional K L := pb.finite_dimensional,
  let e : fin pb.dim ≃ (L →ₐ[K] algebraic_closure L) := (fintype.equiv_fin_of_card_eq _).symm,
  rw [ring_hom.map_det, ring_hom.map_matrix_apply,
      trace_matrix_eq_embeddings_matrix_reindex_mul_trans K _ _ e,
      embeddings_matrix_reindex_eq_vandermonde, det_mul, det_transpose],
  refine mt mul_self_eq_zero.mp _,
  { simp only [det_vandermonde, finset.prod_eq_zero_iff, not_exists, sub_eq_zero],
    intros i _ j hij h,
    exact (finset.mem_Ioi.mp hij).ne' (e.injective $ pb.alg_hom_ext h) },
  { rw [alg_hom.card, pb.finrank] }
end

lemma det_trace_form_ne_zero [is_separable K L] [decidable_eq ι] (b : basis ι K L) :
  det (bilin_form.to_matrix b (trace_form K L)) ≠ 0 :=
begin
  haveI : finite_dimensional K L := finite_dimensional.of_fintype_basis b,
  let pb : power_basis K L := field.power_basis_of_finite_of_separable _ _,
  rw [← bilin_form.to_matrix_mul_basis_to_matrix pb.basis b,
      ← det_comm' (pb.basis.to_matrix_mul_to_matrix_flip b) _,
      ← matrix.mul_assoc, det_mul],
  swap, { apply basis.to_matrix_mul_to_matrix_flip },
  refine mul_ne_zero
    (is_unit_of_mul_eq_one _ ((b.to_matrix pb.basis)ᵀ ⬝ b.to_matrix pb.basis).det _).ne_zero
    _,
  { calc (pb.basis.to_matrix b ⬝ (pb.basis.to_matrix b)ᵀ).det *
        ((b.to_matrix pb.basis)ᵀ ⬝ b.to_matrix pb.basis).det
        = (pb.basis.to_matrix b ⬝ (b.to_matrix pb.basis ⬝ pb.basis.to_matrix b)ᵀ ⬝
          b.to_matrix pb.basis).det
        : by simp only [← det_mul, matrix.mul_assoc, matrix.transpose_mul]
    ... = 1 : by simp only [basis.to_matrix_mul_to_matrix_flip, matrix.transpose_one,
                            matrix.mul_one, matrix.det_one] },
  simpa only [trace_matrix_of_basis] using det_trace_matrix_ne_zero' pb
end

variables (K L)

theorem trace_form_nondegenerate [finite_dimensional K L] [is_separable K L] :
  (trace_form K L).nondegenerate :=
bilin_form.nondegenerate_of_det_ne_zero (trace_form K L) _
  (det_trace_form_ne_zero (finite_dimensional.fin_basis K L))

end det_ne_zero
