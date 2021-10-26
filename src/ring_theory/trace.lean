/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.bilinear_form
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.determinant
import linear_algebra.vandermonde
import linear_algebra.trace
import field_theory.is_alg_closed.algebraic_closure
import field_theory.primitive_element
import ring_theory.power_basis

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/

universes u v w

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables {K L : Type*} [field K] [field L] [algebra K L]
variables {ι : Type w} [fintype ι]

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
  trace R S s = matrix.trace _ R _ (algebra.left_mul_matrix b s) :=
by rw [trace_apply, linear_map.trace_eq_matrix_trace _ b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
lemma trace_algebra_map_of_basis (x : R) :
  trace R S (algebra_map R S x) = fintype.card ι • x :=
begin
  haveI := classical.dec_eq ι,
  rw [trace_apply, linear_map.trace_eq_matrix_trace R b, trace_diag],
  convert finset.sum_const _,
  ext i,
  simp,
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

lemma trace_trace_of_basis [algebra S T] [is_scalar_tower R S T]
  {ι κ : Type*} [fintype ι] [fintype κ]
  (b : basis ι R S) (c : basis κ S T) (x : T) :
  trace R S (trace S T x) = trace R T x :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq κ,
  rw [trace_eq_matrix_trace (b.smul c), trace_eq_matrix_trace b, trace_eq_matrix_trace c,
      matrix.trace_apply, matrix.trace_apply, matrix.trace_apply,
      ← finset.univ_product_univ, finset.sum_product],
  refine finset.sum_congr rfl (λ i _, _),
  simp only [alg_hom.map_sum, smul_left_mul_matrix, finset.sum_apply,
      -- The unifier is not smart enough to apply this one by itself:
      finset.sum_apply i _ (λ y, left_mul_matrix b (left_mul_matrix c x y y))]
end

lemma trace_comp_trace_of_basis [algebra S T] [is_scalar_tower R S T]
  {ι κ : Type*} [fintype ι] [fintype κ]
  (b : basis ι R S) (c : basis κ S T) :
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

section trace_form

variables (R S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : bilin_form R S :=
(linear_map.compr₂ (lmul R S).to_linear_map (trace R S)).to_bilin

variables {S}

-- This is a nicer lemma than the one produced by `@[simps] def trace_form`.
@[simp] lemma trace_form_apply (x y : S) : trace_form R S x y = trace R S (x * y) := rfl

lemma trace_form_is_sym : sym_bilin_form.is_sym (trace_form R S) :=
λ x y, congr_arg (trace R S) (mul_comm _ _)

lemma trace_form_to_matrix [decidable_eq ι] (i j) :
  bilin_form.to_matrix b (trace_form R S) i j = trace R S (b i * b j) :=
by rw [bilin_form.to_matrix_apply, trace_form_apply]

lemma trace_form_to_matrix_power_basis (h : power_basis R S) :
  bilin_form.to_matrix h.basis (trace_form R S) = λ i j, (trace R S (h.gen ^ (i + j : ℕ))) :=
by { ext, rw [trace_form_to_matrix, pow_add, h.basis_eq_pow, h.basis_eq_pow] }

end trace_form

end algebra

section eq_sum_roots

open algebra polynomial

variables {F : Type*} [field F]
variables [algebra K S] [algebra K F]

lemma power_basis.trace_gen_eq_sum_roots [nontrivial S] (pb : power_basis K S)
  (hf : (minpoly K pb.gen).splits (algebra_map K F)) :
  algebra_map K F (trace K S pb.gen) =
    ((minpoly K pb.gen).map (algebra_map K F)).roots.sum :=
begin
  have d_pos : 0 < pb.dim := power_basis.dim_pos pb,
  have d_pos' : 0 < (minpoly K pb.gen).nat_degree, { simpa },
  haveI : nonempty (fin pb.dim) := ⟨⟨0, d_pos⟩⟩,
  -- Write the LHS as the `d-1`'th coefficient of `minpoly K pb.gen`
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_left_mul_matrix,
      ring_hom.map_neg, ← pb.nat_degree_minpoly, fintype.card_fin,
      ← next_coeff_of_pos_nat_degree _ d_pos',
      ← next_coeff_map (algebra_map K F).injective],
  -- Rewrite `minpoly K pb.gen` as a product over the roots.
  conv_lhs { rw eq_prod_roots_of_splits hf },
  rw [monic.next_coeff_mul, next_coeff_C_eq_zero, zero_add, monic.next_coeff_multiset_prod],
  -- And conclude both sides are the same.
  simp_rw [next_coeff_X_sub_C, multiset.sum_map_neg, neg_neg],
  -- Now we deal with the side conditions.
  { intros, apply monic_X_sub_C },
  { convert monic_one, simp [(minpoly.monic pb.is_integral_gen).leading_coeff] },
  { apply monic_multiset_prod_of_monic,
    intros, apply monic_X_sub_C },
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
  { exact (submodule.fg_iff_finite_dimensional _).mpr (finite_dimensional.of_finset_basis b) },
  { exact subset_adjoin K _ (set.mem_singleton x) }
end

lemma trace_gen_eq_sum_roots (x : L)
  (hf : (minpoly K x).splits (algebra_map K F)) :
  algebra_map K F (trace K K⟮x⟯ (adjoin_simple.gen K x)) =
    ((minpoly K x).map (algebra_map K F)).roots.sum :=
begin
  have injKKx : function.injective (algebra_map K K⟮x⟯) := ring_hom.injective _,
  have injKxL : function.injective (algebra_map K⟮x⟯ L) := ring_hom.injective _,
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
  rw [trace_algebra_map, ← is_scalar_tower.algebra_map_smul K, (algebra.trace K K⟮x⟯).map_smul,
      smul_eq_mul, algebra.smul_def],
  apply_instance
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

lemma algebra.is_integral_trace [finite_dimensional L F] {x : F} (hx : _root_.is_integral R x) :
  _root_.is_integral R (algebra.trace L F x) :=
begin
  have hx' : _root_.is_integral L x := is_integral_of_is_scalar_tower _ hx,
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
      multiset.erase_dup_eq_self.mpr (nodup_roots ((separable_map _).mpr hfx)), multiset.map_id],
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
  {x : L} (hx : is_integral K x) :
  algebra_map K E (algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x :=
begin
  rw [trace_eq_trace_adjoin K x, algebra.smul_def, ring_hom.map_mul, ← adjoin.power_basis_gen hx,
      trace_eq_sum_embeddings_gen E (adjoin.power_basis hx) (is_alg_closed.splits_codomain _),
      ← algebra.smul_def, algebra_map_smul],
  { exact (sum_embeddings_eq_finrank_mul L E (adjoin.power_basis hx)).symm },
  { haveI := is_separable_tower_bot_of_is_separable K K⟮x⟯ L,
    exact is_separable.separable K _ }
end

end eq_sum_embeddings

section det_ne_zero

open algebra

variables (pb : power_basis K L)

lemma det_trace_form_ne_zero' [is_separable K L] :
  det (bilin_form.to_matrix pb.basis (trace_form K L)) ≠ 0 :=
begin
  suffices : algebra_map K (algebraic_closure L)
    (det (bilin_form.to_matrix pb.basis (trace_form K L))) ≠ 0,
  { refine mt (λ ht, _) this,
    rw [ht, ring_hom.map_zero] },
  haveI : finite_dimensional K L := pb.finite_dimensional,
  let e : (L →ₐ[K] algebraic_closure L) ≃ fin pb.dim := fintype.equiv_fin_of_card_eq _,
  let M : matrix (fin pb.dim) (fin pb.dim) (algebraic_closure L) :=
    vandermonde (λ i, e.symm i pb.gen),
  calc algebra_map K (algebraic_closure _) (bilin_form.to_matrix pb.basis (trace_form K L)).det
      = det ((algebra_map K _).map_matrix $
              bilin_form.to_matrix pb.basis (trace_form K L)) : ring_hom.map_det _ _
  ... = det (Mᵀ ⬝ M) : _
  ... = det M * det M : by rw [det_mul, det_transpose]
  ... ≠ 0 : mt mul_self_eq_zero.mp _,
  { refine congr_arg det _, ext i j,
    rw [vandermonde_transpose_mul_vandermonde, ring_hom.map_matrix_apply, matrix.map_apply,
        bilin_form.to_matrix_apply, pb.basis_eq_pow, pb.basis_eq_pow, trace_form_apply,
        ← pow_add, trace_eq_sum_embeddings (algebraic_closure L) (pb.is_integral_gen.pow _),
        fintype.sum_equiv e],
    intros σ,
    rw [e.symm_apply_apply, σ.map_pow] },
  { simp only [det_vandermonde, finset.prod_eq_zero_iff, not_exists, sub_eq_zero],
    intros i _ j hij h,
    exact (finset.mem_filter.mp hij).2.ne' (e.symm.injective $ pb.alg_hom_ext h) },
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
    (det_trace_form_ne_zero' pb),
  calc (pb.basis.to_matrix b ⬝ (pb.basis.to_matrix b)ᵀ).det *
      ((b.to_matrix pb.basis)ᵀ ⬝ b.to_matrix pb.basis).det
      = (pb.basis.to_matrix b ⬝ (b.to_matrix pb.basis ⬝ pb.basis.to_matrix b)ᵀ ⬝
        b.to_matrix pb.basis).det
      : by simp only [← det_mul, matrix.mul_assoc, matrix.transpose_mul]
  ... = 1 : by simp only [basis.to_matrix_mul_to_matrix_flip, matrix.transpose_one,
                          matrix.mul_one, matrix.det_one]
end

variables (K L)

theorem trace_form_nondegenerate [finite_dimensional K L] [is_separable K L] :
  (trace_form K L).nondegenerate :=
bilin_form.nondegenerate_of_det_ne_zero (trace_form K L) _
  (det_trace_form_ne_zero (finite_dimensional.fin_basis K L))

end det_ne_zero
