/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.primitive_element
import linear_algebra.determinant
import linear_algebra.finite_dimensional
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.matrix.to_linear_equiv
import field_theory.is_alg_closed.algebraic_closure
import field_theory.galois

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
i.e. `linear_map.mul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/

universes u v w

variables {R S T : Type*} [comm_ring R] [ring S]
variables [algebra R S]
variables {K L F : Type*} [field K] [field L] [field F]
variables [algebra K L] [algebra K F]
variables {ι : Type w}

open finite_dimensional
open linear_map
open matrix polynomial

open_locale big_operators
open_locale matrix

namespace algebra

variables (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
linear_map.det.comp (lmul R S).to_ring_hom.to_monoid_hom

lemma norm_apply (x : S) : norm R x = linear_map.det (lmul R S x) := rfl

lemma norm_eq_one_of_not_exists_basis
  (h : ¬ ∃ (s : finset S), nonempty (basis s R S)) (x : S) : norm R x = 1 :=
by { rw [norm_apply, linear_map.det], split_ifs with h, refl }

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma norm_eq_matrix_det [fintype ι] [decidable_eq ι] (b : basis ι R S) (s : S) :
  norm R s = matrix.det (algebra.left_mul_matrix b s) :=
by { rwa [norm_apply, ← linear_map.det_to_matrix b, ← to_matrix_lmul_eq], refl }

/-- If `x` is in the base ring `K`, then the norm is `x ^ [L : K]`. -/
lemma norm_algebra_map_of_basis [fintype ι] (b : basis ι R S) (x : R) :
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
protected lemma norm_algebra_map {L : Type*} [ring L] [algebra K L] (x : K) :
  norm K (algebra_map K L x) = x ^ finrank K L :=
begin
  by_cases H : ∃ (s : finset L), nonempty (basis s K L),
  { rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some] },
  { rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zero],
    rintros ⟨s, ⟨b⟩⟩,
    exact H ⟨s, ⟨b⟩⟩ },
end

section eq_prod_roots

/-- Given `pb : power_basis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
lemma power_basis.norm_gen_eq_coeff_zero_minpoly (pb : power_basis R S) :
  norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 :=
by rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff,
       charpoly_left_mul_matrix, fintype.card_fin]

/-- Given `pb : power_basis R S`, then the norm of `pb.gen` is
`((minpoly R pb.gen).map (algebra_map R F)).roots.prod`. -/
lemma power_basis.norm_gen_eq_prod_roots [algebra R F] (pb : power_basis R S)
  (hf : (minpoly R pb.gen).splits (algebra_map R F)) :
  algebra_map R F (norm R pb.gen) =
    ((minpoly R pb.gen).map (algebra_map R F)).roots.prod :=
begin
  haveI := module.nontrivial R F,
  have := minpoly.monic pb.is_integral_gen,
  rw [power_basis.norm_gen_eq_coeff_zero_minpoly, ← pb.nat_degree_minpoly, ring_hom.map_mul,
    ← coeff_map, prod_roots_eq_coeff_zero_of_monic_of_split (this.map _)
      ((splits_id_iff_splits _).2 hf), this.nat_degree_map, map_pow, ← mul_assoc, ← mul_pow],
  { simp only [map_neg, _root_.map_one, neg_mul, neg_neg, one_pow, one_mul] }, apply_instance,
end

end eq_prod_roots

section eq_zero_iff
variables [finite ι]

@[simp] lemma norm_zero [nontrivial S] [module.free R S] [module.finite R S] :
  norm R (0 : S) = 0 :=
begin
  nontriviality,
  rw [norm_apply, coe_lmul_eq_mul, map_zero, linear_map.det_zero' (module.free.choose_basis R S)]
end

@[simp] lemma norm_eq_zero_iff [is_domain R] [is_domain S] [module.free R S] [module.finite R S]
  {x : S} :
  norm R x = 0 ↔ x = 0 :=
begin
  split,
  let b := module.free.choose_basis R S,
  swap, { rintro rfl, exact norm_zero },
  { letI := classical.dec_eq (module.free.choose_basis_index R S),
    rw [norm_eq_matrix_det b,
        ← matrix.exists_mul_vec_eq_zero_iff],
    rintros ⟨v, v_ne, hv⟩,
    rw [← b.equiv_fun.apply_symm_apply v, b.equiv_fun_symm_apply, b.equiv_fun_apply,
        left_mul_matrix_mul_vec_repr] at hv,
    refine (mul_eq_zero.mp (b.ext_elem $ λ i, _)).resolve_right (show ∑ i, v i • b i ≠ 0, from _),
    { simpa only [linear_equiv.map_zero, pi.zero_apply] using congr_fun hv i },
    { contrapose! v_ne with sum_eq,
      apply b.equiv_fun.symm.injective,
      rw [b.equiv_fun_symm_apply, sum_eq, linear_equiv.map_zero] } },
end

lemma norm_ne_zero_iff [is_domain R] [is_domain S] [module.free R S] [module.finite R S]
  {x : S} :
  norm R x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr norm_eq_zero_iff

/-- This is `algebra.norm_eq_zero_iff` composed with `algebra.norm_apply`. -/
@[simp]
lemma norm_eq_zero_iff' [is_domain R] [is_domain S] [module.free R S] [module.finite R S]
  {x : S} :
  linear_map.det (linear_map.mul R S x) = 0 ↔ x = 0 :=
norm_eq_zero_iff

lemma norm_eq_zero_iff_of_basis [is_domain R] [is_domain S] (b : basis ι R S) {x : S} :
  algebra.norm R x = 0 ↔ x = 0 :=
begin
  haveI : module.free R S := module.free.of_basis b,
  haveI : module.finite R S := module.finite.of_basis b,
  exact norm_eq_zero_iff
end

lemma norm_ne_zero_iff_of_basis [is_domain R] [is_domain S] (b : basis ι R S) {x : S} :
  algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr (norm_eq_zero_iff_of_basis b)

end eq_zero_iff

open intermediate_field

variable (K)

lemma norm_eq_norm_adjoin [finite_dimensional K L] [is_separable K L] (x : L) :
  norm K x = norm K (adjoin_simple.gen K x) ^ finrank K⟮x⟯ L :=
begin
  letI := is_separable_tower_top_of_is_separable K K⟮x⟯ L,
  let pbL := field.power_basis_of_finite_of_separable K⟮x⟯ L,
  let pbx := intermediate_field.adjoin.power_basis (is_separable.is_integral K x),
  rw [← adjoin_simple.algebra_map_gen K x, norm_eq_matrix_det (pbx.basis.smul pbL.basis) _,
    smul_left_mul_matrix_algebra_map, det_block_diagonal, norm_eq_matrix_det pbx.basis],
  simp only [finset.card_fin, finset.prod_const],
  congr,
  rw [← power_basis.finrank, adjoin_simple.algebra_map_gen K x]
end

variable {K}

section intermediate_field

lemma _root_.intermediate_field.adjoin_simple.norm_gen_eq_one {x : L}
  (hx : ¬is_integral K x) : norm K (adjoin_simple.gen K x) = 1 :=
begin
  rw [norm_eq_one_of_not_exists_basis],
  contrapose! hx,
  obtain ⟨s, ⟨b⟩⟩ := hx,
  refine is_integral_of_mem_of_fg (K⟮x⟯).to_subalgebra _ x _,
  { exact (submodule.fg_iff_finite_dimensional _).mpr (of_fintype_basis b) },
  { exact intermediate_field.subset_adjoin K _ (set.mem_singleton x) }
end

lemma _root_.intermediate_field.adjoin_simple.norm_gen_eq_prod_roots (x : L)
  (hf : (minpoly K x).splits (algebra_map K F)) :
  (algebra_map K F) (norm K (adjoin_simple.gen K x)) =
    ((minpoly K x).map (algebra_map K F)).roots.prod :=
begin
  have injKxL := (algebra_map K⟮x⟯ L).injective,
  by_cases hx : is_integral K x, swap,
  { simp [minpoly.eq_zero hx, intermediate_field.adjoin_simple.norm_gen_eq_one hx] },
  have hx' : is_integral K (adjoin_simple.gen K x),
  { rwa [← is_integral_algebra_map_iff injKxL, adjoin_simple.algebra_map_gen],
    apply_instance },
  rw [← adjoin.power_basis_gen hx, power_basis.norm_gen_eq_prod_roots];
    rw [adjoin.power_basis_gen hx, minpoly.eq_of_algebra_map_eq injKxL hx'];
    try { simp only [adjoin_simple.algebra_map_gen _ _] },
  exact hf
end

end intermediate_field

section eq_prod_embeddings

open intermediate_field intermediate_field.adjoin_simple polynomial

variables (F) (E : Type*) [field E] [algebra K E]

lemma norm_eq_prod_embeddings_gen [algebra R F] (pb : power_basis R S)
  (hE : (minpoly R pb.gen).splits (algebra_map R F)) (hfx : (minpoly R pb.gen).separable) :
  algebra_map R F (norm R pb.gen) = (@@finset.univ pb^.alg_hom.fintype).prod (λ σ, σ pb.gen) :=
begin
  letI := classical.dec_eq F,
  rw [pb.norm_gen_eq_prod_roots hE, fintype.prod_equiv pb.lift_equiv',
    finset.prod_mem_multiset, finset.prod_eq_multiset_prod, multiset.to_finset_val,
    multiset.dedup_eq_self.mpr, multiset.map_id],
  { exact nodup_roots hfx.map },
  { intro x, refl },
  { intro σ, rw [pb.lift_equiv'_apply_coe, id.def] }
end

lemma norm_eq_prod_roots [is_separable K L] [finite_dimensional K L]
  {x : L} (hF : (minpoly K x).splits (algebra_map K F)) :
  algebra_map K F (norm K x) = ((minpoly K x).map (algebra_map K F)).roots.prod ^ finrank K⟮x⟯ L :=
by rw [norm_eq_norm_adjoin K x, map_pow,
  intermediate_field.adjoin_simple.norm_gen_eq_prod_roots _ hF]

lemma prod_embeddings_eq_finrank_pow [algebra L F] [is_scalar_tower K L F] [is_alg_closed E]
  [is_separable K F] [finite_dimensional K F] (pb : power_basis K L) :
  ∏ σ : F →ₐ[K] E, σ (algebra_map L F pb.gen) =
  ((@@finset.univ pb^.alg_hom.fintype).prod (λ σ : L →ₐ[K] E, σ pb.gen)) ^ finrank L F :=
begin
  haveI : finite_dimensional L F := finite_dimensional.right K L F,
  haveI : is_separable L F := is_separable_tower_top_of_is_separable K L F,
  letI : fintype (L →ₐ[K] E) := power_basis.alg_hom.fintype pb,
  letI : ∀ (f : L →ₐ[K] E), fintype (@@alg_hom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _,
  rw [fintype.prod_equiv alg_hom_equiv_sigma (λ (σ : F →ₐ[K] E), _) (λ σ, σ.1 pb.gen),
     ← finset.univ_sigma_univ, finset.prod_sigma, ← finset.prod_pow],
  refine finset.prod_congr rfl (λ σ _, _),
  { letI : algebra L E := σ.to_ring_hom.to_algebra,
    simp only [finset.prod_const, finset.card_univ],
    congr,
    rw alg_hom.card L F E },
  { intros σ,
    simp only [alg_hom_equiv_sigma, equiv.coe_fn_mk, alg_hom.restrict_domain, alg_hom.comp_apply,
         is_scalar_tower.coe_to_alg_hom'] }
end

variable (K)

/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ`  of `L` into `E`. -/
lemma norm_eq_prod_embeddings [finite_dimensional K L] [is_separable K L] [is_alg_closed E]
  {x : L} : algebra_map K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x :=
begin
  have hx := is_separable.is_integral K x,
  rw [norm_eq_norm_adjoin K x, ring_hom.map_pow, ← adjoin.power_basis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.power_basis hx) (is_alg_closed.splits_codomain _)],
  { exact (prod_embeddings_eq_finrank_pow L E (adjoin.power_basis hx)).symm },
  { haveI := is_separable_tower_bot_of_is_separable K K⟮x⟯ L,
    exact is_separable.separable K _ }
end

lemma norm_eq_prod_automorphisms [finite_dimensional K L] [is_galois K L] (x : L) :
  algebra_map K L (norm K x) = ∏ (σ : L ≃ₐ[K] L), σ x :=
begin
  apply no_zero_smul_divisors.algebra_map_injective L (algebraic_closure L),
  rw map_prod (algebra_map L (algebraic_closure L)),
  rw ← fintype.prod_equiv (normal.alg_hom_equiv_aut K (algebraic_closure L) L),
  { rw ← norm_eq_prod_embeddings,
    simp only [algebra_map_eq_smul_one, smul_one_smul] },
  { intro σ,
    simp only [normal.alg_hom_equiv_aut, alg_hom.restrict_normal', equiv.coe_fn_mk,
               alg_equiv.coe_of_bijective, alg_hom.restrict_normal_commutes, id.map_eq_id,
               ring_hom.id_apply] },
end

lemma is_integral_norm [algebra R L] [algebra R K] [is_scalar_tower R K L]
  [is_separable K L] [finite_dimensional K L] {x : L} (hx : is_integral R x) :
  is_integral R (norm K x) :=
begin
  have hx' : is_integral K x := is_integral_of_is_scalar_tower hx,
  rw [← is_integral_algebra_map_iff (algebra_map K (algebraic_closure L)).injective,
      norm_eq_prod_roots],
  { refine (is_integral.multiset_prod (λ y hy, _)).pow _,
    rw mem_roots_map (minpoly.ne_zero hx') at hy,
    use [minpoly R x, minpoly.monic hx],
    rw ← aeval_def at ⊢ hy,
    exact minpoly.aeval_of_is_scalar_tower R x y hy },
  { apply is_alg_closed.splits_codomain },
  { apply_instance }
end

end eq_prod_embeddings

end algebra
