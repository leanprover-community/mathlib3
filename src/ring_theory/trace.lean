/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import field_theory.adjoin
import field_theory.algebraic_closure
import field_theory.galois
import field_theory.primitive_element
import linear_algebra.bilinear_form
import linear_algebra.char_poly.coeff
import order.conditionally_complete_lattice
import ring_theory.algebra_tower
import ring_theory.localization

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`matrix.lmul`, i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/

universes u v w

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables {A: Type*} [integral_domain A] [algebra A S]
variables [algebra R S] [algebra R T]
variables {K L : Type*} [field K] [field L] [algebra K L]
variables {ι : Type w} [fintype ι]

open finite_dimensional
open intermediate_field
open linear_map
open matrix

open_locale big_operators
open_locale matrix

namespace algebra

variables {b : ι → S} (hb : is_basis R b)

variables (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R :=
(linear_map.trace R S).comp (lmul R S).to_linear_map

variables {S}

@[simp] lemma trace_apply (s : S) : trace R S s = linear_map.trace R S (lmul R S s) := rfl

lemma trace_eq_zero_of_not_exists_basis
  (h : ¬ ∃ s : finset S, is_basis R (λ x, x : (↑s : set S) → S)) : trace R S = 0 :=
by { ext s, simp [linear_map.trace, h] }

lemma findim_eq_zero_of_not_exists_basis
  (h : ¬ ∃ s : finset L, is_basis K (λ x, x : (↑s : set L) → L)) : findim K L = 0 :=
dif_neg (mt (λ h, @exists_is_basis_finset K L _ _ _ (finite_dimensional_iff_dim_lt_omega.mpr h)) h)

include hb

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma trace_eq_matrix_trace [decidable_eq ι] (hb : is_basis R b) (s : S) :
  trace R S s = matrix.trace _ R _ (matrix.lmul hb s) :=
by rw [trace_apply, linear_map.trace_eq_matrix_trace _ hb, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
lemma trace_algebra_map_of_basis (x : R) :
  trace R S (algebra_map R S x) = fintype.card ι • x :=
begin
  haveI := classical.dec_eq ι,
  rw [trace_apply, linear_map.trace_eq_matrix_trace R hb, trace_diag],
  convert finset.sum_const _,
  ext i,
  simp,
end
omit hb

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `findim` return `0`.)
-/
@[simp]
lemma trace_algebra_map (x : K) : trace K L (algebra_map K L x) = findim K L • x :=
begin
  by_cases H : ∃ s : finset L, is_basis K (λ x, x : (↑s : set L) → L),
  { rw [trace_algebra_map_of_basis H.some_spec, findim_eq_card_basis H.some_spec] },
  { simp [trace_eq_zero_of_not_exists_basis K H, findim_eq_zero_of_not_exists_basis H] },
end

section trace_form

variables (R S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : bilin_form R S :=
{ bilin := λ x y, trace R S (x * y),
  bilin_add_left := λ x y z, by rw [add_mul, linear_map.map_add],
  bilin_smul_left := λ x y z, by rw [smul_mul_assoc, linear_map.map_smul, smul_eq_mul],
  bilin_add_right := λ x y z, by rw [mul_add, linear_map.map_add],
  bilin_smul_right := λ x y z, by rw [mul_smul_comm, linear_map.map_smul, smul_eq_mul], }

variables {S}

@[simp] lemma trace_form_apply (x y : S) : trace_form R S x y = trace R S (x * y) := rfl

lemma trace_form_is_sym : sym_bilin_form.is_sym (trace_form R S) :=
λ x y, congr_arg (trace R S) (mul_comm _ _)

lemma trace_form_to_matrix [decidable_eq ι] (i j) :
  bilin_form.to_matrix hb (trace_form R S) i j = trace R S (b i * b j) :=
by rw [bilin_form.to_matrix_apply, trace_form_apply]

lemma trace_form_to_matrix_power_basis (h : power_basis R S) :
  bilin_form.to_matrix h.is_basis (trace_form R S) = λ i j, (trace R S (h.gen ^ (i + j : ℕ))) :=
by { ext, rw [trace_form_to_matrix, pow_add] }

end trace_form

end algebra

section trace_eq_sum_roots

variables {b : ι → S} (hb : is_basis R b)

open intermediate_field.adjoin_simple
open algebra

section

open polynomial

lemma matrix.card_le_card_of_left_inv' {m n : ℕ}
  {M : matrix (fin m) (fin n) A} {M' : matrix (fin n) (fin m) A}
  (hMM' : M ⬝ M' = 1) :
  m ≤ n :=
have function.left_inverse
  ((M.map (algebra_map A (fraction_ring A))).mul_vec)
  ((M'.map (algebra_map A (fraction_ring A))).mul_vec) :=
λ x, by rw [mul_vec_mul_vec, ← matrix.map_mul, hMM', matrix.ring_hom_map_one, mul_vec_one],
have function.injective ((M'.map (algebra_map A (fraction_ring A))).to_lin') :=
function.left_inverse.injective this,
calc m = findim (fraction_ring A) (fin m → fraction_ring A) : (findim_fin_fun _).symm
   ... ≤ findim (fraction_ring A) (fin n → fraction_ring A) : findim_le_findim_of_injective this
   ... = n : findim_fin_fun _

lemma matrix.card_le_card_of_left_inv {m n : Type*}
  [fintype m] [decidable_eq m] [fintype n]
  {M : matrix m n A} {M' : matrix n m A} (hMM' : M ⬝ M' = 1) :
  fintype.card m ≤ fintype.card n :=
begin
  haveI : decidable_eq n := classical.dec_eq n,
  let em := trunc.out (fintype.equiv_fin m),
  let en := trunc.out (fintype.equiv_fin n),
  apply @matrix.card_le_card_of_left_inv' A,
  calc reindex_linear_equiv em en M ⬝ reindex_linear_equiv en em M'
      = reindex_linear_equiv em em (M ⬝ M') : reindex_mul em en em M M'
  ... = reindex_linear_equiv em em 1 : by rw hMM'
  ... = 1 : (reindex_alg_equiv em).map_one
end

/-- If an `m × n` matrix has an inverse, then `m = n`. -/
noncomputable def matrix.equiv_of_inv {m n : Type*}
  [fintype m] [decidable_eq m] [fintype n] [decidable_eq n]
   {M : matrix m n A} {M' : matrix n m A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  m ≃ n :=
classical.choice (fintype.card_eq.mp (le_antisymm
  (matrix.card_le_card_of_left_inv hMM')
  (matrix.card_le_card_of_left_inv hM'M)))

/-- If `A'` is a two-sided inverse for `A` (indexed differently), `det (A ⬝ B ⬝ A') = det B`. -/
lemma det_conjugate_aux {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] {M : matrix m n A} {M' : matrix n m A} {N : matrix n n A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  det (M ⬝ N ⬝ M') = det N :=
begin
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e : m ≃ n := matrix.equiv_of_inv hMM' hM'M,
  have :
    det (reindex_linear_equiv e (equiv.refl _) M ⬝ N ⬝ reindex_linear_equiv (equiv.refl _) e M')
    = det N,
  { rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, reindex_mul,
        reindex_linear_equiv_refl_refl, hM'M, det_one, one_mul] },
  convert this,
  rw [← det_reindex_linear_equiv_self e (M ⬝ N ⬝ M'), ← reindex_mul e (equiv.refl n) e,
      ← reindex_mul e (equiv.refl n) (equiv.refl n), reindex_linear_equiv_refl_refl],
end

/-- If `A'` is a two-sided inverse for `A`, `char_poly (A ⬝ B ⬝ A') = char_poly B`. -/
lemma char_poly_conjugate_aux {m n : Type*} [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] {M : matrix m n A} {M' : matrix n m A} {N : matrix n n A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  char_poly (M ⬝ N ⬝ M') = char_poly N :=
have hCACA' : M.map C ⬝ M'.map C = 1 := by rw [← matrix.map_mul, hMM', matrix.ring_hom_map_one],
have hCA'CA : M'.map C ⬝ M.map C = 1 := by rw [← matrix.map_mul, hM'M, matrix.ring_hom_map_one],
calc (X • 1 - C.map_matrix (M ⬝ N ⬝ M')).det
    = (M.map C ⬝ (scalar n X - N.map C) ⬝ M'.map C).det :
    by rw [matrix.mul_sub, matrix.sub_mul, ring_hom.map_matrix_apply, matrix.map_mul,
           matrix.map_mul, coe_scalar, matrix.mul_smul, matrix.mul_one,
           matrix.smul_mul, hCACA']
... = (X • 1 - C.map_matrix N).det : det_conjugate_aux hCACA' hCA'CA

lemma char_poly_conjugate {n : Type*} [fintype n] [decidable_eq n] {M B : matrix n n A}
  (hM : is_unit M.det) :
  char_poly (M⁻¹ ⬝ B ⬝ M) = char_poly B :=
char_poly_conjugate_aux (nonsing_inv_mul _ hM) (mul_nonsing_inv _ hM)

end

variables {M M' : Type*} [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

section

variables {ι' κ κ' : Type*} [fintype ι'] [decidable_eq ι']
variables [decidable_eq ι] [fintype κ] [fintype κ']
variables {b' : ι' → M} (hb' : is_basis R b')
variables {c : κ → M'} {c' : κ' → M'} (hc : is_basis R c) (hc' : is_basis R c')
variables (f : M →ₗ[R] M')

lemma to_matrix_basis_change
  {b : ι → M} (hb : is_basis R b) :
  to_matrix hb hc f = hc.to_matrix c' ⬝ to_matrix hb' hc' f ⬝ hb'.to_matrix b :=
by rw [is_basis_to_matrix_mul_linear_map_to_matrix, linear_map_to_matrix_mul_is_basis_to_matrix]

end

lemma char_poly_lmul_matrix_basis_invariant [decidable_eq ι]
  {ι' : Type*} [fintype ι'] [decidable_eq ι']
  (hb : is_basis A b) {b' : ι' → S} (hb' : is_basis A b') (x : S) :
  char_poly (matrix.lmul hb x) = char_poly (matrix.lmul hb' x) :=
begin
  change char_poly (to_matrix hb hb (lmul A S x)) = char_poly (to_matrix hb' hb' (lmul A S x)),
  rw [to_matrix_basis_change hb hb' hb, char_poly_conjugate_aux];
    rw [is_basis.to_matrix_mul_to_matrix, is_basis.to_matrix_self];
    assumption
end

section

/-- `(l : M →ₗ[S] M').restrict_base R` is `l` as an `R`-linear map. -/
def linear_map.restrict_base (R : Type*) [comm_semiring R]
  {S M M' : Type*} [semiring S] [algebra R S]
  [add_comm_monoid M] [semimodule R M] [semimodule S M] [is_scalar_tower R S M]
  [add_comm_monoid M'] [semimodule R M'] [semimodule S M'] [is_scalar_tower R S M']
  (l : M →ₗ[S] M') : M →ₗ[R] M' :=
{ map_smul' := λ c x,
    show l (c • x) = c • l x,
    by rw [← is_scalar_tower.algebra_map_smul S c x, l.map_smul, is_scalar_tower.algebra_map_smul],
  .. (l.to_add_monoid_hom) }

@[simp] lemma linear_map.restrict_base_apply
  (R : Type*) {S M M' : Type*} [comm_semiring R] [semiring S] [algebra R S]
  [add_comm_monoid M] [semimodule R M] [semimodule S M] [is_scalar_tower R S M]
  [add_comm_monoid M'] [semimodule R M'] [semimodule S M'] [is_scalar_tower R S M']
  (l : M →ₗ[S] M') (x : M) : l.restrict_base R x = l x := rfl

instance is_scalar_tower.finsupp {α : Type*} : is_scalar_tower R S (α →₀ S) :=
⟨λ r s t, finsupp.ext (λ x, show ((r • s) • t x) = (r • s • t x), by rw smul_assoc)⟩

end

lemma trace_comp_of_basis [algebra S T] [is_scalar_tower R S T]
  {ι κ : Type*} [fintype ι] [fintype κ] {b : ι → S} {c : κ → T}
  (hb : is_basis R b) (hc : is_basis S c) (x : T) :
  algebra.trace R T x = trace R S (trace S T x) :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq κ,
  rw [trace_eq_matrix_trace (hb.smul hc), trace_eq_matrix_trace hb, trace_eq_matrix_trace hc,
      matrix.trace_apply, matrix.trace_apply, matrix.trace_apply,
      ← finset.univ_product_univ, finset.sum_product],
  refine finset.sum_congr rfl (λ i _, _),
  rw [alg_hom.map_sum, finset.sum_apply, finset.sum_apply],
      refine finset.sum_congr rfl (λ j _, _),
  apply matrix.smul_lmul
end

lemma trace_comp (L : Type*) [field L]
  [algebra K L] [algebra K T] [algebra L T] [is_scalar_tower K L T]
  [finite_dimensional K L] [finite_dimensional L T] (x : T) :
  algebra.trace K T x = trace K L (trace L T x) :=
trace_comp_of_basis
  (classical.some_spec (exists_is_basis_finset K L))
  (classical.some_spec (exists_is_basis_finset L T))
  x

lemma aeval_lmul_matrix [decidable_eq ι] (p : polynomial R) (x : S) :
  polynomial.aeval (matrix.lmul hb x) p = matrix.lmul hb (polynomial.aeval x p) :=
p.aeval_alg_hom_apply (matrix.lmul hb) x

lemma linear_map.injective_iff {V V' : Type*} [add_comm_group V] [add_comm_monoid V']
  [semimodule R V] [semimodule R V']
  (f : V →ₗ[R] V') : function.injective f ↔ ∀ x, f x = 0 → x = 0 :=
f.to_add_monoid_hom.injective_iff

lemma char_poly_lmul_power_basis [algebra K S] (h : power_basis K S) :
  char_poly (matrix.lmul h.is_basis h.gen) = minpoly K h.gen :=
begin
  apply minpoly.unique,
  { apply char_poly_monic },
  { have := matrix.lmul_injective h.is_basis,
    apply (matrix.lmul _).injective_iff.mp this,
    rw [← aeval_lmul_matrix, aeval_self_char_poly] },
  { intros q q_monic root_q,
    rw [char_poly_degree_eq_dim, fintype.card_fin,
        polynomial.degree_eq_nat_degree q_monic.ne_zero],
    apply with_bot.some_le_some.mpr,
    exact h.dim_le_nat_degree_of_root q_monic.ne_zero root_q }
end

section

open polynomial

lemma multiset.sum_const_one {α R : Type*} [semiring R] (s : multiset α) :
  (s.map (λ _, (1 : R))).sum = s.card :=
begin
  refine multiset.induction_on s _ _,
  { rw [multiset.map_zero, multiset.card_zero, multiset.sum_zero],
    norm_cast },
  { intros a s ih,
    rw [multiset.map_cons, multiset.sum_cons, multiset.card_cons, ih, add_comm],
    norm_cast }
end

lemma coeff_prod_X_sub_C {R : Type*} [comm_ring R] [nontrivial R] (s : multiset R) :
  (s.map (λ x, X - C x)).prod.coeff s.card = 1 :=
begin
  have monic : ∀ p ∈ s.map (λ x, X - C x), p.monic,
  { simp only [multiset.mem_map],
    rintros _ ⟨a, ha, rfl⟩,
    exact monic_X_sub_C a },
  have nat_degree_eq' : (nat_degree ∘ λ (x : R), X - C x) = (λ _, 1),
  { ext a,
    exact nat_degree_X_sub_C a },
  have leading_coeff_eq' : (leading_coeff ∘ λ (x : R), X - C x) = (λ _, 1),
  { ext a,
    exact monic_X_sub_C a },

  convert leading_coeff_multiset_prod' _ _,
  { simp [nat_degree_multiset_prod_of_monic _ monic, nat_degree_eq', multiset.sum_const_one] },
  { rw [multiset.map_map, leading_coeff_eq', multiset.prod_map_one] },
  { convert (one_ne_zero : (1 : R) ≠ 0),
    rw [multiset.map_map, leading_coeff_eq', multiset.prod_map_one] },
end

lemma coeff_prod_X_sub_C_of_succ_eq_aux {R : Type*} [comm_ring R] [nontrivial R]
  (a : R) (s : multiset R) :
  ((a ::ₘ s).map (λ x, X - C x)).prod.coeff s.card = - (a ::ₘ s).sum :=
begin
  refine multiset.induction_on s _ (λ b s ih, _),
  { simp only [multiset.map_cons, multiset.map_zero, multiset.prod_cons, multiset.prod_zero,
        mul_one, multiset.sum_cons, multiset.sum_zero, add_zero, multiset.card_zero,
        coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] },
  rw [multiset.cons_swap a b s, multiset.map_cons, multiset.prod_cons, multiset.sum_cons,
      multiset.card_cons, coeff_mul, finset.nat.antidiagonal_succ, finset.sum_insert, neg_add],
  congr,
  { simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub],
    rw [← multiset.card_cons a s, coeff_prod_X_sub_C (a ::ₘ s), mul_one] },
  { rw [finset.sum_eq_single (1, s.card), ih, coeff_sub, coeff_X_one, coeff_C,
        if_neg (one_ne_zero : (1 : ℕ) ≠ 0), sub_zero, one_mul],
    { simp only [finset.mem_map],
      rintros _ ⟨⟨i, j⟩, hij, rfl⟩ ij_ne,
      have one_ne : 1 ≠ nat.succ i,
      { intro hi,
        apply ij_ne,
        cases nat.succ_injective hi,
        simp only [finset.nat.mem_antidiagonal, zero_add] at hij,
        cases hij,
        refl },
      simp only [function.embedding.prod_map, function.embedding.coe_fn_mk, prod.map,
          coeff_sub, coeff_X, if_neg one_ne, coeff_C, if_neg (nat.succ_ne_zero i),
          sub_zero, zero_mul] },
    { simp only [finset.mem_map, not_exists],
      intros hx,
      exfalso,
      simpa using hx ⟨0, multiset.card s⟩ } },
  { simp only [finset.mem_map, not_exists],
    rintros ⟨i, j⟩ hij,
    simp [i.succ_ne_zero] }
end

lemma coeff_prod_X_sub_C_of_succ_eq {R : Type*} [comm_ring R] [nontrivial R]
  (s : multiset R) :
  ∀ {i : ℕ} (hi : i + 1 = s.card), (s.map (λ x, X - C x)).prod.coeff i = - s.sum :=
begin
  refine multiset.induction _ _ s,
  { rintros i ⟨⟩ },
  intros a s ih i hi,
  rw [multiset.card_cons, add_left_inj] at hi,
  cases hi,
  exact coeff_prod_X_sub_C_of_succ_eq_aux a s
end

lemma coeff_sub_one_eq {K L : Type*} [field K] [field L]
  {p : polynomial K} {hp : 0 < p.nat_degree} {f : K →+* L} (h : p.splits f) :
  f (p.coeff (p.nat_degree - 1)) = - f (p.leading_coeff) * multiset.sum (p.map f).roots :=
begin
  conv_lhs { rw [← coeff_map, eq_prod_roots_of_splits h] },
  rw [coeff_C_mul, coeff_prod_X_sub_C_of_succ_eq, neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm],
  rw [nat.sub_add_cancel hp, nat_degree_eq_card_roots h],
end

end

lemma fin.nonempty {n : ℕ} (hn : 0 < n) : nonempty (fin n) :=
by { cases n, { cases hn }, { exact has_zero.nonempty } }

lemma power_basis.trace_gen_eq_sum_roots {F : Type*} [field F] [algebra K F]
  (pb : power_basis K L)
  (h : polynomial.splits (algebra_map K F) pb.minpoly_gen) :
  algebra_map _ F (algebra.trace K L pb.gen) =
    (pb.minpoly_gen.map (algebra_map K F)).roots.sum :=
begin
  rw [trace_eq_matrix_trace pb.is_basis,
      trace_eq_neg_char_poly_coeff (matrix.lmul _ (power_basis.gen _)),
      char_poly_lmul_power_basis, ← pb.minpoly_gen_eq,
      fintype.card_fin, ← pb.nat_degree_minpoly_gen,
      ring_hom.map_neg, coeff_sub_one_eq h,
      show pb.minpoly_gen.leading_coeff = 1, from pb.minpoly_gen_monic,
      ring_hom.map_one, neg_mul_eq_neg_mul_symm, one_mul, neg_neg],
   { exact pb.nat_degree_minpoly_gen_pos },
   { apply fin.nonempty,
      rw [← pb.nat_degree_minpoly, polynomial.nat_degree_pos_iff_degree_pos],
     exact minpoly.degree_pos pb.is_integral_gen }
end

section

open intermediate_field

lemma trace_gen_eq_sum_roots {F : Type*} [field F] [algebra K F]
  {x : L} (hx : is_integral K x) (h : polynomial.splits (algebra_map K F) (minpoly K x)) :
  algebra_map _ F (algebra.trace K K⟮x⟯ (gen K x)) =
    ((minpoly K x).map (algebra_map K F)).roots.sum :=
begin
  rw ← adjoin.power_basis.minpoly_gen_eq hx at ⊢ h,
  exact power_basis.trace_gen_eq_sum_roots _ h
end

@[simp] lemma multiset.length_to_list {α : Type*} (m : multiset α) :
  m.to_list.length = m.card :=
calc m.to_list.length = multiset.card ↑m.to_list : (multiset.coe_card _).symm
... = m.card : congr_arg _ m.coe_to_list

section conjugates

open polynomial

/-- `alg_hom_of_root (hx : is_integral K x) (hy : aeval y (minpoly hx) = 0)`
is the algebra homomorphism sending `K` to the image of `K` in `F` and `x` to `y`. -/
noncomputable def alg_hom_of_root {F : Type*} [field F] [algebra K F]
  {x : L} (hx : is_integral K x) {y : F} (hy : aeval y (minpoly K x) = 0) :
  ↥K⟮x⟯ →ₐ[K] F :=
(alg_hom_adjoin_integral_equiv _ hx).symm
⟨y, by simpa [mem_roots_map (minpoly.ne_zero hx)] using hy⟩

noncomputable instance algebra_adjoin_splitting_field {x : L} (hx : is_integral K x) :
  algebra ↥K⟮x⟯ (splitting_field (minpoly K x)) :=
(alg_hom_of_root hx (map_root_of_splits _ (splitting_field.splits _)
  (ne_of_gt (minpoly.degree_pos hx)))).to_ring_hom.to_algebra

variables {F : Type*} [field F] [algebra K F] (pb : power_basis K L)
  (hF : pb.minpoly_gen.splits (algebra_map K F))

lemma power_basis.dim_eq_card_roots
  (hF : pb.minpoly_gen.splits (algebra_map K F)) :
  pb.dim = (pb.minpoly_gen.map (algebra_map K F)).roots.card :=
by rw [← power_basis.nat_degree_minpoly_gen, nat_degree_eq_card_roots hF]

@[simp]
lemma multiset.to_list_nodup {α : Type*} {m : multiset α} :
  m.to_list.nodup ↔ m.nodup :=
by rw [← multiset.coe_nodup, m.coe_to_list]

@[simp]
lemma list.sum_nth_le {α β : Type*} [add_comm_monoid β] (l : list α) (f : α → β)
  {n : ℕ} (hn : n = l.length) :
  ∑ i : fin n, f (l.nth_le i (lt_of_lt_of_le i.2 (le_of_eq hn))) = (l.map f).sum :=
begin
  cases hn,
  induction l with a l ih,
  { rw [list.map_nil, list.sum_nil, ← finset.sum_empty, finset.sum_congr _ (λ _ _, rfl)],
    ext i,
    cases i.2 },
  { rw [list.map_cons, list.sum_cons, ← ih rfl, finset.sum_fin_eq_sum_range,
        finset.sum_fin_eq_sum_range],
    conv in (finset.range (a :: l).length)
    { rw list.length_cons a l},
    rw [finset.sum_range_succ', add_comm],
    dsimp only [list.length_cons],
    refine congr (congr_arg (+) _) _,
    { simp [dif_pos (nat.zero_lt_succ _)] },
    { refine finset.sum_congr rfl _,
      intros i hi,
      rw finset.mem_range at hi,
      rw [dif_pos hi, dif_pos (nat.succ_lt_succ hi)],
      refl } },
end

-- TODO: `@[to_additive]` doesn't work
@[simp]
lemma list.prod_nth_le {α β : Type*} [comm_monoid β] (l : list α) (f : α → β)
  {n : ℕ} (hn : n = l.length) :
  ∏ i : fin n, f (l.nth_le i (lt_of_lt_of_le i.2 (le_of_eq hn))) = (l.map f).prod :=
begin
  cases hn,
  induction l with a l ih,
  { rw [list.map_nil, list.prod_nil, ← finset.prod_empty, finset.prod_congr _ (λ _ _, rfl)],
    ext i,
    cases i.2 },
  { rw [list.map_cons, list.prod_cons, ← ih rfl, finset.prod_fin_eq_prod_range,
        finset.prod_fin_eq_prod_range],
    conv in (finset.range (a :: l).length)
    { rw list.length_cons a l},
    rw [finset.prod_range_succ', mul_comm],
    dsimp only [list.length_cons],
    refine congr (congr_arg (*) _) _,
    { simp [dif_pos (nat.zero_lt_succ _)] },
    { refine finset.prod_congr rfl _,
      intros i hi,
      rw finset.mem_range at hi,
      simp only [dif_pos hi, dif_pos (nat.succ_lt_succ hi)],
      refl } },
end

@[simp, to_additive]
lemma multiset.prod_to_list {α : Type*} [comm_monoid α] (m : multiset α) :
  m.to_list.prod = m.prod :=
by rw [← multiset.coe_prod m.to_list, m.coe_to_list]

include hF
/-- `power_basis.conjugates hF` is the vector of all conjugates to the generator of `L / K`,
in a field `F` where `hF` shows the appropriate minimal polynomial splits.

The order of the conjugates is arbitrary.
-/
noncomputable def power_basis.conjugates :
  fin pb.dim → F :=
λ i, (pb.minpoly_gen.map (algebra_map K F)).roots.to_list.nth_le i
  (by simpa [pb.dim_eq_card_roots hF] using i.2)

/-- `power_basis.conjugate_matrix hF` is a Vandermonde matrix of conjugates to
the generator of `L / K`, in a field `F` where `hF` shows the appropriate minimal polynomial splits.

The order of the conjugates is arbitrary.
-/
noncomputable def power_basis.conjugate_matrix :
  matrix (fin pb.dim) (fin pb.dim) F
| i j := pb.conjugates hF j ^ (i : ℕ)

lemma power_basis.conjugates_injective (hpb : pb.minpoly_gen.separable) :
  function.injective (pb.conjugates hF) :=
λ i j h, fin.coe_injective (list.nodup_iff_nth_le_inj.mp
  (multiset.to_list_nodup.mpr (nodup_roots (separable.map hpb)))
  _ _ _ _ h)

lemma sum_conjugates (f : F → R) :
  ∑ i, f (pb.conjugates hF i) = ((pb.minpoly_gen.map (algebra_map K F)).roots.map f).sum :=
begin
  refine trans (list.sum_nth_le _ _ _) _,
  { rw [pb.dim_eq_card_roots hF, multiset.length_to_list] },
  rw [← multiset.coe_sum, ← multiset.coe_map, multiset.coe_to_list]
end

omit hF

/-- A `S`-algebra structure on `T` given by a map fixing `R` gives a tower of algebras. -/
@[priority(100)] -- See note [lower instance priority]
instance algebra_tower_alg_hom (f : S →ₐ[R] T) :
  @is_scalar_tower R S T _ f.to_ring_hom.to_algebra.to_has_scalar _ :=
{ smul_assoc := λ x y z, show f (x • y) • z = x • (f y • z), by rw [f.map_smul, smul_assoc] }

lemma trace_eq_sum_roots [finite_dimensional K L]
  {x : L} (hx : is_integral K x) (hF : (minpoly K x).splits (algebra_map K F)) :
  algebra_map K F (algebra.trace K L x) =
    findim ↥K⟮x⟯ L • ((minpoly K x).map (algebra_map K _)).roots.sum :=
begin
  haveI : finite_dimensional K⟮x⟯ L := finite_dimensional.right K _ L,
  rw trace_comp K⟮x⟯ x,
  conv in x { rw [← algebra_map_gen K x] },
  rw [trace_algebra_map, ← is_scalar_tower.algebra_map_smul K, (algebra.trace K K⟮x⟯).map_smul,
      smul_eq_mul, ring_hom.map_mul, ← is_scalar_tower.algebra_map_apply ℕ K _, ← smul_def,
      trace_gen_eq_sum_roots hx hF],
   all_goals { apply_instance }
end

noncomputable instance multiset.fintype_mem {α : Type*} (m : multiset α) :
  fintype {x // x ∈ m} :=
by classical; exact
fintype.of_injective
  (λ x, (⟨x.1, finset.mem_coe.mpr (multiset.mem_to_finset.mpr x.2)⟩ : (m.to_finset : set α)))
  (λ ⟨x, hx⟩ ⟨y, hy⟩ h, by { ext, simpa using h })

@[simp] lemma multiset.univ_mem_zero {α : Type*} :
  (finset.univ : finset {x // x ∈ (0 : multiset α)}) = ∅ :=
by { ext x, cases x with _ hx, cases hx }

@[to_additive, simp] lemma multiset.prod_mem {α M : Type*} [decidable_eq α]
  [comm_monoid M] (m : multiset α) (f : {x // x ∈ m} → M) (g : α → M)
  (hfg : ∀ x, f x = g x) :
  ∏ (x : {x // x ∈ m}), f x = ∏ x in m.to_finset, g x :=
finset.prod_bij (λ x _, x.1) (λ x _, multiset.mem_to_finset.mpr x.2)
  (λ _ _, hfg _)
  (λ _ _ _ _ h, by { ext, assumption })
  (λ y hy, ⟨⟨y, multiset.mem_to_finset.mp hy⟩, finset.mem_univ _, rfl⟩)

/-- Specialize `finset.sum_bij'` to sums over fintypes with an equiv. -/
lemma finset.sum_equiv {M : Type*} [add_comm_monoid M]
  {m n : Type*} [fintype m] [fintype n] (e : m ≃ n) (f : m → M) :
  ∑ x : m, f x = ∑ y : n, f (e.symm y) :=
finset.sum_bij'
  (λ x _, e x) (λ _ _, finset.mem_univ _) (λ _ _, by rw e.symm_apply_apply)
  (λ y _, e.symm y) (λ _ _, finset.mem_univ _) (λ _ _, by rw e.symm_apply_apply)
  (λ _ _, by rw e.apply_symm_apply)

@[simp] lemma adjoin_root_equiv_adjoin_symm_gen {x : L} (h : is_integral K x) :
  (adjoin_root_equiv_adjoin K h).symm (adjoin_simple.gen K x) =
    adjoin_root.root (minpoly K x) :=
(adjoin_root_equiv_adjoin K h).injective (by simp [adjoin_root_equiv_adjoin_apply_root])

@[simp] lemma adjoin_root_equiv_symm_apply_root {f : polynomial K} (hf : f ≠ 0)
  (x : {x // x ∈ (f.map (algebra_map K L)).roots}) :
  (adjoin_root.equiv K L f hf).symm x (adjoin_root.root _) = x :=
by { simp only [adjoin_root.equiv, equiv.coe_fn_symm_mk],
     exact @adjoin_root.lift_root _ _ _ f _ _ _ ((mem_roots_map hf).mp x.2) }

lemma alg_hom_adjoin_integral_equiv_apply
  {x : L} (hx : is_integral K x)
  (y : {y // y ∈ ((minpoly K x).map (algebra_map K F)).roots}) :
  (alg_hom_adjoin_integral_equiv K hx).symm y (gen K x) = y :=
by simp only [alg_hom_adjoin_integral_equiv, equiv.symm_trans_apply,
  adjoin_root_equiv_adjoin_symm_gen, alg_equiv.coe_alg_hom, equiv.coe_fn_symm_mk,
  alg_equiv.to_alg_hom_eq_coe, adjoin_root_equiv_symm_apply_root, alg_hom.comp_apply]

lemma sum_embeddings_gen {M : Type*} [add_comm_monoid M]
  {x : L} (hx : is_integral K x) (hfx : (minpoly K x).separable)
  (f : F → M) :
  @finset.sum _ _ _ (@finset.univ _ (fintype_of_alg_hom_adjoin_integral _ hx))
      (λ σ : ↥K⟮x⟯ →ₐ[K] F, f (σ (adjoin_simple.gen K x)))
    = (((minpoly K x).map (algebra_map K F)).roots.map f).sum :=
begin
  classical,
  rw [finset.sum_equiv (alg_hom_adjoin_integral_equiv K hx), multiset.sum_mem _ _ f],
  { rw [finset.sum_eq_multiset_sum, multiset.to_finset_val,
        multiset.erase_dup_eq_self.mpr (nodup_roots ((separable_map _).mpr hfx))] },
  { intro x,
    rw alg_hom_adjoin_integral_equiv_apply hx }
end

-- TODO: prove this directly assuming `is_power_basis`
lemma trace_eq_sum_embeddings_gen [finite_dimensional K L]
  {x : L} (hx : is_integral K x) (hfx : (minpoly K x).separable)
  (hF : (minpoly K x).splits (algebra_map K F)) :
  algebra_map K F (algebra.trace K L x) =
    findim ↥K⟮x⟯ L • @finset.sum _ _ _ (@finset.univ _ (fintype_of_alg_hom_adjoin_integral _ hx))
      (λ σ : ↥K⟮x⟯ →ₐ[K] F, σ (adjoin_simple.gen K x)) :=
by simp_rw [trace_eq_sum_roots hx hF, sum_embeddings_gen hx hfx (λ x, x), multiset.map_id']

/-- Apply an `alg_equiv` to the left side of an `alg_hom`. -/
def alg_hom_congr_left {S' : Type*} (T : Type*) [comm_semiring S'] [algebra R S']
  [comm_semiring T] [algebra R T]
  (e : S ≃ₐ[R] S') : (S →ₐ[R] T) ≃ (S' →ₐ[R] T) :=
{ to_fun := λ f, f.comp e.symm,
  inv_fun := λ f, f.comp e,
  left_inv := λ x,
    by { ext, simp only [alg_equiv.symm_apply_apply, alg_equiv.coe_alg_hom, alg_hom.comp_apply] },
  right_inv := λ x,
    by { ext, simp only [alg_equiv.apply_symm_apply, alg_equiv.coe_alg_hom, alg_hom.comp_apply] } }

@[simp] lemma alg_hom_congr_left_apply {S' T : Type*} [comm_semiring S'] [algebra R S']
  [comm_semiring T] [algebra R T]
  (e : S ≃ₐ[R] S') (f : S →ₐ[R] T) (x : S') : alg_hom_congr_left T e f x = f (e.symm x) :=
rfl

@[simp] lemma alg_hom_congr_left_symm_apply {S' T : Type*} [comm_semiring S'] [algebra R S']
  [comm_semiring T] [algebra R T]
  (e : S ≃ₐ[R] S') (f : S' →ₐ[R] T) (x : S) : (alg_hom_congr_left T e).symm f x = f (e x) :=
rfl

/-- A rephrasing of the primitive element theorem:
in a finite separable field extension, there is an `x` such that `L ≃ K⟮x⟯`. -/
noncomputable def field.equiv_primitive_element (K L : Type*) [field K] [field L] [algebra K L]
  [is_separable K L] [finite_dimensional K L] :
  Σ x : L, L ≃ₐ[K] K⟮x⟯ :=
let f := (@intermediate_field.top_equiv K _ L _ _).symm in
⟨classical.some (field.exists_primitive_element K L),
 by rwa ← classical.some_spec (field.exists_primitive_element K L) at f⟩

/-- If `L` has a power basis over `K`, there are finitely many maps `L → F` fixing `K`. -/
noncomputable def power_basis.fintype_alg_hom (pb : power_basis K L) :
  fintype (L →ₐ[K] F) :=
@fintype.of_equiv _ (K⟮pb.gen⟯ →ₐ[K] F)
  (fintype_of_alg_hom_adjoin_integral _ pb.is_integral_gen)
  (alg_hom_congr_left F pb.equiv_adjoin_simple)

lemma finite_dimensional.is_integral (K : Type*) [field K] [algebra K L] [finite_dimensional K L]
  (x : L) : is_integral K x :=
((is_algebraic_iff_is_integral K).mp (is_algebraic_of_finite x))

noncomputable instance alg_hom.fintype_of_separable
  [hsep : is_separable K L] [finite_dimensional K L] :
  fintype (L →ₐ[K] F) :=
@fintype.of_equiv _ (K⟮(field.equiv_primitive_element K L).1⟯ →ₐ[K] F)
  (fintype_of_alg_hom_adjoin_integral _ (finite_dimensional.is_integral _ _))
  (alg_hom_congr_left F (field.equiv_primitive_element K L).2.symm)

noncomputable instance adjoin.fintype_alg_hom_of_finite_dimensional (x : L)
  [finite_dimensional K L] :
  fintype (K⟮x⟯ →ₐ[K] F) :=
power_basis.fintype_alg_hom
  (intermediate_field.adjoin.power_basis (finite_dimensional.is_integral _ _))

-- TODO: to_additive this from prod_surj
lemma finset.sum_eq_card_smul {α β : Type*} [decidable_eq β]
  (f : α → β) {M : Type*} [add_comm_monoid M] (gf : α → M) (g : β → M)
  (s : finset α) (t : finset β)
  (hf : ∀ x ∈ s, f x ∈ t) (hgf : ∀ x ∈ s, gf x = g (f x)) (n : ℕ)
  (hcard : ∀ y ∈ t, (s.filter (λ x, f x = y)).card = n) :
  ∑ x in s, gf x = n • (∑ y in t, g y) :=
calc ∑ x in s, gf x = ∑ x in s, g (f x) : finset.sum_congr rfl hgf
... = ∑ y in finset.image f s, (s.filter (λ x, f x = y)).card • g y : finset.sum_comp g f
... = ∑ y in t, (s.filter (λ x, f x = y)).card • g y :
  finset.sum_subset
    (λ y hy, by { rcases finset.mem_image.mp hy with ⟨x, hx, rfl⟩, exact hf x hx })
    (λ y hyt hys, (by { have := mt (finset.fiber_card_ne_zero_iff_mem_image _ _ _).mp hys,
                        rw [ne.def, not_not] at this,
                        rw [this, zero_smul] }))
... = ∑ y in t, n • g y : finset.sum_congr rfl (λ y hy, by rw hcard y hy)
... = n • ∑ y in t, g y : finset.smul_sum.symm

lemma adjoin_root.nontrivial {R : Type*} [integral_domain R]
  {f : polynomial R} (hf : 0 < degree f) :
  nontrivial (adjoin_root f) :=
⟨⟨0, 1, λ h,
  begin
    apply not_le_of_gt (nat_degree_pos_iff_degree_pos.mpr hf),
    simpa using nat_degree_le_of_dvd ((adjoin_root.mk_eq_mk _ _ _).mp h) (by simp),
  end ⟩⟩

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable def power_basis.alg_hom_adjoin_equiv (pb : power_basis K L) :
  (L →ₐ[K] F) ≃ {x // x ∈ (pb.minpoly_gen.map (algebra_map K F)).roots} :=
begin
  haveI : nontrivial (adjoin_root pb.minpoly_gen) :=
    adjoin_root.nontrivial pb.degree_minpoly_gen_pos,
  let ϕ := (adjoin_root.power_basis pb.minpoly_gen_ne_zero).equiv pb _,
  { let swap1 : (L →ₐ[K] F) ≃ (adjoin_root pb.minpoly_gen →ₐ[K] F) :=
      { to_fun := λ f, f.comp ϕ.to_alg_hom,
        inv_fun := λ f, f.comp ϕ.symm.to_alg_hom,
        left_inv := λ _, by { ext, simp only [alg_equiv.coe_alg_hom,
        alg_equiv.to_alg_hom_eq_coe, alg_hom.comp_apply, alg_equiv.apply_symm_apply]},
        right_inv := λ _, by { ext, simp only [alg_equiv.symm_apply_apply,
        alg_equiv.coe_alg_hom, alg_equiv.to_alg_hom_eq_coe, alg_hom.comp_apply] } },
    let swap2 := adjoin_root.equiv K F pb.minpoly_gen pb.minpoly_gen_ne_zero,
    exact swap1.trans swap2 },
  rw [adjoin_root.minpoly_gen_eq _ pb.minpoly_gen_monic],
  { rw pb.minpoly_gen_eq, exact minpoly.irreducible pb.is_integral_gen }
end

-- generalizes card_alg_hom_adjoin_integral
-- TODO: merge this with the field.adjoin version
lemma power_basis.card_alg_hom (pb : power_basis K L)
  (h_sep : pb.minpoly_gen.separable)
  (h_splits : pb.minpoly_gen.splits (algebra_map K F)) :
  @fintype.card (L →ₐ[K] F) pb.fintype_alg_hom = pb.dim :=
begin
  classical,
  let s := (pb.minpoly_gen.map (algebra_map K F)).roots.to_finset,
  have H := λ x, multiset.mem_to_finset,
  rw [fintype.card_congr pb.alg_hom_adjoin_equiv, fintype.card_of_subtype s H,
      multiset.to_finset_card_of_nodup, ← nat_degree_eq_card_roots h_splits,
      pb.nat_degree_minpoly_gen],
  exact polynomial.nodup_roots h_sep.map
end

lemma polynomial.splits_of_is_alg_closed (L : Type*) [field L] [algebra K L]
  [is_alg_closed L] (f : polynomial K) :
  f.splits (algebra_map K L) :=
begin
  convert (splits_map_iff _ (ring_hom.id L)).mp (f.map (algebra_map K L)).splits',
  exact (ring_hom.id_comp _).symm
end

lemma alg_hom.to_linear_map_injective :
  function.injective (alg_hom.to_linear_map : (L →ₐ[K] F) → (L →ₗ[K] F)) :=
λ f g h, alg_hom.ext (λ x, by rw [← f.to_linear_map_apply, h, g.to_linear_map_apply])

lemma power_basis.alg_hom_ext (pb : power_basis K L) (f g : L →ₐ[K] F)
  (h : f pb.gen = g pb.gen) : f = g :=
alg_hom.to_linear_map_injective (pb.is_basis.ext (λ i,
  by rw [f.to_linear_map_apply, g.to_linear_map_apply, alg_hom.map_pow, alg_hom.map_pow, h]))

lemma is_scalar_tower.restrict_base_injective {A B : Type*}
  [semiring A] [semiring B]
  [algebra R A] [algebra S A] [algebra R B] [algebra S B]
  [is_scalar_tower R S A] [is_scalar_tower R S B] :
  function.injective (is_scalar_tower.restrict_base R : (A →ₐ[S] B) → (A →ₐ[R] B)) :=
λ f g h, alg_hom.ext (λ x,
  by rw [← is_scalar_tower.restrict_base_apply R f x, h, is_scalar_tower.restrict_base_apply])

@[simp] lemma intermediate_field.algebra_map_mk (S : intermediate_field K L)
  {x : L} (hx : x ∈ S) : algebra_map S L ⟨x, hx⟩ = x := rfl

@[simp] lemma intermediate_field.algebra_map_algebra_map (S : intermediate_field K L)
  [algebra S F] [is_scalar_tower K S F] (x : K) :
  algebra_map S F ⟨algebra_map K L x, S.algebra_map_mem x⟩ = algebra_map K F x :=
by { rw [is_scalar_tower.algebra_map_apply K S F], refl }

/-- If `f` fixes `K` and `x`, then `f` fixes `K⟮x⟯`. -/
def intermediate_field.adjoin.extend_base (x : L) [algebra K⟮x⟯ F] [is_scalar_tower K K⟮x⟯ F]
  (f : L →ₐ[K] F) (hf : f x = algebra_map _ _ (gen K x)) :
  L →ₐ[K⟮x⟯] F :=
{ commutes' := begin
    rintro ⟨r, hr⟩,
    simp only [intermediate_field.algebra_map_mk, ring_hom.to_fun_eq_coe, alg_hom.coe_to_ring_hom],
    suffices : ∃ hr, f r = algebra_map K⟮x⟯ F ⟨r, hr⟩,
    { obtain ⟨_, h⟩ := this,
      exact h },
    refine intermediate_field.adjoin_induction K hr _ _ _ _ _ _,
    { rintros x' (hx' | hx'), exact ⟨intermediate_field.subset_adjoin K _ H, hf⟩ },
    { rintros c,
      use K⟮x⟯.algebra_map_mem c,
      simp only [f.commutes],
      apply (K⟮x⟯.algebra_map_algebra_map c).symm.trans _, assumption, assumption,
      congr },
    { rintros a b ⟨ha, a_eq⟩ ⟨hb, b_eq⟩,
      use K⟮x⟯.add_mem ha hb,
      simp only [f.map_add, a_eq, b_eq, ← ring_hom.map_add],
      congr },
    { rintros a ⟨ha, a_eq⟩,
      use K⟮x⟯.neg_mem ha,
      simp only [f.map_neg, a_eq, ← ring_hom.map_neg],
      congr },
    { rintros a ⟨ha, a_eq⟩,
      use K⟮x⟯.inv_mem ha,
      simp only [f.map_inv, a_eq, ← ring_hom.map_inv],
      congr },
    { rintros a b ⟨ha, a_eq⟩ ⟨hb, b_eq⟩,
      use K⟮x⟯.mul_mem ha hb,
      simp only [f.map_mul, a_eq, b_eq, ← ring_hom.map_mul],
      congr },
  end,
  .. (f : L →+* F) }

@[simp]
lemma restrict_base_extend_base (x : L) [algebra K⟮x⟯ F] [is_scalar_tower K K⟮x⟯ F]
  (f : L →ₐ[K] F) (hf : f x = algebra_map _ _ (gen K x)) :
  is_scalar_tower.restrict_base K (intermediate_field.adjoin.extend_base x f hf) = f :=
by { ext, refl }

lemma card_filter_apply_eq [decidable_eq F] [is_alg_closed F]
  [is_separable K L] [finite_dimensional K L]
  (x : L) (hx : is_integral K x) (y : F)
  (hy : aeval y ((intermediate_field.adjoin.power_basis hx).minpoly_gen) = 0) :
  (finset.univ.filter (λ (σ : L →ₐ[K] F), σ x = y)).card = findim K⟮x⟯ L :=
begin
  let pb : power_basis K L := field.power_basis_of_finite_of_separable K L,
  let emb_y : K⟮x⟯ →ₐ[K] F := (intermediate_field.adjoin.power_basis hx).lift y hy,
  letI : algebra K⟮x⟯ F := (emb_y : K⟮x⟯ →+* F).to_algebra,
  haveI : is_scalar_tower K K⟮x⟯ F := is_scalar_tower.of_algebra_map_eq
    (λ x, (emb_y.commutes x).symm),

  have emb_y_gen : emb_y (adjoin_simple.gen K x) = y,
  { rw [← adjoin.power_basis.gen_eq hx, (intermediate_field.adjoin.power_basis hx).lift_gen] },
  have algebra_map_gen : algebra_map _ F (adjoin_simple.gen K x) = y := emb_y_gen,

  haveI sep_x : is_separable K⟮x⟯ L :=
    is_separable_tower_top_of_is_separable K K⟮x⟯ L,
  let pb_x : power_basis K⟮x⟯ L := field.power_basis_of_finite_of_separable _ L,
  letI : fintype (L →ₐ[K⟮x⟯] F) := pb_x.fintype_alg_hom,

  calc (finset.univ.filter (λ (σ : L →ₐ[K] F), σ x = y)).card
      = fintype.card (L →ₐ[K⟮x⟯] F) :
        (finset.card_congr (λ f _, is_scalar_tower.restrict_base K f) _ _ _).symm
  ... = pb_x.dim : pb_x.card_alg_hom _ _
  ... = findim ↥K⟮x⟯ L : pb_x.findim.symm,
  { intros f _,
    simp only [finset.mem_filter, finset.mem_univ, true_and, is_scalar_tower.restrict_base_apply,
               ← adjoin_simple.algebra_map_gen K x, f.commutes, algebra_map_gen] },
  { intros f g _ _ h,
    ext x,
    rw is_scalar_tower.restrict_base_injective h },
  { intros f hf,
    simp only [finset.mem_filter, finset.mem_univ, true_and] at hf,
    refine ⟨intermediate_field.adjoin.extend_base _ f (hf.trans algebra_map_gen.symm),
            finset.mem_univ _,
            _⟩,
    simp },
  { rw [pb_x.minpoly_gen_eq], apply is_separable.separable },
  { apply polynomial.splits_of_is_alg_closed },
end

lemma sum_embeddings_eq_findim_mul [is_alg_closed F]
  [finite_dimensional K L] [hsep : is_separable K L]
  {x : L} (hx : is_integral K x) :
  ∑ σ : L →ₐ[K] F, (σ x) = findim K⟮x⟯ L •
    @finset.sum _ _ _ (@finset.univ _ (fintype_of_alg_hom_adjoin_integral _ hx))
      (λ σ : ↥K⟮x⟯ →ₐ[K] F, σ (adjoin_simple.gen K x)) :=
begin
  classical,
  letI : fintype (K⟮x⟯ →ₐ[K] F) := fintype_of_alg_hom_adjoin_integral _ hx,
  apply finset.sum_eq_card_smul (λ σ : L →ₐ[K] F, σ.comp (is_scalar_tower.to_alg_hom K K⟮x⟯ L)),
  { intros, apply finset.mem_univ },
  { intros σ hσ,
    simp only [alg_hom.comp_apply, is_scalar_tower.to_alg_hom_apply, algebra_map_gen] },
  intros σ' _,
  rw ← card_filter_apply_eq x hx (σ' (adjoin_simple.gen K x)),
  apply finset.card_congr (λ σ _, σ),
  { intros σ hσ,
    simp only [finset.mem_filter, finset.mem_univ, true_and] at ⊢ hσ,
    simp only [← hσ, alg_hom.comp_apply, is_scalar_tower.to_alg_hom_apply, algebra_map_gen] },
  { intros σ τ hσ hτ h,
    exact h },
  { intros σ hσ,
    refine ⟨σ, _, rfl⟩,
    simp only [finset.mem_filter, finset.mem_univ, true_and] at ⊢ hσ,
    apply (intermediate_field.adjoin.power_basis hx).alg_hom_ext,
    simp only [← hσ, alg_hom.comp_apply, is_scalar_tower.to_alg_hom_apply,
               intermediate_field.adjoin.power_basis.gen_eq, algebra_map_gen] },
  { rw [aeval_alg_hom, alg_hom.comp_apply, ← intermediate_field.adjoin.power_basis.gen_eq,
        (intermediate_field.adjoin.power_basis hx).aeval_minpoly_gen, σ'.map_zero] }
end

section

lemma power_basis.sum_embeddings_gen [is_separable K L] (f : F → R) :
  ∑ σ in (@finset.univ _ (@alg_hom.fintype_of_separable _ _ _ _ _ _ _ _ _
      pb.finite_dimensional)),
    f (σ pb.gen) =
    ((pb.minpoly_gen.map (algebra_map K F)).roots.map f).sum :=
begin
  haveI := pb.finite_dimensional,
  haveI : fintype (↥K⟮pb.gen⟯ →ₐ[K] F) :=
    fintype_of_alg_hom_adjoin_integral _ pb.is_integral_gen,
  convert sum_embeddings_gen pb.is_integral_gen _ f using 1,
  { rw finset.sum_equiv (alg_hom_congr_left F pb.equiv_adjoin_simple.symm),
    convert finset.sum_congr rfl (λ x _, _),
    rw [alg_hom_congr_left_symm_apply, power_basis.equiv_adjoin_simple_symm_gen] },
  { rw pb.minpoly_gen_eq },
  { apply is_separable.separable }
end

lemma power_basis.trace_gen_eq_sum_embeddings [is_separable K L]
  (hF : pb.minpoly_gen.splits (algebra_map K F)) :
  algebra_map K F (algebra.trace K L pb.gen) =
    ∑ σ in (@finset.univ _
        (@alg_hom.fintype_of_separable _ _ _ _ _ F _ _ _ pb.finite_dimensional)),
      σ pb.gen :=
by simp only [pb.trace_gen_eq_sum_roots hF, pb.sum_embeddings_gen (λ x, x), multiset.map_id']

end

section
variables (K)

-- TODO: go via `power_basis` instead of adjoin K x
lemma trace_eq_sum_embeddings
  [is_alg_closed F] [finite_dimensional K L] [is_separable K L]
  {x : L} (hx : is_integral K x) :
  algebra_map K F (algebra.trace K L x) = ∑ σ : L →ₐ[K] F, σ x :=
by { rw trace_eq_sum_embeddings_gen hx (is_separable.separable K x)
          (polynomial.splits_of_is_alg_closed F _),
     exact (sum_embeddings_eq_findim_mul hx).symm }
end

lemma algebraic_closure.splits (f : polynomial K) :
  f.splits (algebra_map K (algebraic_closure K)) :=
f.splits_of_is_alg_closed (algebraic_closure K)

lemma trace_form_gen_pow_gen_pow
  [is_alg_closed F] [is_separable K L] [finite_dimensional K L]
  (i j : ℕ) :
  algebra_map K F (trace_form K L (pb.gen ^ i) (pb.gen ^ j)) =
    ((pb.minpoly_gen.map (algebra_map K F)).roots.map (λ x, x ^ i * x ^ j)).sum :=
calc algebra_map K F (trace_form K L (pb.gen ^ i) (pb.gen ^ j))
    = algebra_map K F (trace K L (pb.gen ^ (i + j))) : by rw [pow_add, trace_form_apply]
... = ∑ (σ : L →ₐ[K] F), σ (pb.gen ^ (i + j)) :
  trace_eq_sum_embeddings _ (is_integral_pow _ pb.is_integral_gen)
... = ∑ (σ : L →ₐ[K] F), (σ pb.gen) ^ i * (σ pb.gen) ^ j :
  by simp only [pow_add, alg_hom.map_mul, alg_hom.map_pow]
... = ((pb.minpoly_gen.map (algebra_map K F)).roots.map (λ x, x ^ i * x ^ j)).sum :
  by rw ← pb.sum_embeddings_gen (λ x, x ^ i * x ^ j)

lemma conjugate_matrix_mul_conjugate_matrix [is_separable K L] :
  (pb.conjugate_matrix (algebraic_closure.splits _)) ⬝
    (pb.conjugate_matrix (algebraic_closure.splits _))ᵀ =
    ((bilin_form.to_matrix pb.is_basis (trace_form K L)).map
      (algebra_map K (algebraic_closure K))) :=
begin
  ext i k,
  simp only [matrix.mul_apply, map_apply, trace_form_to_matrix_power_basis, transpose_apply,
             power_basis.conjugate_matrix],

  haveI := pb.finite_dimensional,
  rw trace_eq_sum_embeddings K (is_integral_pow (i + k) pb.is_integral_gen),
  { simp only [← pow_add, alg_hom.map_pow],
    refine trans (sum_conjugates pb (algebraic_closure.splits _) (λ x, x ^ (i + k : ℕ))) _,
    exact (pb.sum_embeddings_gen (λ x, x ^ (i + k : ℕ))).symm },
  { apply algebraic_closure.is_alg_closed }
end

@[simp] lemma det_conjugate_matrix :
  (pb.conjugate_matrix hF).det = ∏ (i : fin pb.dim),
    ∏ j in finset.univ.filter (λ (j : fin pb.dim), i < j),
      (pb.conjugates hF j - pb.conjugates hF i) :=
matrix.det_vandermonde _

lemma sum_repr (x : S) : ∑ i, hb.repr x i • b i = x :=
begin
  convert hb.total_repr x using 1,
  rw finsupp.total_apply,
  refine (finset.sum_subset (finset.subset_univ _) (λ i _ hi, _)).symm,
  rw [finsupp.not_mem_support_iff.mp hi, zero_smul]
end

lemma lmul_one : lmul R S 1 = linear_map.id :=
by { ext, simp }

@[simp] lemma det_map {R S : Type*} [comm_ring R] [comm_ring S]
  {n : Type*} [fintype n] [decidable_eq n] (f : R →+* S) (M : matrix n n R) :
  (M.map f).det = f M.det :=
by { unfold det, simp only [f.map_sum, f.map_mul, f.map_prod, f.map_int_cast, map_apply] }

lemma det_trace_form_ne_zero' [is_separable K L] :
  det (bilin_form.to_matrix pb.is_basis (trace_form K L)) ≠ 0 :=
begin
  suffices : algebra_map K (algebraic_closure K)
    (det (bilin_form.to_matrix pb.is_basis (trace_form K L))) ≠ 0,
  { refine mt (λ ht, _) this,
    rw [ht, ring_hom.map_zero] },
  have hF := algebraic_closure.splits _,
  calc algebra_map K (algebraic_closure K) (det _)
      = det (pb.conjugate_matrix hF ⬝ (pb.conjugate_matrix hF)ᵀ) : _
  ... = det (pb.conjugate_matrix hF) ^ 2 : by simp [pow_two]
  ... = (∏ (i : fin pb.dim), ∏ j in finset.univ.filter (λ (j : fin pb.dim), i < j),
          (pb.conjugates hF j - pb.conjugates hF i)) ^ 2 : by rw det_conjugate_matrix pb
  ... ≠ 0 : _,
  { rw [← det_map, conjugate_matrix_mul_conjugate_matrix] },
  { simp only [pow_two, ne.def, mul_self_eq_zero, finset.prod_eq_zero_iff, not_exists, sub_eq_zero],
    intros i _ j hj,
    refine mt (λ hij, pb.conjugates_injective hF _ hij) (ne_of_lt (finset.mem_filter.mp hj).2).symm,
    rw pb.minpoly_gen_eq,
    exact is_separable.separable K pb.gen }
end

lemma det_transpose_mul_mul_self {n m : Type*} [fintype m] [fintype n]
  [decidable_eq m] [decidable_eq n]
  {A : matrix n n K} {B : matrix n m K} {C : matrix m n K} (hBC : B ⬝ C = 1) (hCB : C ⬝ B = 1) :
  det (Bᵀ ⬝ A ⬝ B) = det (B ⬝ Bᵀ) * det A :=
begin
  rw ← det_conjugate_aux hBC hCB,
  calc (B ⬝ (Bᵀ ⬝ A ⬝ B) ⬝ C).det = ((B ⬝ Bᵀ) ⬝ (A ⬝ (B ⬝ C))).det : by simp only [matrix.mul_assoc]
                           ... = ((B ⬝ Bᵀ) ⬝ A).det : by rw [hBC, matrix.mul_one]
                           ... = det (B ⬝ Bᵀ) * det A : matrix.det_mul _ _
end

lemma det_trace_form_ne_zero  [is_separable K L] [decidable_eq ι] {b : ι → L} (hb : is_basis K b) :
  det (bilin_form.to_matrix hb (trace_form K L)) ≠ 0 :=
begin
  haveI : finite_dimensional K L := finite_dimensional.of_fintype_basis hb,
  let pb : power_basis K L := field.power_basis_of_finite_of_separable _ _,
  have hph : pb.is_basis.to_matrix b ⬝ hb.to_matrix (λ i : fin pb.dim, pb.gen ^ (i : ℕ)) = 1,
  { apply (matrix.to_lin pb.is_basis pb.is_basis).injective,
    rw [matrix.to_lin_mul pb.is_basis hb pb.is_basis, is_basis.to_lin_to_matrix,
        is_basis.to_lin_to_matrix, id_comp, to_lin_one] },
  have hhp : hb.to_matrix (λ i : fin pb.dim, pb.gen ^ (i : ℕ)) ⬝ pb.is_basis.to_matrix b = 1,
  { apply (matrix.to_lin hb hb).injective,
    rw [matrix.to_lin_mul hb pb.is_basis hb, is_basis.to_lin_to_matrix, is_basis.to_lin_to_matrix,
        id_comp, to_lin_one] },
  rw [← bilin_form.to_matrix_basis_change hb pb.is_basis, det_transpose_mul_mul_self hph hhp],
  apply mul_ne_zero (is_unit.ne_zero _) (det_trace_form_ne_zero' pb),
  apply is_unit_det_of_left_inverse _ (_ᵀ ⬝ _),
  rw [matrix.mul_assoc, ← matrix.mul_assoc _ (pb.is_basis.to_matrix b), hhp, matrix.one_mul,
      ← matrix.transpose_mul, hph, matrix.transpose_one],
end

end conjugates

end

end trace_eq_sum_roots

section dual_basis

open algebra

variables [decidable_eq ι] {b : ι → L} (hb : is_basis K b)

lemma nonsing_inv_det_zero (A : matrix ι ι K) (hA : det A = 0) :
  A⁻¹ = 0 :=
begin
  unfold has_inv.inv nonsing_inv,
  rw [hA, dif_neg not_is_unit_zero],
  apply_instance
end

lemma det_inv_ne_zero {A : matrix ι ι K} :
  det (A⁻¹) ≠ 0 ↔ det A ≠ 0 :=
begin
  by_cases hι : nonempty ι,
  swap,
  { have : fintype.card ι = 0,
    { rw fintype.card_eq_zero_iff, exact λ i, hι ⟨i⟩ },
    simp only [matrix.det_eq_one_of_card_eq_zero, matrix.det_eq_one_of_card_eq_zero this] },

  by_cases hA : det A = 0,
  { simp [hA, nonsing_inv_det_zero A hA, matrix.det_zero hι] },
  simp only [hA, ne.def, not_false_iff, iff_true],
  exact is_unit_iff_ne_zero.mp (is_unit_nonsing_inv_det A (is_unit.mk0 _ hA)),
end


include hb

/-- If `pb` is a power basis for the finite separable field extension `L / K`,
`dual_basis pb` is another basis such that
`trace_form (pb.gen ^ i) (dual_basis pb j) = if i = j then 1 else 0`. -/
noncomputable def dual_basis : ι → L :=
λ i, matrix.to_lin hb hb
  (bilin_form.to_matrix hb (trace_form K L))⁻¹ (b i)

lemma dual_basis_apply (i : ι) :
  dual_basis hb i = matrix.to_lin hb hb
    (bilin_form.to_matrix hb (trace_form K L))⁻¹ (b i) :=
rfl

lemma trace_form_dual_basis_power_basis [is_separable K L] (i j : ι) :
  trace_form K L (b i) (dual_basis hb j) = (1 : matrix _ _ K) i j :=
calc trace_form K L (b i) (dual_basis hb j)
    = ((bilin_form.to_matrix hb (trace_form K L)) ⬝
       (bilin_form.to_matrix hb (trace_form K L))⁻¹) i j :
  by simp_rw [dual_basis, ← bilin_form.comp_right_apply,
              bilin_form.to_matrix_mul hb, bilin_form.to_matrix_apply]
... = (1 : matrix _ _ K) i j :
  by rw matrix.mul_nonsing_inv _ (is_unit.mk0 _ (det_trace_form_ne_zero hb))

lemma trace_dual_basis_mul_power_basis [is_separable K L] (i j : ι) :
  algebra.trace K L (b i * dual_basis hb j) = if i = j then 1 else 0 :=
trace_form_dual_basis_power_basis hb i j

lemma is_basis_dual_basis [is_separable K L] :
  is_basis K (dual_basis hb) :=
  let e : L ≃ₗ[K] L := linear_equiv.of_bijective
    (matrix.to_lin hb hb (bilin_form.to_matrix hb (trace_form K L))⁻¹)
    (matrix.ker_to_lin_eq_bot hb _ (det_inv_ne_zero.mpr (det_trace_form_ne_zero _)))
    (matrix.range_to_lin_eq_top hb _ (det_inv_ne_zero.mpr (det_trace_form_ne_zero _)))
    in
@linear_equiv.is_basis ι _ _ _ _ _ _ _ _ _ hb e

lemma trace_gen_pow_mul [is_separable K L] (x : L) (i : ι) :
  algebra.trace K L (b i * x) = (is_basis_dual_basis hb).repr x i :=
begin
  calc algebra.trace K L (b i * x)
      = algebra.trace K L (b i * (∑ j, (is_basis_dual_basis hb).repr x j • dual_basis hb j)) :
    by rw sum_repr
  ... = algebra.trace K L (∑ j, (is_basis_dual_basis hb).repr x j • (b i * dual_basis hb j)) :
    by simp_rw [finset.mul_sum, mul_smul_comm]
  ... = ∑ j, (is_basis_dual_basis hb).repr x j • algebra.trace K L (b i * dual_basis hb j) :
    by simp_rw [linear_map.map_sum, linear_map.map_smul]
  ... = (is_basis_dual_basis hb).repr x i * algebra.trace K L (b i * dual_basis hb i) :
    finset.sum_eq_single _ _ _
  ... = (is_basis_dual_basis hb).repr x i :
    by rw [trace_dual_basis_mul_power_basis, if_pos rfl, mul_one],

  { intros j _ ne,
    rw [trace_dual_basis_mul_power_basis, if_neg ne.symm, smul_zero] },
  { intro not_mem_univ,
    have := finset.mem_univ i,
    contradiction }
end

end dual_basis

section trace_mem

open polynomial

variables {F : Type*} [field F] [algebra R L] [algebra L F] [algebra R F] [is_scalar_tower R L F]

lemma is_integral.nat_smul (n : ℕ) (x : F) (hx : is_integral R x) : is_integral R (n • x) :=
begin
  rw [algebra.smul_def, is_scalar_tower.algebra_map_apply ℕ R F],
  exact is_integral_mul is_integral_algebra_map hx,
end

lemma is_integral.multiset_sum (m : multiset F) :
  (∀ x ∈ m, is_integral R x) → is_integral R m.sum :=
begin
  refine m.induction _ _,
  { intros, simpa only [multiset.sum_zero] using is_integral_zero },
  { intros x m ih h,
    simpa [multiset.sum_cons] using
      is_integral_add
        (h x (multiset.mem_cons_self x m))
        (ih (λ x hx, h x (multiset.mem_cons.mpr (or.inr hx)))) }
end

lemma eval₂_dvd {R S : Type*} [semiring R] [comm_semiring S]
  {f : R →+* S} {p q : polynomial R} {x : S}
  (hpq : p ∣ q) : eval₂ f x p ∣ eval₂ f x q :=
begin
  rcases hpq with ⟨q, rfl⟩,
  exact ⟨eval₂ f x q, eval₂_mul f x⟩,
end

lemma eval₂_eq_zero_of_dvd_of_eval₂_eq_zero {R S : Type*} [semiring R] [comm_semiring S]
  {f : R →+* S} {p q : polynomial R} {x : S}
  (hpq : p ∣ q) (hxp : eval₂ f x p = 0) : eval₂ f x q = 0 :=
zero_dvd_iff.mp (dvd_trans (zero_dvd_iff.mpr hxp) (eval₂_dvd hpq))

lemma is_integral_trace [finite_dimensional L F] {x : F} (hx : is_integral R x) :
  is_integral R (algebra.trace L F x) :=
begin
  have hx' : is_integral L x := is_integral_of_is_scalar_tower _ hx,
  letI : algebra L (algebraic_closure F) := ((algebra_map F _).comp (algebra_map _ F)).to_algebra,
  letI : algebra R (algebraic_closure F) := ((algebra_map L _).comp (algebra_map _ L)).to_algebra,
  letI : is_scalar_tower L F (algebraic_closure F) := is_scalar_tower.of_algebra_map_eq (λ x, rfl),
  letI : is_scalar_tower R L (algebraic_closure F) := is_scalar_tower.of_algebra_map_eq (λ x, rfl),
  apply (is_integral_algebra_map_iff (algebra_map L (algebraic_closure F)).injective).mp,
  rw trace_eq_sum_roots hx',
  { apply is_integral.nat_smul,
    apply is_integral.multiset_sum,
    intros y hy,
    rw mem_roots_map (minpoly.ne_zero hx') at hy,
    use [minpoly R x, minpoly.monic hx],
    rw [← aeval_def, is_scalar_tower.aeval_apply R L, aeval_def],
    apply eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (minpoly.dvd L x _) hy,
    rw ← is_scalar_tower.aeval_apply R L,
    apply minpoly.aeval },
  { apply splits_of_is_alg_closed },
  { apply_instance }
end

end trace_mem
