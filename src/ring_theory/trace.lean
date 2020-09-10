/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import field_theory.adjoin
import field_theory.simple_extension
import linear_algebra.bilinear_form
import linear_algebra.char_poly.coeff
import ring_theory.algebra_tower

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/

universes u v w

variables (R S T : Type*) [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables (K L : Type*) [field K] [field L] [algebra K L]
variables {ι : Type w} [fintype ι] {b : ι → S} (hb : is_basis R b)

open finite_dimensional
open linear_map
open matrix

open_locale big_operators
open_locale matrix

namespace algebra

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R := (linear_map.trace R S).comp (lmul R S)

@[simp] lemma trace_apply (s : S) : trace R S s = linear_map.trace R S (lmul R S s) := rfl

lemma trace_eq_zero_of_not_exists_basis
  (h : ¬ ∃ s : finset S, is_basis R (λ x, x : (↑s : set S) → S)) : trace R S = 0 :=
by { ext s, simp [linear_map.trace, h] }

lemma findim_eq_zero_of_not_exists_basis
  (h : ¬ ∃ s : finset L, is_basis K (λ x, x : (↑s : set L) → L)) : findim K L = 0 :=
dif_neg (mt (λ h, @exists_is_basis_finset K L _ _ _ (finite_dimensional_iff_dim_lt_omega.mpr h)) h)

theorem smul_id (r : R) : r • linear_map.id = lsmul R S r := rfl

@[simp] lemma lmul_algebra_map (x : R) : lmul R S (algebra_map R S x) = lsmul R S x :=
linear_map.ext (λ s, by simp [smul_def''])

@[simp] lemma linear_equiv_matrix_id [decidable_eq ι] :
  linear_equiv_matrix hb hb linear_map.id = 1 :=
by convert (linear_equiv_matrix_comp hb hb hb id ((linear_equiv_matrix hb hb).inv_fun 1)).symm; simp

@[simp] lemma linear_equiv_matrix_lmul [decidable_eq ι] (x : S) (i j) :
  linear_equiv_matrix hb hb (lmul R S x) i j = hb.repr (x * b j) i :=
by rw [linear_equiv_matrix_apply', lmul_apply]

include hb
/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
lemma trace_algebra_map_of_basis (x : R) :
  trace R S (algebra_map R S x) = fintype.card ι • x :=
begin
  rw [trace_apply, trace_eq_matrix_trace R hb, trace_diag],
  convert finset.sum_const _,
  ext i,
  simp [←smul_id]
end
omit hb

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
@[simp]
lemma trace_algebra_map (x : K) : trace K L (algebra_map K L x) = findim K L • x :=
begin
  by_cases H : ∃ s : finset L, is_basis K (λ x, x : (↑s : set L) → L),
  { rw [trace_algebra_map_of_basis K L H.some_spec, findim_eq_card_basis H.some_spec] },
  { simp [trace_eq_zero_of_not_exists_basis K L H, findim_eq_zero_of_not_exists_basis K L H] },
end

lemma linear_equiv.map_sum {R : Type u} {M : Type v} {M₂ : Type w}
  [semiring R] [add_comm_monoid M]
  [add_comm_monoid M₂] [semimodule R M] [semimodule R M₂]
  (f : M ≃ₗ[R] M₂) {ι : Type u_1} {t : finset ι} {g : ι → M} :
  f (t.sum (λ (i : ι), g i)) = t.sum (λ (i : ι), f (g i)) :=
f.to_linear_map.map_sum

section trace_form

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : bilin_form R S :=
{ bilin := λ x y, trace R S (x * y),
  bilin_add_left := λ x y z, by rw [add_mul, linear_map.map_add],
  bilin_smul_left := λ x y z, by rw [smul_mul_assoc, linear_map.map_smul, smul_eq_mul],
  bilin_add_right := λ x y z, by rw [mul_add, linear_map.map_add],
  bilin_smul_right := λ x y z, by rw [mul_smul_comm, linear_map.map_smul, smul_eq_mul], }

@[simp] lemma trace_form_apply (x y : S) : trace_form R S x y = trace R S (x * y) := rfl

lemma trace_form_is_sym : sym_bilin_form.is_sym (trace_form R S) :=
λ x y, congr_arg (trace R S) (mul_comm _ _)

lemma trace_form_to_matrix [decidable_eq ι] (i j) :
  bilin_form_equiv_matrix hb (trace_form R S) i j = trace R S (b i * b j) :=
by rw [bilin_form_equiv_matrix_apply, trace_form_apply]

open bilin_form

lemma lmul_mul (x y : S) : lmul R S (x * y) = (lmul R S x).comp (lmul R S y) :=
by { ext z, simp [mul_assoc] }

lemma matrix.trace_apply (A : matrix ι ι S) : matrix.trace ι R S A = ∑ i, A i i := rfl

open is_simple_extension

lemma linear_equiv_matrix_lmul [is_simple_extension K L] (alg : is_algebraic K L)
  [decidable_eq ι] (x : L) (b : ι → L) (hb : is_basis K⟮x⟯ b) :
  linear_equiv_matrix (power_basis (K⟮x⟯.is_algebraic_iff.mp _)) (lmul R S x) :=
begin

end

lemma trace_comp_of_basis [algebra S T] [is_scalar_tower R S T]
{ι κ : Type*} [fintype ι] [fintype κ] [decidable_eq ι] [decidable_eq κ] {b : ι → S} {c : κ → T}
(hb : is_basis R b) (hc : is_basis S c) (x : T) :
trace R T x = trace R S (trace S T x) :=
begin
haveI hι : nonempty ι := _,
haveI hκ : nonempty κ := _,
haveI : nonempty (ι × κ) := prod.nonempty,
rw [trace_apply R T, trace_eq_matrix_trace R (hb.smul hc)],
have := trace_eq_neg_char_poly_coeff (linear_equiv_matrix (hb.smul hc) (hb.smul hc) (lmul R T x)),
simp at this ⊢,
refine trans this _,
end

lemma repr_primitive_element_pow_of_lt'
  [is_simple_extension K L] (alg : is_algebraic K L) (n : fin (simple_degree alg)) :
  (power_basis_is_basis alg).repr (primitive_element K L ^ (n : ℕ)) = finsupp.single n 1 :=
is_basis.repr_eq_single (power_basis_is_basis alg)

lemma repr_primitive_element_pow_of_lt
  [is_simple_extension K L] (alg : is_algebraic K L) {n : ℕ} (hn : n < simple_degree alg) (i) :
  (power_basis_is_basis alg).repr (primitive_element K L ^ (n : ℕ)) i = if n = i then 1 else 0 :=
by { rw [← fin.coe_mk hn, (repr_primitive_element_pow_of_lt' _ _ alg ⟨n, hn⟩),
         finsupp.single_apply, fin.ext_iff], congr' 1 }

@[simp] lemma finsupp.finset_sum_apply {α α₁ β : Type*} [add_comm_monoid β]
  {s : finset α₁} {g : α₁ → α →₀ β} {a₂ : α} :
  (s.sum g) a₂ = s.sum (λa₁, g a₁ a₂) :=
(finsupp.eval_add_hom a₂ : (α →₀ β) →+ _).map_sum _ _

variables {K L}

lemma repr_primitive_element_pow_simple_degree
  [is_simple_extension K L] (alg : is_algebraic K L) (i) :
  (power_basis_is_basis alg).repr (primitive_element K L ^ simple_degree alg) i =
    - (minimal_polynomial alg).coeff i :=
begin
  unfold simple_degree,
  have : ∀ {p : polynomial K} (hp : p.monic) (x : L),
    x ^ p.nat_degree = polynomial.aeval x p - ∑ i in finset.range p.nat_degree, p.coeff i • x^i,
  { intros p hp x,
    conv_rhs { congr, { rw hp.as_sum } },
    rw [alg_hom.map_add, alg_hom.map_pow, polynomial.aeval_X, add_sub_assoc, alg_hom.map_sum,
        ← finset.sum_sub_distrib],
    convert (add_zero _).symm,
    refine finset.sum_eq_zero (λ i hi, _),
    rw [alg_hom.map_mul, alg_hom.map_pow, polynomial.aeval_C, polynomial.aeval_X, smul_def, sub_self] },

  erw [this (show (minimal_polynomial alg).monic, from minimal_polynomial.monic _),
      minimal_polynomial.aeval],
  rw [zero_sub, linear_map.map_neg, linear_map.map_sum, finsupp.neg_apply, finsupp.finset_sum_apply,
      ← finset.sum_attach, neg_inj],
  convert finset.sum_ite_eq (finset.range (minimal_polynomial alg).nat_degree) i
    (λ i, (minimal_polynomial alg).coeff i) using 1,
  { conv_rhs { rw ← finset.sum_attach },
    apply finset.sum_congr rfl,
    intros j hj,
    rw [linear_map.map_smul, finsupp.smul_apply, smul_eq_mul],
    erw repr_primitive_element_pow_of_lt _ _ alg (finset.mem_range.mp j.2) i,
    rw mul_boole, simp [eq_comm] },
  { exact (if_pos (finset.mem_range.mpr i.2)).symm }
end

lemma linear_equiv_matrix_lmul_primitive_element_pow_of_lt
  [is_simple_extension K L] (alg : is_algebraic K L) {n : ℕ} (i j : fin _) (hn : n + (j : ℕ) < simple_degree alg) :
  linear_equiv_matrix (power_basis_is_basis alg) (power_basis_is_basis alg)
      (lmul K L (primitive_element K L ^ n)) i j =
    if n + (j : ℕ) = i then 1 else 0 :=
by rw [linear_equiv_matrix_apply', lmul_apply, power_basis_apply, ←pow_add, repr_primitive_element_pow_of_lt K L alg hn]

#check nat.sub_le_iff

lemma linear_equiv_matrix_lmul_primitive_element_pow
  [is_simple_extension K L] (alg : is_algebraic K L) {n : ℕ} (i j : fin _) (hn : n < simple_degree alg) :
  linear_equiv_matrix (power_basis_is_basis alg) (power_basis_is_basis alg)
      (lmul K L (primitive_element K L ^ n)) i j =
    if n + (j : ℕ) < simple_degree alg
    then if n + (j : ℕ) = i then 1 else 0
    else sorry :=
begin
  split_ifs with hj hi,
  { rw [linear_equiv_matrix_apply', lmul_apply, power_basis_apply, ←pow_add, repr_primitive_element_pow_of_lt K L alg hj, if_pos hi] },
  { rw [linear_equiv_matrix_apply', lmul_apply, power_basis_apply, ←pow_add, repr_primitive_element_pow_of_lt K L alg hj, if_neg hi] },
  replace hj := nat.sub_le_right_iff_le_add.mpr (le_of_not_gt hj),
  obtain ⟨n', rfl⟩ := nat.exists_eq_add_of_le hj,
  rw [pow_add, lmul_mul, linear_equiv_matrix_comp _ (power_basis_is_basis alg), matrix.mul_apply],
  simp_rw linear_equiv_matrix_lmul_primitive_element_pow_of_lt,
  sorry
end

lemma sum_repr (x : S) : ∑ i, hb.repr x i • b i = x :=
begin
  convert hb.total_repr x using 1,
  rw finsupp.total_apply,
  refine (finset.sum_subset (finset.subset_univ _) (λ i _ hi, _)).symm,
  rw [finsupp.not_mem_support_iff.mp hi, zero_smul]
end

lemma lmul_one : lmul R S 1 = linear_map.id :=
by { ext, simp }

lemma trace_form.nondegenerate [finite_dimensional K L] [is_separable K L] :
  (trace_form K L).nondegenerate :=
begin
  rw nondegenerate_iff_eq_zero,
  intros x hxy,
  have alg : is_algebraic K L := is_algebraic_of_finite,
  have hb := power_basis_is_basis alg,
  haveI := classical.prop_decidable,
  by_contra hx,
  have trace_eq_zero : ∀ (z : L), trace K L z = 0,
  { intro z,
    convert hxy (x⁻¹ * z),
    rw [←mul_assoc, mul_inv_cancel hx, one_mul] },
  have trace_primitive_element : ∀ i < simple_degree alg,
    trace K L (primitive_element K L ^ (i : ℕ)) = (minimal_polynomial alg).coeff (simple_degree alg - i),
  { intro i,
    induction i with i ih,
    { sorry },
    { intro hi,
      rw pow_succ } },

/-
  use x⁻¹ * is_simple_extension.primitive_element K L,
  rw [trace_form_apply, ← mul_assoc, mul_inv_cancel hxy, one_mul, trace_apply,
      linear_map.trace_eq_matrix_trace K hb, matrix.trace_apply],
  simp_rw [linear_equiv_matrix_apply' hb hb],
  -/
end

end trace_form

end algebra
