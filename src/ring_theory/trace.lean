/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import linear_algebra.bilinear_form
import linear_algebra.matrix
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

@[simp] lemma linear_equiv_matrix_id {ι : Type w} [fintype ι] [decidable_eq ι]
  {b : ι → S} (hb : is_basis R b) :
  linear_equiv_matrix hb hb linear_map.id = 1 :=
by convert (linear_equiv_matrix_comp hb hb hb id ((linear_equiv_matrix hb hb).inv_fun 1)).symm; simp

lemma linear_equiv_matrix_apply [decidable_eq ι]
  {κ : Type*} [fintype κ] [decidable_eq κ] {c : κ → T} (hc : is_basis R c)
  (e : S →ₗ[R] T) (i j) : linear_equiv_matrix hb hc e i j = equiv_fun_basis hc (e (b j)) i :=
by simp only [linear_equiv_matrix, to_matrix, to_matrixₗ, ite_smul,
  linear_equiv.trans_apply, linear_equiv.arrow_congr_apply,
  linear_equiv.coe_coe, linear_equiv_matrix'_apply, finset.mem_univ, if_true,
  one_smul, zero_smul, finset.sum_ite_eq, equiv_fun_basis_symm_apply]

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
  f (t.sum (λ (i : ι), g i)) = t.sum (λ (i : ι), f (g i)) := linear_map.map_sum f.to_linear_map

lemma trace_comp_of_basis [algebra S T] [is_algebra_tower R S T]
  {ι κ : Type*} [fintype ι] [fintype κ] [decidable_eq ι] [decidable_eq κ] {b : ι → S} {c : κ → T}
  (hb : is_basis R b) (hc : is_basis S c) (x : T) :
  trace R T x = trace R S (trace S T x) :=
begin
  rw [trace_apply R S, trace_eq_matrix_trace R hb, trace_diag,
      trace_apply S T, trace_eq_matrix_trace S hc, trace_diag,
      trace_apply R T, trace_eq_matrix_trace R (hb.smul hc), trace_diag],
    refine trans finset.sum_product _,
  congr, ext i,
  simp_rw [diag_apply, linear_map.map_sum, linear_equiv.map_sum, finset.sum_apply],
  congr, ext j,
  sorry
end

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

end trace_form

end algebra
