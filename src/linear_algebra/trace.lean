/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle
-/
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.trace
import linear_algebra.contraction
import linear_algebra.tensor_product_basis
import linear_algebra.free_module.strong_rank_condition
import linear_algebra.free_module.finite.rank
import linear_algebra.projection

/-!
# Trace of a linear map

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the trace of a linear map.

See also `linear_algebra/matrix/trace.lean` for the trace of a matrix.

## Tags

linear_map, trace, diagonal

-/

noncomputable theory

universes u v w

namespace linear_map

open_locale big_operators
open_locale matrix
open finite_dimensional

open_locale tensor_product

section
variables (R : Type u) [comm_semiring R] {M : Type v} [add_comm_monoid M] [module R M]
variables {ι : Type w} [decidable_eq ι] [fintype ι]
variables {κ : Type*} [decidable_eq κ] [fintype κ]
variables (b : basis ι R M) (c : basis κ R M)

/-- The trace of an endomorphism given a basis. -/
def trace_aux :
  (M →ₗ[R] M) →ₗ[R] R :=
(matrix.trace_linear_map ι R R) ∘ₗ ↑(linear_map.to_matrix b b)

-- Can't be `simp` because it would cause a loop.
lemma trace_aux_def (b : basis ι R M) (f : M →ₗ[R] M) :
  trace_aux R b f = matrix.trace (linear_map.to_matrix b b f) :=
rfl

theorem trace_aux_eq : trace_aux R b = trace_aux R c :=
linear_map.ext $ λ f,
calc  matrix.trace (linear_map.to_matrix b b f)
    = matrix.trace (linear_map.to_matrix b b ((linear_map.id.comp f).comp linear_map.id)) :
  by rw [linear_map.id_comp, linear_map.comp_id]
... = matrix.trace (linear_map.to_matrix c b linear_map.id ⬝
        linear_map.to_matrix c c f ⬝
        linear_map.to_matrix b c linear_map.id) :
  by rw [linear_map.to_matrix_comp _ c, linear_map.to_matrix_comp _ c]
... = matrix.trace (linear_map.to_matrix c c f ⬝
        linear_map.to_matrix b c linear_map.id ⬝
        linear_map.to_matrix c b linear_map.id) :
  by rw [matrix.mul_assoc, matrix.trace_mul_comm]
... = matrix.trace (linear_map.to_matrix c c ((f.comp linear_map.id).comp linear_map.id)) :
  by rw [linear_map.to_matrix_comp _ b, linear_map.to_matrix_comp _ c]
... = matrix.trace (linear_map.to_matrix c c f) :
  by rw [linear_map.comp_id, linear_map.comp_id]

open_locale classical

variables (R) (M)

/-- Trace of an endomorphism independent of basis. -/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
if H : ∃ (s : finset M), nonempty (basis s R M)
then trace_aux R H.some_spec.some
else 0

variables (R) {M}

/-- Auxiliary lemma for `trace_eq_matrix_trace`. -/
theorem trace_eq_matrix_trace_of_finset {s : finset M} (b : basis s R M)
  (f : M →ₗ[R] M) :
  trace R M f = matrix.trace (linear_map.to_matrix b b f) :=
have ∃ (s : finset M), nonempty (basis s R M),
from ⟨s, ⟨b⟩⟩,
by { rw [trace, dif_pos this, ← trace_aux_def], congr' 1, apply trace_aux_eq }

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
  trace R M f = matrix.trace (linear_map.to_matrix b b f) :=
by rw [trace_eq_matrix_trace_of_finset R b.reindex_finset_range,
    ← trace_aux_def, ← trace_aux_def, trace_aux_eq R b]

theorem trace_mul_comm (f g : M →ₗ[R] M) :
  trace R M (f * g) = trace R M (g * f) :=
if H : ∃ (s : finset M), nonempty (basis s R M) then let ⟨s, ⟨b⟩⟩ := H in
by { simp_rw [trace_eq_matrix_trace R b, linear_map.to_matrix_mul], apply matrix.trace_mul_comm }
else by rw [trace, dif_neg H, linear_map.zero_apply, linear_map.zero_apply]

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
theorem trace_conj (g : M →ₗ[R] M) (f : (M →ₗ[R] M)ˣ) :
  trace R M (↑f * g * ↑f⁻¹) = trace R M g :=
by { rw trace_mul_comm, simp }

end

section

variables {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
variables (N : Type*) [add_comm_group N] [module R N]
variables {ι : Type*}

/-- The trace of a linear map correspond to the contraction pairing under the isomorphism
 `End(M) ≃ M* ⊗ M`-/
lemma trace_eq_contract_of_basis [finite ι] (b : basis ι R M) :
  (linear_map.trace R M) ∘ₗ (dual_tensor_hom R M M) = contract_left R M :=
begin
  classical,
  casesI nonempty_fintype ι,
  apply basis.ext (basis.tensor_product (basis.dual_basis b) b),
  rintros ⟨i, j⟩,
  simp only [function.comp_app, basis.tensor_product_apply, basis.coe_dual_basis, coe_comp],
  rw [trace_eq_matrix_trace R b, to_matrix_dual_tensor_hom],
  by_cases hij : i = j,
  { rw [hij], simp },
  rw matrix.std_basis_matrix.trace_zero j i (1:R) hij,
  simp [finsupp.single_eq_pi_single, hij],
end

/-- The trace of a linear map correspond to the contraction pairing under the isomorphism
 `End(M) ≃ M* ⊗ M`-/
lemma trace_eq_contract_of_basis' [fintype ι] [decidable_eq ι] (b : basis ι R M) :
  (linear_map.trace R M) =
  (contract_left R M) ∘ₗ (dual_tensor_hom_equiv_of_basis b).symm.to_linear_map :=
by simp [linear_equiv.eq_comp_to_linear_map_symm, trace_eq_contract_of_basis b]

variables (R M N)
variables [module.free R M] [module.finite R M] [module.free R N] [module.finite R N] [nontrivial R]

/-- When `M` is finite free, the trace of a linear map correspond to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`-/
@[simp] theorem trace_eq_contract :
  (linear_map.trace R M) ∘ₗ (dual_tensor_hom R M M) = contract_left R M :=
trace_eq_contract_of_basis (module.free.choose_basis R M)

@[simp] theorem trace_eq_contract_apply (x : module.dual R M ⊗[R] M) :
  (linear_map.trace R M) ((dual_tensor_hom R M M) x) = contract_left R M x :=
by rw [←comp_apply, trace_eq_contract]

open_locale classical

/-- When `M` is finite free, the trace of a linear map correspond to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`-/
theorem trace_eq_contract' :
  (linear_map.trace R M) =
  (contract_left R M) ∘ₗ (dual_tensor_hom_equiv R M M).symm.to_linear_map :=
trace_eq_contract_of_basis' (module.free.choose_basis R M)

/-- The trace of the identity endomorphism is the dimension of the free module -/
@[simp] theorem trace_one : trace R M 1 = (finrank R M : R) :=
begin
  have b := module.free.choose_basis R M,
  rw [trace_eq_matrix_trace R b, to_matrix_one, finrank_eq_card_choose_basis_index],
  simp,
end

/-- The trace of the identity endomorphism is the dimension of the free module -/
@[simp] theorem trace_id : trace R M id = (finrank R M : R) :=
by rw [←one_eq_id, trace_one]

@[simp] theorem trace_transpose : trace R (module.dual R M) ∘ₗ module.dual.transpose = trace R M :=
begin
  let e := dual_tensor_hom_equiv R M M,
  have h : function.surjective e.to_linear_map := e.surjective,
  refine (cancel_right h).1 _,
  ext f m, simp [e],
end

theorem trace_prod_map :
  trace R (M × N) ∘ₗ prod_map_linear R M N M N R =
  (coprod id id : R × R →ₗ[R] R) ∘ₗ prod_map (trace R M) (trace R N) :=
begin
  let e := ((dual_tensor_hom_equiv R M M).prod (dual_tensor_hom_equiv R N N)),
  have h : function.surjective e.to_linear_map := e.surjective,
  refine (cancel_right h).1 _,
  ext,
  { simp only [dual_tensor_hom_equiv, tensor_product.algebra_tensor_module.curry_apply,
  to_fun_eq_coe, tensor_product.curry_apply, coe_restrict_scalars_eq_coe, coe_comp,
  linear_equiv.coe_to_linear_map, coe_inl, function.comp_app, linear_equiv.prod_apply,
  dual_tensor_hom_equiv_of_basis_apply, map_zero, prod_map_apply, coprod_apply, id_coe, id.def,
  add_zero, prod_map_linear_apply, dual_tensor_hom_prod_map_zero, trace_eq_contract_apply,
  contract_left_apply, fst_apply] },
  { simp only [dual_tensor_hom_equiv, tensor_product.algebra_tensor_module.curry_apply,
  to_fun_eq_coe, tensor_product.curry_apply, coe_restrict_scalars_eq_coe, coe_comp,
  linear_equiv.coe_to_linear_map, coe_inr, function.comp_app, linear_equiv.prod_apply,
  dual_tensor_hom_equiv_of_basis_apply, map_zero, prod_map_apply, coprod_apply, id_coe, id.def,
  zero_add, prod_map_linear_apply, zero_prod_map_dual_tensor_hom, trace_eq_contract_apply,
  contract_left_apply, snd_apply], },
end

variables {R M N}

theorem trace_prod_map' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
  trace R (M × N) (prod_map f g) = trace R M f + trace R N g :=
begin
  have h := ext_iff.1 (trace_prod_map R M N) (f, g),
  simp only [coe_comp, function.comp_app, prod_map_apply, coprod_apply, id_coe, id.def,
  prod_map_linear_apply] at h, exact h,
end

variables (R M N)

open tensor_product function

theorem trace_tensor_product :
  compr₂ (map_bilinear R M N M N) (trace R (M ⊗ N)) =
  compl₁₂ (lsmul R R : R →ₗ[R] R →ₗ[R] R) (trace R M) (trace R N) :=
begin
  apply (compl₁₂_inj
    (show surjective (dual_tensor_hom R M M), from (dual_tensor_hom_equiv R M M).surjective)
    (show surjective (dual_tensor_hom R N N), from (dual_tensor_hom_equiv R N N).surjective)).1,
  ext f m g n,
  simp only [algebra_tensor_module.curry_apply, to_fun_eq_coe, tensor_product.curry_apply,
  coe_restrict_scalars_eq_coe, compl₁₂_apply, compr₂_apply, map_bilinear_apply,
  trace_eq_contract_apply, contract_left_apply, lsmul_apply, algebra.id.smul_eq_mul,
  map_dual_tensor_hom, dual_distrib_apply],
end

theorem trace_comp_comm :
  compr₂ (llcomp R M N M) (trace R M) = compr₂ (llcomp R N M N).flip (trace R N) :=
begin
  apply (compl₁₂_inj
    (show surjective (dual_tensor_hom R N M), from (dual_tensor_hom_equiv R N M).surjective)
    (show surjective (dual_tensor_hom R M N), from (dual_tensor_hom_equiv R M N).surjective)).1,
  ext g m f n,
  simp only [tensor_product.algebra_tensor_module.curry_apply, to_fun_eq_coe,
      linear_equiv.coe_to_linear_map, tensor_product.curry_apply, coe_restrict_scalars_eq_coe,
      compl₁₂_apply, compr₂_apply, flip_apply, llcomp_apply', comp_dual_tensor_hom, map_smul,
      trace_eq_contract_apply, contract_left_apply, smul_eq_mul, mul_comm],
end

variables {R M N}

@[simp]
theorem trace_transpose' (f : M →ₗ[R] M) : trace R _ (module.dual.transpose f) = trace R M f :=
by { rw [←comp_apply, trace_transpose] }

theorem trace_tensor_product' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
  trace R (M ⊗ N) (map f g) = trace R M f * trace R N g :=
begin
  have h := ext_iff.1 (ext_iff.1 (trace_tensor_product R M N) f) g,
  simp only [compr₂_apply, map_bilinear_apply, compl₁₂_apply, lsmul_apply,
    algebra.id.smul_eq_mul] at h, exact h,
end

theorem trace_comp_comm' (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
  trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g) :=
begin
  have h := ext_iff.1 (ext_iff.1 (trace_comp_comm R M N) g) f,
  simp only [llcomp_apply', compr₂_apply, flip_apply] at h,
  exact h,
end

@[simp] theorem trace_conj' (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) : trace R N (e.conj f) = trace R M f :=
by rw [e.conj_apply, trace_comp_comm', ←comp_assoc, linear_equiv.comp_coe,
  linear_equiv.self_trans_symm, linear_equiv.refl_to_linear_map, id_comp]

theorem is_proj.trace {p : submodule R M} {f : M →ₗ[R] M} (h : is_proj p f)
  [module.free R p] [module.finite R p] [module.free R f.ker] [module.finite R f.ker] :
  trace R M f = (finrank R p : R) :=
by rw [h.eq_conj_prod_map, trace_conj', trace_prod_map', trace_id, map_zero, add_zero]

end

end linear_map
