/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.trace


/-!
# Trace of a matrix

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

variables (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
variables {ι : Type w} [decidable_eq ι] [fintype ι]
variables {κ : Type*} [decidable_eq κ] [fintype κ]
variables (b : basis ι R M) (c : basis κ R M)

/-- The trace of an endomorphism given a basis. -/
def trace_aux :
  (M →ₗ[R] M) →ₗ[R] R :=
(matrix.trace ι R R).comp $ linear_map.to_matrix b b

-- Can't be `simp` because it would cause a loop.
lemma trace_aux_def (b : basis ι R M) (f : M →ₗ[R] M) :
  trace_aux R b f = matrix.trace ι R R (linear_map.to_matrix b b f) :=
rfl

theorem trace_aux_eq : trace_aux R b = trace_aux R c :=
linear_map.ext $ λ f,
calc  matrix.trace ι R R (linear_map.to_matrix b b f)
    = matrix.trace ι R R (linear_map.to_matrix b b ((linear_map.id.comp f).comp linear_map.id)) :
  by rw [linear_map.id_comp, linear_map.comp_id]
... = matrix.trace ι R R (linear_map.to_matrix c b linear_map.id ⬝
        linear_map.to_matrix c c f ⬝
        linear_map.to_matrix b c linear_map.id) :
  by rw [linear_map.to_matrix_comp _ c, linear_map.to_matrix_comp _ c]
... = matrix.trace κ R R (linear_map.to_matrix c c f ⬝
        linear_map.to_matrix b c linear_map.id ⬝
        linear_map.to_matrix c b linear_map.id) :
  by rw [matrix.mul_assoc, matrix.trace_mul_comm]
... = matrix.trace κ R R (linear_map.to_matrix c c ((f.comp linear_map.id).comp linear_map.id)) :
  by rw [linear_map.to_matrix_comp _ b, linear_map.to_matrix_comp _ c]
... = matrix.trace κ R R (linear_map.to_matrix c c f) :
  by rw [linear_map.comp_id, linear_map.comp_id]

open_locale classical

theorem trace_aux_reindex_range [nontrivial R] : trace_aux R b.reindex_range = trace_aux R b :=
linear_map.ext $ λ f,
begin
  change ∑ i : set.range b, _ = ∑ i : ι, _, simp_rw [matrix.diag_apply], symmetry,
  convert (equiv.of_injective _ b.injective).sum_comp _, ext i,
  exact (linear_map.to_matrix_reindex_range b b f i i).symm
end

variables (R) (M)

/-- Trace of an endomorphism independent of basis. -/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
if H : ∃ (s : set M) (b : basis (s : set M) R M), s.finite
then @trace_aux R _ _ _ _ _ _ (classical.choice H.some_spec.some_spec) H.some_spec.some
else 0

variables (R) {M}

/-- Auxiliary lemma for `trace_eq_matrix_trace`. -/
theorem trace_eq_matrix_trace_of_finite_set {s : set M} (b : basis s R M) (hs : fintype s)
  (f : M →ₗ[R] M) :
  trace R M f = matrix.trace s R R (linear_map.to_matrix b b f) :=
have ∃ (s : set M) (b : basis (s : set M) R M), s.finite,
from ⟨s, b, ⟨hs⟩⟩,
by { rw [trace, dif_pos this, ← trace_aux_def], congr' 1, apply trace_aux_eq }

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
  trace R M f = matrix.trace ι R R (linear_map.to_matrix b b f) :=
if hR : nontrivial R
then by haveI := hR;
        rw [trace_eq_matrix_trace_of_finite_set R b.reindex_range (set.fintype_range b),
            ← trace_aux_def, ← trace_aux_def, trace_aux_reindex_range]
else @subsingleton.elim _ (not_nontrivial_iff_subsingleton.mp hR) _ _

theorem trace_mul_comm (f g : M →ₗ[R] M) :
  trace R M (f * g) = trace R M (g * f) :=
if H : ∃ (s : set M) (b : basis (s : set M) R M), s.finite then let ⟨s, b, hs⟩ := H in
by { haveI := classical.choice hs,
     simp_rw [trace_eq_matrix_trace R b, linear_map.to_matrix_mul], apply matrix.trace_mul_comm }
else by rw [trace, dif_neg H, linear_map.zero_apply, linear_map.zero_apply]

end linear_map
