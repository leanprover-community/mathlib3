/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.finiteness
import linear_algebra.dimension

/-!
# A module over a division ring is noetherian if and only if it is finite.

-/

universes u v

open_locale classical
open cardinal submodule module function

namespace is_noetherian

variables {K : Type u} {V : Type v} [division_ring K] [add_comm_group V] [module K V]

-- PROJECT: Show all division rings are noetherian.
-- This is currently annoying because we only have ideal of commutative rings.
variables [is_noetherian_ring K]

/--
A module over a division ring is noetherian if and only if
its dimension (as a cardinal) is strictly less than the first infinite cardinal `omega`.
-/
lemma iff_dim_lt_omega : is_noetherian K V ↔ module.rank K V < omega.{v} :=
begin
  let b := basis.of_vector_space K V,
  rw [← b.mk_eq_dim'', lt_omega_iff_finite],
  split,
  { introI,
    exact finite_of_linear_independent (basis.of_vector_space_index.linear_independent K V) },
  { assume hbfinite,
    refine @is_noetherian_of_linear_equiv K (⊤ : submodule K V) V _
      _ _ _ _ (linear_equiv.of_top _ rfl) (id _),
    refine is_noetherian_of_fg_of_noetherian _ ⟨set.finite.to_finset hbfinite, _⟩,
    rw [set.finite.coe_to_finset, ← b.span_eq, basis.coe_of_vector_space, subtype.range_coe] }
end

variables (K V)

/-- The dimension of a noetherian module over a division ring, as a cardinal,
is strictly less than the first infinite cardinal `omega`. -/
lemma dim_lt_omega : ∀ [is_noetherian K V], module.rank K V < omega.{v} :=
is_noetherian.iff_dim_lt_omega.1

variables {K V}

/-- In a noetherian module over a division ring, all bases are indexed by a finite type. -/
noncomputable def fintype_basis_index {ι : Type*} [is_noetherian K V] (b : basis ι K V) :
  fintype ι :=
b.fintype_index_of_dim_lt_omega (dim_lt_omega K V)

/-- In a noetherian module over a division ring,
`basis.of_vector_space` is indexed by a finite type. -/
noncomputable instance [is_noetherian K V] : fintype (basis.of_vector_space_index K V) :=
fintype_basis_index (basis.of_vector_space K V)

/-- In a noetherian module over a division ring,
if a basis is indexed by a set, that set is finite. -/
lemma finite_basis_index {ι : Type*} {s : set ι} [is_noetherian K V] (b : basis s K V) :
  s.finite :=
b.finite_index_of_dim_lt_omega (dim_lt_omega K V)

variables (K V)

/-- In a noetherian module over a division ring,
there exists a finite basis. This is the indexing `finset`. -/
noncomputable def finset_basis_index [is_noetherian K V] :
  finset V :=
(finite_basis_index (basis.of_vector_space K V)).to_finset

@[simp] lemma coe_finset_basis_index [is_noetherian K V] :
  (↑(finset_basis_index K V) : set V) = basis.of_vector_space_index K V :=
set.finite.coe_to_finset _

@[simp] lemma coe_sort_finset_basis_index [is_noetherian K V] :
  ((finset_basis_index K V) : Type*) = basis.of_vector_space_index K V :=
set.finite.coe_sort_to_finset _

/--
In a noetherian module over a division ring, there exists a finite basis.
This is indexed by the `finset` `finite_dimensional.finset_basis_index`.
This is in contrast to the result `finite_basis_index (basis.of_vector_space K V)`,
which provides a set and a `set.finite`.
-/
noncomputable def finset_basis [is_noetherian K V] :
  basis (finset_basis_index K V) K V :=
(basis.of_vector_space K V).reindex (by simp)

@[simp] lemma range_finset_basis [is_noetherian K V] :
  set.range (finset_basis K V) = basis.of_vector_space_index K V :=
by rw [finset_basis, basis.range_reindex, basis.range_of_vector_space]

variables {K V}

/-- A module over a division ring is noetherian if and only if it is finitely generated. -/
lemma iff_fg :
  is_noetherian K V ↔ module.finite K V :=
begin
  split,
  { introI h,
    exact ⟨⟨finset_basis_index K V, by { convert (finset_basis K V).span_eq, simp }⟩⟩ },
  { rintros ⟨s, hs⟩,
    rw [is_noetherian.iff_dim_lt_omega, ← dim_top, ← hs],
    exact lt_of_le_of_lt (dim_span_le _) (lt_omega_iff_finite.2 (set.finite_mem_finset s)) }
end

end is_noetherian
