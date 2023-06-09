/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/

import linear_algebra.eigenspace.basic
import field_theory.is_alg_closed.spectrum

/-!
# Eigenvectors and eigenvalues over algebraically closed fields.

* Every linear operator on a vector space over an algebraically closed field has an eigenvalue.
* The generalized eigenvectors span the entire vector space.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

universes u v w

namespace module
namespace End

open finite_dimensional

variables {K : Type v} {V : Type w} [field K] [add_comm_group V] [module K V]

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. -/
-- This is Lemma 5.21 of [axler2015], although we are no longer following that proof.
lemma exists_eigenvalue [is_alg_closed K] [finite_dimensional K V] [nontrivial V] (f : End K V) :
  ∃ (c : K), f.has_eigenvalue c :=
by { simp_rw has_eigenvalue_iff_mem_spectrum,
     exact spectrum.nonempty_of_is_alg_closed_of_finite_dimensional K f }

noncomputable instance [is_alg_closed K] [finite_dimensional K V] [nontrivial V] (f : End K V) :
  inhabited f.eigenvalues :=
⟨⟨f.exists_eigenvalue.some, f.exists_eigenvalue.some_spec⟩⟩

/-- The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/
lemma supr_generalized_eigenspace_eq_top [is_alg_closed K] [finite_dimensional K V] (f : End K V) :
  (⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k) = ⊤ :=
begin
  -- We prove the claim by strong induction on the dimension of the vector space.
  unfreezingI { induction h_dim : finrank K V using nat.strong_induction_on
  with n ih generalizing V },
  cases n,
  -- If the vector space is 0-dimensional, the result is trivial.
  { rw ←top_le_iff,
    simp only [finrank_eq_zero.1 (eq.trans (finrank_top _ _) h_dim), bot_le] },
  -- Otherwise the vector space is nontrivial.
  { haveI : nontrivial V := finrank_pos_iff.1 (by { rw h_dim, apply nat.zero_lt_succ }),
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.has_eigenvalue μ₀ := exists_eigenvalue f,
    -- We define `ES` to be the generalized eigenspace
    let ES := f.generalized_eigenspace μ₀ (finrank K V),
    -- and `ER` to be the generalized eigenrange.
    let ER := f.generalized_eigenrange μ₀ (finrank K V),
    -- `f` maps `ER` into itself.
    have h_f_ER : ∀ (x : V), x ∈ ER → f x ∈ ER,
      from λ x hx, map_generalized_eigenrange_le (submodule.mem_map_of_mem hx),
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER,
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES,
    { dsimp only [ES],
      rw h_dim,
      apply pos_finrank_generalized_eigenspace_of_has_eigenvalue hμ₀ (nat.zero_lt_succ n) },
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V,
    { apply linear_map.finrank_range_add_finrank_ker },
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ, by linarith,
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : (⨆ (μ : K) (k : ℕ), f'.generalized_eigenspace μ k) = ⊤,
      from ih (finrank K ER) h_dim_ER f' rfl,
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `submodule.subtype`:
    have ih_ER' : (⨆ (μ : K) (k : ℕ), (f'.generalized_eigenspace μ k).map ER.subtype) = ER,
      by simp only [(submodule.map_supr _ _).symm, ih_ER, submodule.map_subtype_top ER],
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' : ∀ μ k,
        (f'.generalized_eigenspace μ k).map ER.subtype ≤ f.generalized_eigenspace μ k,
    { intros,
      rw generalized_eigenspace_restrict,
      apply submodule.map_comap_le },
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k,
    { rw ← ih_ER',
      exact supr₂_mono hff' },
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k,
      from le_trans
        (le_supr (λ k, f.generalized_eigenspace μ₀ k) (finrank K V))
        (le_supr (λ (μ : K), ⨆ (k : ℕ), f.generalized_eigenspace μ k) μ₀),
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : disjoint ER ES,
      from generalized_eigenvec_disjoint_range_ker f μ₀,
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    show (⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k) = ⊤,
    { rw [←top_le_iff, ←submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint],
      apply sup_le hER hES } }
end

end End
end module
