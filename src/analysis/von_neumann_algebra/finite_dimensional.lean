/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.von_neumann_algebra.basic
import analysis.inner_product_space.finite_dimensional

/-!

# Finite-dimensional von Neumann algebras

In this file, we prove some results in finite-dimensional von Neumann algebras.

## Notation

We let `V` be a finite-dimensional inner product space over `ℂ`.

## Main results

* `idempotent_in_vN_iff_ker_and_range_are_centralizer_invariant`:
idempotent `e ∈ L(V)` is in von Neumann algebra `M` if and only if
`e.range,e.ker` are `M'` (i.e., commutant of `M` or `M.centralizer`)
invariant subspaces

-/

variables {V : Type*} [inner_product_space ℂ V] [finite_dimensional ℂ V]

open continuous_linear_map

/-- Let `e ∈ L(V)` be an idempotent operator.
Then `e ∈ M` if and only if `e.ker` and `e.range` are `M'`
(i.e., the commutant of `M` or `M.centralizer`) invariant subspaces -/
theorem idempotent_in_vN_iff_ker_and_range_are_centralizer_invariant
  (M : von_neumann_algebra V) (e : V →L[ℂ] V) (h : is_idempotent_elem e) :
  e ∈ M ↔ ∀ y : V →L[ℂ] V, y ∈ set.centralizer M.carrier
                   → submodule.invariant e.ker y ∧ submodule.invariant e.range y :=
begin
  simp only [ submodule.invariant_iff, to_linear_map_eq_coe, set_like.mem_coe,
              set.image_subset_iff, set.subset_def, set.mem_image,
              linear_map.mem_ker, linear_map.mem_range,
              continuous_linear_map.coe_coe, forall_exists_index,
              and_imp, forall_apply_eq_imp_iff₂ ],
  split,
    { intros he y hy,
      have : e.comp y = y.comp e := set.mem_centralizer_iff.mp hy e he,
      simp only [← comp_apply, this],
      simp only [comp_apply],
      exact ⟨ λ x hx, by rw [hx,map_zero],
              λ u v w hu hv, by rw [← hv, ← hu, ← comp_apply, ← this, comp_apply];
                                simp only [exists_apply_eq_apply] ⟩, },
    { intros H,
      rw [← von_neumann_algebra.mem_carrier,
          ← von_neumann_algebra.double_commutant, set.mem_centralizer_iff],
      intros m hm, ext x,
      have h' : is_idempotent_elem (e : V →ₗ[ℂ] V) := by
        { rw is_idempotent_elem at ⊢ h, ext y,
          rw [linear_map.mul_apply, continuous_linear_map.coe_coe,
              ← mul_apply, h] },
      obtain ⟨v, w, hvw, hunique⟩ :=
        submodule.exists_unique_add_of_is_compl
        (linear_map.is_idempotent.is_compl_range_ker ↑e h') x,
      obtain ⟨y, hy⟩ := set_like.coe_mem w,
      have hg := linear_map.mem_ker.mp (set_like.coe_mem v),
      simp only [to_linear_map_eq_coe, continuous_linear_map.coe_coe] at hy hg,
      obtain ⟨p,hp⟩ := (H m hm).2 (m w) w y hy rfl,
      rw [← hvw], simp only [mul_apply, map_add],
      rw [hg, map_zero, zero_add, ← hp, (H m hm).1 v hg, zero_add, ← mul_apply e e,
          is_idempotent_elem.eq h, hp, ← hy, ← mul_apply e e, is_idempotent_elem.eq h], }
end
