/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.von_neumann_algebra.basic

/-!

# Finite-dimensional von Neumann algebras

In this file, we prove some results in finite-dimensional von Neumann algebras.

## Notation

We let `V` be an inner product space over `ℂ`.

## Main results

* `idempotent_operator_in_vN_iff_ker_and_range_are_commutant_invariant`:
idempotent `e ∈ L(V)` is in von Neumann algebra `M` if and only if
`e.range,e.ker` are `M'` (i.e., commutant of `M` or `M.centralizer`)
invariant subspaces
-/

variables {V : Type*} [inner_product_space ℂ V]

-- this definition and lemma are copied from
-- `analysis/inner_product_space/finite_dimensional (PR #18041)`
/-- `U` is `T` invariant: `∀ u : V`, if `u ∈ U` then `T u ∈ U`-/
def invariant_subspace (U : submodule ℂ V) (T : V →L[ℂ] V) :
 Prop := U ≤ U.comap T
lemma invariant_subspace_def (U : submodule ℂ V) (T : V →L[ℂ] V) :
 (invariant_subspace U T) ↔ (T '' U ⊆ U)
  := by simp [set.image_subset_iff]; refl

open continuous_linear_map

-- Not sure if there already exists a version of this lemma in Mathlib.
/-- given any idempotent operator `T ∈ L(V)` and element `x ∈ V`,
there exists `v ∈ T.ker` and `w ∈ T.range` such that `x = v + w` -/
lemma idempotent_operator_exists_ker_add_range
 (T : V →L[ℂ] V) (h : T^2 = T) :
  (∀ x : V, ∃ v : T.ker, ∃ w : T.range, x = v + w)
   := λ x, by { use (x-(T x)),
                rw [to_linear_map_eq_coe, linear_map.mem_ker,
                    continuous_linear_map.coe_coe, map_sub,
                    ← mul_apply, ← pow_two, h, sub_self],
                use (T x),
                rw [to_linear_map_eq_coe, linear_map.mem_range,
                    continuous_linear_map.coe_coe];
                simp only [exists_apply_eq_apply],
                simp only [submodule.coe_mk, sub_add_cancel], }

/-- Let `e ∈ L(V)` be an idempotent operator (i.e., `e^2 = e`).
Then `e ∈ M` if and only if `e.ker` and `e.range` are `M'`
(i.e., the commutant of `M` or `M.centralizer`) invariant subspaces -/
theorem idempotent_operator_in_vN_iff_ker_and_range_are_commutant_invariant
 [finite_dimensional ℂ V] (M : von_neumann_algebra V)
 (e : V →L[ℂ] V) (h : e^2 = e) :
  (e ∈ M.carrier)
     ↔ ∀ (y : V →L[ℂ] V), y ∈ set.centralizer M.carrier
          → invariant_subspace e.ker y ∧ invariant_subspace e.range y :=
  begin
   simp only [ invariant_subspace_def, to_linear_map_eq_coe,
               set_like.mem_coe, set.image_subset_iff,
               set.subset_def, set.mem_image,
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
      rw [← von_neumann_algebra.double_commutant, set.mem_centralizer_iff],
      intros m hm,
      ext x,
      obtain ⟨v,w,hvw⟩ := idempotent_operator_exists_ker_add_range e h x,
      obtain ⟨y,hy⟩ := (set_like.coe_mem w),
      have hg := linear_map.mem_ker.mp (set_like.coe_mem v),
      simp only [to_linear_map_eq_coe,
                 continuous_linear_map.coe_coe] at hy hg,
      obtain ⟨p,hp⟩ := ((H m hm).2) (m w) w y hy rfl,
      rw [hvw],
      simp only [mul_apply, map_add],
      rw [hg, map_zero, zero_add, ← hp, (H m hm).1 v hg, zero_add, ← mul_apply e e,
          ← pow_two, h, hp, ← hy, ← mul_apply e e, ← pow_two, h], }
  end
