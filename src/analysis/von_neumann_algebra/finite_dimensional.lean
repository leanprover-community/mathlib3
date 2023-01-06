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

* `idempotent_in_vN_iff_ker_and_range_are_centralizer_invariant`:
idempotent `e ∈ L(V)` is in von Neumann algebra `M` if and only if
`e.range,e.ker` are `M'` (i.e., commutant of `M` or `M.centralizer`)
invariant subspaces

-/

variables {V : Type*} [inner_product_space ℂ V]

-- this definition and lemma are copied from
-- `analysis/inner_product_space/finite_dimensional (PR #18041)`
/-- `U` is `T` invariant: `∀ u : V`, if `u ∈ U` then `T u ∈ U`-/
def invariant_subspace (U : submodule ℂ V) (T : V →L[ℂ] V) : Prop := U ≤ U.comap T
lemma invariant_subspace_def (U : submodule ℂ V) (T : V →L[ℂ] V) :
  invariant_subspace U T ↔ T '' U ⊆ U := by simp [set.image_subset_iff]; refl

open continuous_linear_map

-- Not sure if there already exists a version of this lemma in Mathlib.
-- There's a copy of this in `analysis/inner_product_space/finite_dimensional (PR #18041)`
-- it probably belongs there more
/-- given any idempotent operator `T ∈ L(V)`, then `is_compl T.ker T.range`,
in other words, there exists unique `v ∈ T.ker` and `w ∈ T.range` such that `x = v + w` -/
lemma idempotent_is_compl_range_ker (T : V →L[ℂ] V) (h : is_idempotent_elem T) :
  is_compl T.ker T.range :=
begin
 split,
   { rw disjoint_iff,
     ext,
     simp only [submodule.mem_bot, submodule.mem_inf, linear_map.mem_ker,
                linear_map.mem_range, continuous_linear_map.to_linear_map_eq_coe,
                continuous_linear_map.coe_coe],
     split,
       { intro h', cases h'.2 with y hy,
         rw [← hy, ← is_idempotent_elem.eq h, mul_apply, hy],
         exact h'.1, },
       { intro h', rw [h', map_zero],
         simp only [eq_self_iff_true, true_and],
         use x, simp only [h', map_zero, eq_self_iff_true], }, },
    { suffices : ∀ x : V, ∃ v : T.ker, ∃ w : T.range, x = v + w,
        { rw [codisjoint_iff, ← submodule.add_eq_sup],
          ext, rcases this x with ⟨v,w,hvw⟩,
          simp only [submodule.mem_top, iff_true, hvw],
          apply submodule.add_mem_sup (set_like.coe_mem v) (set_like.coe_mem w), },
      intro x,
      use (x-(T x)), rw [to_linear_map_eq_coe, linear_map.mem_ker,
                         continuous_linear_map.coe_coe, map_sub,
                         ← mul_apply, is_idempotent_elem.eq h, sub_self],
      use (T x), rw [to_linear_map_eq_coe, linear_map.mem_range,
                     continuous_linear_map.coe_coe]; simp only [exists_apply_eq_apply],
      simp only [submodule.coe_mk, sub_add_cancel], }
end

/-- Let `e ∈ L(V)` be an idempotent operator.
Then `e ∈ M` if and only if `e.ker` and `e.range` are `M'`
(i.e., the commutant of `M` or `M.centralizer`) invariant subspaces -/
theorem idempotent_in_vN_iff_ker_and_range_are_centralizer_invariant
[finite_dimensional ℂ V] (M : von_neumann_algebra V) (e : V →L[ℂ] V) (h : is_idempotent_elem e) :
  e ∈ M.carrier ↔ ∀ y : V →L[ℂ] V, y ∈ set.centralizer M.carrier
                   → invariant_subspace e.ker y ∧ invariant_subspace e.range y :=
begin
  simp only [ invariant_subspace_def, to_linear_map_eq_coe, set_like.mem_coe,
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
      rw [← von_neumann_algebra.double_commutant, set.mem_centralizer_iff],
      intros m hm, ext x,
      obtain ⟨v, w, hvw, hunique⟩ :=
        submodule.exists_unique_add_of_is_compl (idempotent_is_compl_range_ker e h) x,
      obtain ⟨y, hy⟩ := set_like.coe_mem w,
      have hg := linear_map.mem_ker.mp (set_like.coe_mem v),
      simp only [to_linear_map_eq_coe, continuous_linear_map.coe_coe] at hy hg,
      obtain ⟨p,hp⟩ := (H m hm).2 (m w) w y hy rfl,
      rw [← hvw], simp only [mul_apply, map_add],
      rw [hg, map_zero, zero_add, ← hp, (H m hm).1 v hg, zero_add, ← mul_apply e e,
          is_idempotent_elem.eq h, hp, ← hy, ← mul_apply e e, is_idempotent_elem.eq h], }
end
