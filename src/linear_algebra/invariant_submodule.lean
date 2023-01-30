/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.basic
import linear_algebra.projection

/-!
# Invariant submodules

In this file, we define and prove some basic results on invariant submodules.

## Definition

* `U.invariant_under T`: a submodule `U` is invariant under `T` if `U ≤ U.comap T`,
in other words, it is invariant under `T` if for any `u ∈ U` we also have `T u ∈ U`

Equivalently, one can use `submodule.map`, `set.maps_to`, and `set.image` to describe this using:

* `U.invariant_under_iff_map T`: `U.invariant_under T` iff `U.map T ≤ U`

* `U.invariant_under_iff_maps_to T`: `U.invariant_under T` iff `set.maps_to T U U`

* `U.invariant_under_iff T`: `U.invariant_under T` iff `T '' U ⊆ U`

## Notation

This file uses the local notation `pᵤ` for the linear projection to `U` along its complement `V`
and `pᵥ` for the linear projection to `V` along its complement `U`.

## Tags

invariant
-/

namespace submodule

variables {E R : Type*} [ring R] [add_comm_group E] [module R E]

/-- `U` is `T` invariant : `U ≤ U.comap` -/
def invariant_under (U : submodule R E) (T : E →ₗ[R] E) : Prop := U ≤ U.comap T

/-- `U` is `T` invariant if and only if `U.map T ≤ U` -/
lemma invariant_under_iff_map (U : submodule R E) (T : E →ₗ[R] E) :
  U.invariant_under T ↔ U.map T ≤ U := map_le_iff_le_comap.symm

/-- `U` is `T` invariant if and only if `set.maps_to T U U` -/
lemma invariant_under_iff_maps_to (U : submodule R E) (T : E →ₗ[R] E) :
  U.invariant_under T ↔ set.maps_to T U U := iff.rfl

/-- `U` is `T` invariant is equivalent to saying `T(U) ⊆ U` -/
lemma invariant_under_iff (U : submodule R E) (T : E →ₗ[R] E) :
  U.invariant_under T ↔ T '' U ⊆ U := by rw [← set.maps_to', U.invariant_under_iff_maps_to]

variables (U V : submodule R E) (hUV : is_compl U V) (T : E →ₗ[R] E)

local notation `pᵤ` := linear_proj_of_is_compl U V hUV
local notation `pᵥ` := linear_proj_of_is_compl V U hUV.symm

lemma invariant_under.linear_proj_comp_self_comp_linear_proj_eq
  (h : U.invariant_under T) (x : E) : ↑(pᵤ (T (pᵤ x))) = T (pᵤ x) :=
begin
  rw linear_proj_of_is_compl_eq_self_iff,
  exact h (coe_mem _),
end

lemma invariant_under_of_linear_proj_comp_self_comp_linear_proj_eq
  (h : ∀ x : E, ↑(pᵤ (T (pᵤ x))) = T (pᵤ x)) : U.invariant_under T :=
begin
  intros u hu,
  rw [mem_comap, ← linear_proj_of_is_compl_eq_self_iff hUV _,
      ← (linear_proj_of_is_compl_eq_self_iff hUV u).mpr hu, h],
end

/-- `U` is invariant under `T` if and only if `pᵤ.comp (T.comp pᵤ) = T.comp pᵤ`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma invariant_under_iff_linear_proj_comp_self_comp_linear_proj_eq :
  U.invariant_under T ↔ (∀ x : E, (pᵤ (T (pᵤ x)) : E) = T (pᵤ x)) :=
⟨invariant_under.linear_proj_comp_self_comp_linear_proj_eq U V hUV T,
 invariant_under_of_linear_proj_comp_self_comp_linear_proj_eq U V hUV T⟩

/-- `V` is invariant under `T` if and only if `pᵤ.comp (T.comp pᵤ) = pᵤ.comp T`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq :
  V.invariant_under T ↔ (∀ x : E, (pᵤ (T (pᵤ x)) : E) = pᵤ (T x)) :=
by simp_rw [invariant_under_iff_linear_proj_comp_self_comp_linear_proj_eq _ _ hUV.symm,
            linear_proj_of_is_compl_eq_self_sub_linear_proj, map_sub, sub_eq_self,
            submodule.coe_sub, sub_eq_zero, eq_comm]

/-- both `U` and `V` are invariant under `T` if and only if `T` commutes with `pᵤ`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma is_compl_invariant_under_iff_linear_proj_and_self_commute :
  (U.invariant_under T ∧ V.invariant_under T) ↔ commute (U.subtype.comp pᵤ) T :=
begin
  simp_rw [commute, semiconj_by, linear_map.ext_iff, linear_map.mul_apply,
           linear_map.comp_apply, U.subtype_apply],
  split,
  { rintros ⟨h1, h2⟩ x,
    rw [← (U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq V _ _).mp h2 x],
    exact (linear_proj_of_is_compl_eq_self_iff hUV _).mpr
      (h1 (set_like.coe_mem (pᵤ x))) },
  { intros h,
    split,
    { simp_rw [U.invariant_under_iff_linear_proj_comp_self_comp_linear_proj_eq _ hUV, h,
               linear_proj_of_is_compl_idempotent hUV],
      exact λ x, rfl },
    { simp_rw [U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq _ hUV, h,
               linear_proj_of_is_compl_idempotent hUV],
      exact λ x, rfl } }
end

/-- `U` is invariant under `T.symm` if and only if `U ⊆ T(U)` -/
lemma invariant_under_symm_iff_subset_image (T : E ≃ₗ[R] E) :
  U.invariant_under T.symm ↔ ↑U ⊆ T '' U :=
(U.invariant_under_iff T.symm).trans (T.to_equiv.symm.subset_image' _ _).symm

/-- `U` is invariant under `⅟ T` if and only if `U ⊆ T(U)` -/
lemma invariant_under_inv_of_iff_subset_image [invertible T] :
  U.invariant_under (⅟ T) ↔ ↑U ⊆ T '' U :=
begin
  simp_rw [← linear_equiv.coe_linear_map_of_invertible T, ← T.of_invertible_symm_eq_inv_of],
  exact invariant_under_symm_iff_subset_image U _,
end

/-- (⅟ T).comp (pᵤ.comp T) = pᵤ` if and only if `T(U) = U` and `T(V) = V`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
theorem inv_of_comp_linear_proj_comp_self_eq_linear_proj_iff_image_eq [invertible T] :
  (⅟ T).comp ((U.subtype.comp pᵤ).comp T) = U.subtype.comp pᵤ ↔ T '' U = U ∧ T '' V = V :=
begin
  simp_rw [← commute_with_invertible_linear_map_iff_conj_eq_self,
           ← is_compl_invariant_under_iff_linear_proj_and_self_commute,
           set.subset.antisymm_iff, ← invariant_under_iff, and_and_and_comm, iff_self_and,
           ← invariant_under_inv_of_iff_subset_image,
           is_compl_invariant_under_iff_linear_proj_and_self_commute U V hUV],
  rw [commute_with_invertible_linear_map_iff_conj_eq_self, commute, semiconj_by],
  simp_rw [← linear_map.mul_eq_comp],
  intros h,
  rw ← h,
  simp_rw [mul_assoc _ _ (⅟ T), mul_inv_of_self, h],
  refl,
end

end submodule
