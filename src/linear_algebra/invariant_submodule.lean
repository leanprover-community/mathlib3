/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.basic
import linear_algebra.projection
import linear_algebra.general_linear_group

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

lemma invariant_under.linear_proj_comp_self_eq
  (h : U.invariant_under T) (x : U) : (pᵤ (T x) : E) = T x :=
begin
  rw linear_proj_of_is_compl_eq_self_iff,
  exact h (coe_mem _),
end

lemma invariant_under_of_linear_proj_comp_self_eq
  (h : ∀ x : U, (pᵤ (T x) : E) = T x) : U.invariant_under T :=
begin
  intros u hu,
  rw [mem_comap, ← linear_proj_of_is_compl_eq_self_iff hUV _,
      ← (linear_proj_of_is_compl_eq_self_iff hUV u).mpr hu, h],
end

/-- `U` is invariant under `T` if and only if `pᵤ ∘ₗ T = T`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma invariant_under_iff_linear_proj_comp_self_eq :
  U.invariant_under T ↔ (∀ x : U, (pᵤ (T x) : E) = T x) :=
⟨λ h u, invariant_under.linear_proj_comp_self_eq U V hUV T h u,
 λ h, invariant_under_of_linear_proj_comp_self_eq U V hUV T h⟩

/-- `V` is invariant under `T` if and only if `pᵤ ∘ₗ (T ∘ₗ pᵤ) = pᵤ ∘ₗ T`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq :
  V.invariant_under T ↔ (∀ x : E, (pᵤ (T (pᵤ x)) : E) = pᵤ (T x)) :=
by simp_rw [invariant_under_iff_linear_proj_comp_self_eq _ _ hUV.symm,
            (linear_map.range_eq_top.1 (linear_proj_of_is_compl_range hUV.symm)).forall,
            linear_proj_of_is_compl_eq_self_sub_linear_proj, map_sub,
            sub_eq_self, submodule.coe_sub, sub_eq_zero, eq_comm]

/-- both `U` and `V` are invariant under `T` if and only if `T` commutes with `pᵤ`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma is_compl_invariant_under_iff_linear_proj_and_self_commute :
  (U.invariant_under T ∧ V.invariant_under T) ↔ commute (U.subtype ∘ₗ pᵤ) T :=
begin
  simp_rw [commute, semiconj_by, linear_map.ext_iff, linear_map.mul_apply,
           linear_map.comp_apply, U.subtype_apply],
  split,
  { rintros ⟨h1, h2⟩ x,
    rw [← (U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq V _ _).mp h2 x],
    exact (linear_proj_of_is_compl_eq_self_iff hUV _).mpr
      (h1 (set_like.coe_mem (pᵤ x))) },
  { intros h,
    simp_rw [U.invariant_under_iff_linear_proj_comp_self_eq _ hUV,
             (linear_map.range_eq_top.1 (linear_proj_of_is_compl_range hUV)).forall,
             U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq _ hUV, h,
             linear_proj_of_is_compl_idempotent hUV, ← forall_and_distrib, and_self,
             eq_self_iff_true, forall_const], }
end

/-- `U` is invariant under `T.symm` if and only if `U ⊆ T(U)` -/
lemma invariant_under_symm_iff_le_map (T : E ≃ₗ[R] E) :
  U.invariant_under T.symm ↔ U ≤ U.map T :=
(U.invariant_under_iff T.symm).trans (T.to_equiv.symm.subset_image' _ _).symm

/-- `U` is invariant under `⅟T` if and only if `U ⊆ T(U)` -/
lemma invariant_under_inv_of_iff_le_map [invertible T] :
  U.invariant_under (⅟T) ↔ U ≤ U.map T :=
invariant_under_symm_iff_le_map _ (linear_equiv.of_invertible T)

/-- `⅟T ∘ₗ (pᵤ ∘ₗ T) = pᵤ` if and only if `T(U) = U` and `T(V) = V`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
theorem inv_of_comp_linear_proj_comp_self_eq_linear_proj_iff_map_eq [invertible T] :
  ⅟T ∘ₗ (U.subtype ∘ₗ pᵤ) ∘ₗ T = U.subtype ∘ₗ pᵤ ↔ U.map T = U ∧ V.map T = V :=
begin
  have : ∀ f, commute f T ↔ ⅟T ∘ₗ f ∘ₗ T = f :=
    λ f, commute.symm_iff.trans ((unit_of_invertible T).commute_iff_inv_mul_cancel f),
  simp_rw [←this,
           ← is_compl_invariant_under_iff_linear_proj_and_self_commute, le_antisymm_iff,
           ← invariant_under_iff_map, and_and_and_comm, iff_self_and,
           ← invariant_under_inv_of_iff_le_map,
           is_compl_invariant_under_iff_linear_proj_and_self_commute U V hUV],
  rw [this, commute, semiconj_by],
  simp_rw [← linear_map.mul_eq_comp],
  intros h,
  rw ← h,
  simp_rw [mul_assoc _ _ (⅟T), mul_inv_of_self, h],
  refl,
end

end submodule
