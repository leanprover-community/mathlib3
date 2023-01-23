/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.basic
import linear_algebra.projection

/-!
# Invariant submodules

In this file, we define and prove some basic results on invaraint submodules.
-/

variables {E R : Type*} [ring R] [add_comm_group E] [module R E]

/-- `U` is `T` invariant (ver 1): `U ≤ U.comap` -/
def submodule.invariant_under (U : submodule R E) (T : E →ₗ[R] E) : Prop := U ≤ U.comap T

/-- `U` is `T` invariant if and only if `U.map T ≤ U` -/
@[simp] lemma submodule.invariant_under_iff_map (U : submodule R E) (T : E →ₗ[R] E) :
  U.invariant_under T ↔ U.map T ≤ U := submodule.map_le_iff_le_comap.symm

/-- `U` is `T` invariant if and only if `set.maps_to T U U` -/
lemma submodule.invariant_under_iff_maps_to (U : submodule R E) (T : E →ₗ[R] E) :
  set.maps_to T U U ↔ U.invariant_under T := iff.rfl

/-- `U` is `T` invariant is equivalent to saying `T(U) ⊆ U` -/
lemma submodule.invariant_under_iff (U : submodule R E) (T : E →ₗ[R] E) :
  U.invariant_under T ↔ T '' U ⊆ U := by rw [← set.maps_to', U.invariant_under_iff_maps_to]

variables (U V : submodule R E) (hUV : is_compl U V) (T : E →ₗ[R] E)

local notation `eᵤ` := submodule.linear_proj_of_is_compl U V hUV
local notation `eᵥ` := submodule.linear_proj_of_is_compl V U (is_compl.symm hUV)

lemma submodule.proj_comp_self_comp_proj_eq_of_invariant_under
  (h : U.invariant_under T) (x : E) : ↑(eᵤ (T ↑(eᵤ x))) = T ↑(eᵤ x) :=
begin
  rw submodule.linear_proj_of_is_compl_eq_self_iff,
  exact h (submodule.coe_mem _),
end

lemma submodule.invariant_under_of_proj_comp_self_comp_proj_eq
  (h : ∀ x : E, ↑(eᵤ (T ↑(eᵤ x))) = T ↑(eᵤ x)) : U.invariant_under T :=
begin
  intros u hu,
  rw [submodule.mem_comap, ← submodule.linear_proj_of_is_compl_eq_self_iff hUV _,
      ← (submodule.linear_proj_of_is_compl_eq_self_iff hUV u).mpr hu, h],
end

lemma submodule.proj_comp_self_comp_proj_eq_iff_invariant_under :
  U.invariant_under T ↔ (∀ x : E, ↑(eᵤ (T ↑(eᵤ x))) = T ↑(eᵤ x)) :=
begin
 split,
 { intros h x,
   exact submodule.proj_comp_self_comp_proj_eq_of_invariant_under U V hUV T h x, },
 { intros h,
   exact submodule.invariant_under_of_proj_comp_self_comp_proj_eq U V hUV T h, }
end

lemma submodule.compl_invariant_under_iff_linear_proj_and_T_commute :
  (U.invariant_under T ∧ V.invariant_under T) ↔ commute (U.subtype.comp (eᵤ)) T :=
begin
  rw [commute, semiconj_by, linear_map.ext_iff],
  simp only [linear_map.mul_apply, linear_map.coe_comp, submodule.coe_subtype,
             function.comp_app, submodule.proj_comp_self_comp_proj_eq_iff_invariant_under U V hUV,
             submodule.proj_comp_self_comp_proj_eq_iff_invariant_under V U (is_compl.symm hUV)],
  have : ∀ x : E, ↑(eᵥ x) = x - ↑(eᵤ x) := λ x,
  by rw [eq_sub_iff_add_eq, add_comm, submodule.linear_proj_add_linear_proj_of_is_compl_eq_self],
  simp_rw [this], clear this,
  simp_rw [map_sub, sub_eq_self, add_subgroup_class.coe_sub,
           sub_eq_zero, ← submodule.proj_comp_self_comp_proj_eq_iff_invariant_under],
  split,
  { rintros ⟨h1, h2⟩ x,
    simp_rw [h2 x],
    exact (submodule.linear_proj_of_is_compl_eq_self_iff hUV _).mpr
      (h1 (set_like.coe_mem (eᵤ x))), },
  { intros h,
    split,
    { intros u h',
      specialize h u,
      simp_rw [(submodule.linear_proj_of_is_compl_eq_self_iff hUV _).mpr h'] at h,
      exact (submodule.linear_proj_of_is_compl_eq_self_iff hUV _).mp h, },
    { intros x,
      simp_rw [← h, submodule.linear_proj_of_is_compl_apply_left], } },
end

lemma submodule.commutes_with_linear_proj_iff_linear_proj_eq [invertible T] :
  commute (U.subtype.comp eᵤ) T ↔
    (⅟ T).comp ((U.subtype.comp eᵤ).comp T) = U.subtype.comp eᵤ :=
begin
  rw [commute, semiconj_by],
  simp_rw [linear_map.mul_eq_comp],
  split,
  { intro h,
    simp_rw [h, ← linear_map.mul_eq_comp, ← mul_assoc, inv_of_mul_self, one_mul], },
  { intros h,
    rw ← h, simp_rw [← linear_map.mul_eq_comp, ← mul_assoc, mul_inv_of_self],
    rw [mul_assoc (⅟ T) _ _],
    simp_rw [linear_map.mul_eq_comp, h], refl, }
end

lemma submodule.invariant_under_inv_iff_U_subset_image [invertible T] :
  U.invariant_under (⅟ T) ↔ ↑U ⊆ T '' U :=
begin
  split,
 { intros h x hx,
   simp only [set.mem_image, set_like.mem_coe],
   use (⅟ T) x,
   rw [← linear_map.comp_apply, ← linear_map.mul_eq_comp,
       mul_inv_of_self, linear_map.one_apply, eq_self_iff_true, and_true],
   exact h hx, },
 { intros h x hx,
   rw submodule.mem_comap,
   simp only [set.subset_def, set.mem_image] at h,
   cases h x hx with y hy,
   rw [← hy.2, ← linear_map.comp_apply, ← linear_map.mul_eq_comp,
       inv_of_mul_self],
   exact hy.1 }
end

theorem submodule.inv_linear_proj_comp_map_eq_linear_proj_iff_images_eq [invertible T] :
  (⅟ T).comp ((U.subtype.comp eᵤ).comp T) = U.subtype.comp eᵤ ↔ T '' U = U ∧ T '' V = V :=
begin
  simp_rw [← submodule.commutes_with_linear_proj_iff_linear_proj_eq,
           ← submodule.compl_invariant_under_iff_linear_proj_and_T_commute,
           set.subset.antisymm_iff],
  have Hu : ∀ p q r s, ((p ∧ q) ∧ r ∧ s) = ((p ∧ r) ∧ (q ∧ s)) := λ _ _ _ _, by
    { simp only [ and.assoc, eq_iff_iff, and.congr_right_iff],
      simp only [← and.assoc, and.congr_left_iff],
      simp only [and.comm], simp only [iff_self, implies_true_iff], },
  rw Hu,
  clear Hu,
  simp_rw [← submodule.invariant_under_iff _ _, iff_self_and,
           ← submodule.invariant_under_inv_iff_U_subset_image,
           submodule.compl_invariant_under_iff_linear_proj_and_T_commute U V hUV],
  rw [submodule.commutes_with_linear_proj_iff_linear_proj_eq, commute, semiconj_by],
  simp_rw [← linear_map.mul_eq_comp],
  intros h,
  rw ← h,
  simp_rw [mul_assoc _ _ (⅟ T), mul_inv_of_self, h],
  refl,
end
