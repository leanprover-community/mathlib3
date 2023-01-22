/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.basic
import linear_algebra.projection
import topology.algebra.module.basic

/-!
# Invariant submodules

In this file, we define and prove some basic results on invaraint submodules.
-/

/-- `U` is `T` invariant (ver 1): `U ≤ U.comap` -/
def submodule.invariant_under {V K : Type*} [semiring K] [add_comm_monoid V] [module K V]
   (U : submodule K V) (T : V →ₗ[K] V) : Prop := U ≤ U.comap T

/-- `U` is `T` invariant if and only if `U.map T ≤ U` -/
@[simp] lemma submodule.invariant_under_iff_map {V K : Type*} [semiring K]
  [add_comm_monoid V] [module K V] (U : submodule K V) (T : V →ₗ[K] V) :
  U.invariant_under T ↔ U.map T ≤ U := submodule.map_le_iff_le_comap.symm

/-- `U` is `T` invariant if and only if `set.maps_to T U U` -/
@[simp] lemma submodule.invariant_under_iff_maps_to {V K : Type*} [semiring K]
  [add_comm_monoid V] [module K V] (U : submodule K V) (T : V →ₗ[K] V) :
  U.invariant_under T ↔ set.maps_to T U U := iff.rfl

/-- `U` is `T` invariant is equivalent to saying `T(U) ⊆ U` -/
lemma submodule.invariant_under_iff {V K : Type*} [semiring K] [add_comm_monoid V] [module K V]
  (U : submodule K V) (T : V →ₗ[K] V) : U.invariant_under T ↔ T '' U ⊆ U :=
by rw [← set.maps_to', U.invariant_under_iff_maps_to]

/-- projection to `U` along `V` of `x` equals `x` if and only if `x ∈ U` -/
lemma submodule.linear_proj_of_is_compl_eq_self_iff {R E : Type*}
  [ring R] [add_comm_group E] [module R E]
  (U V : submodule R E) (hUV : is_compl U V) (x : E) :
  (U.linear_proj_of_is_compl V hUV x : E) = x ↔ x ∈ U :=
begin
  split; intro H,
  { rw ← H, exact submodule.coe_mem _ },
  { exact congr_arg _ (submodule.linear_proj_of_is_compl_apply_left hUV ⟨x, H⟩) }
end

lemma submodule.proj_comp_self_comp_proj_eq_of_invariant_under {R E : Type*}
  [ring R] [add_comm_group E] [module R E]
  (U V : submodule R E) (hUV : is_compl U V) (T : E →ₗ[R] E)
  (h : U.invariant_under T) (x : E) :
  ↑((U.linear_proj_of_is_compl V hUV) (T ↑((U.linear_proj_of_is_compl V hUV) x))) =
  T ↑((U.linear_proj_of_is_compl V hUV) x) :=
begin
  rw submodule.linear_proj_of_is_compl_eq_self_iff,
  exact h (submodule.coe_mem _),
end

lemma submodule.invariant_under_of_proj_comp_self_comp_proj_eq {R E : Type*}
  [ring R] [add_comm_group E] [module R E]
  (U V : submodule R E) (hUV : is_compl U V) (T : E →ₗ[R] E)
  (h : ∀ x : E,
  ↑((U.linear_proj_of_is_compl V hUV) (T ↑((U.linear_proj_of_is_compl V hUV) x))) =
  T ↑((U.linear_proj_of_is_compl V hUV) x)) : U.invariant_under T :=
begin
  intros u hu,
  rw [submodule.mem_comap, ← submodule.linear_proj_of_is_compl_eq_self_iff U V hUV,
  ← (submodule.linear_proj_of_is_compl_eq_self_iff U V hUV u).mpr hu, h],
end

lemma submodule.proj_comp_self_comp_proj_eq_iff_invariant_under {R E : Type*}
  [ring R] [add_comm_group E] [module R E]
  (U V : submodule R E) (hUV : is_compl U V) (T : E →ₗ[R] E)
  : U.invariant_under T ↔ (∀ x : E, ↑((U.linear_proj_of_is_compl V hUV)
  (T ↑((U.linear_proj_of_is_compl V hUV) x))) = T ↑((U.linear_proj_of_is_compl V hUV) x)) :=
begin
 split,
 { intros h x,
   exact submodule.proj_comp_self_comp_proj_eq_of_invariant_under U V hUV T h x, },
 { intros h,
   exact submodule.invariant_under_of_proj_comp_self_comp_proj_eq U V hUV T h, }
end

lemma submodule.compl_invariant_under_iff_linear_proj_and_T_commute {R E : Type*}
  [ring R] [add_comm_group E] [module R E]
  (U V : submodule R E) (hUV : is_compl U V) (T : E →ₗ[R] E) :
  (U.invariant_under T ∧ V.invariant_under T)
    ↔ commute (U.subtype.comp (U.linear_proj_of_is_compl V hUV)) T :=
begin
  rw [commute, semiconj_by, linear_map.ext_iff],
  simp only [linear_map.mul_apply],
  simp only [linear_map.coe_comp, submodule.coe_subtype, function.comp_app],
  simp only [submodule.proj_comp_self_comp_proj_eq_iff_invariant_under U V hUV],
  simp only [submodule.proj_comp_self_comp_proj_eq_iff_invariant_under V U (is_compl.symm hUV)],
  have : ∀ x : E, ↑(V.linear_proj_of_is_compl U (is_compl.symm hUV) x) =
    x - ↑(U.linear_proj_of_is_compl V hUV x) := λ x,
  by rw [eq_sub_iff_add_eq, add_comm, submodule.linear_proj_add_linear_proj_of_is_compl_eq_self],
  simp_rw [this], clear this,
  simp_rw [map_sub, sub_eq_self, add_subgroup_class.coe_sub,
    sub_eq_zero,
    ← submodule.proj_comp_self_comp_proj_eq_iff_invariant_under],
  split,
  { rintros ⟨h1, h2⟩ x,
    simp_rw [h2 x],
    exact (U.linear_proj_of_is_compl_eq_self_iff V hUV _).mpr
      (h1 (set_like.coe_mem (U.linear_proj_of_is_compl V hUV x))), },
  { intros h,
    split,
    { intros u h',
      specialize h u,
      simp_rw [(U.linear_proj_of_is_compl_eq_self_iff V hUV _).mpr h'] at h,
      exact (U.linear_proj_of_is_compl_eq_self_iff V hUV _).mp h, },
    { intros x,
      simp_rw [← h, submodule.linear_proj_of_is_compl_apply_left], } },
end

lemma submodule.commutes_with_linear_proj_iff_linear_proj_eq {R E : Type*}
  [ring R] [add_comm_group E] [module R E] [topological_space E] [topological_add_group E]
  (U V : submodule R E) (hUV : is_compl U V) (T : E →L[R] E) [invertible T] :
  commute (U.subtype.comp (U.linear_proj_of_is_compl V hUV)) T ↔
    (T.inverse : E →ₗ[R] E).comp ((U.subtype.comp (U.linear_proj_of_is_compl V hUV)).comp
      (T : E →ₗ[R] E)) = U.subtype.comp (U.linear_proj_of_is_compl V hUV) :=
begin
  rw [commute, semiconj_by],
  simp_rw [linear_map.mul_eq_comp],
  have gs : ∀ S I : E →L[R] E, (S : E →ₗ[R] E) * ↑I = ↑(S*I) := λ S I, rfl,
  split,
  { intro h,
    simp_rw [h, ← linear_map.mul_eq_comp,
             ← mul_assoc, gs, continuous_linear_map.inv_mul_self T],
    refl, },
  { intros h,
    rw ← h, simp_rw [← linear_map.mul_eq_comp, ← mul_assoc,
                     gs, continuous_linear_map.mul_inv_self],
    rw [mul_assoc ↑(T.inverse) _ _],
    simp_rw [linear_map.mul_eq_comp, h], refl, }
end

lemma submodule.invariant_under_inv_iff_U_subset_image {R E : Type*}
  [ring R] [add_comm_group E] [module R E] [topological_space E] [topological_add_group E]
  (U V : submodule R E) (hUV : is_compl U V) (T : E →L[R] E) [invertible T] :
  U.invariant_under T.inverse ↔ ↑U ⊆ T '' U :=
begin
  split,
 { intros h x hx,
   simp only [set.mem_image, set_like.mem_coe],
   use T.inverse x,
   rw [ ← continuous_linear_map.comp_apply, ← continuous_linear_map.mul_def,
        continuous_linear_map.mul_inv_self, continuous_linear_map.one_apply ],
   simp only [eq_self_iff_true, and_true],
   apply h, exact hx, },
 { intros h x hx,
   rw submodule.mem_comap,
   simp only [set.subset_def, set.mem_image] at h,
   cases h x hx with y hy,
   rw [continuous_linear_map.coe_coe, ← hy.2,
       ← continuous_linear_map.comp_apply, ← continuous_linear_map.mul_def,
       continuous_linear_map.inv_mul_self ],
   exact hy.1 }
end

theorem submodule.inv_linear_proj_comp_map_eq_linear_proj_iff_images_eq {R E : Type*}
  [ring R] [add_comm_group E] [module R E] [topological_space E] [topological_add_group E]
  (U V : submodule R E) (hUV : is_compl U V) (T : E →L[R] E) [invertible T] :
  (T.inverse : E →ₗ[R] E).comp
    ((U.subtype.comp (U.linear_proj_of_is_compl V hUV)).comp (T : E →ₗ[R] E)) =
      U.subtype.comp (U.linear_proj_of_is_compl V hUV) ↔ T '' U = U ∧ T '' V = V :=
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
  simp_rw [← continuous_linear_map.coe_coe T, ← submodule.invariant_under_iff _ _,
           iff_self_and, continuous_linear_map.coe_coe],
   simp_rw [← submodule.invariant_under_inv_iff_U_subset_image _ _ hUV,
             ← submodule.invariant_under_inv_iff_U_subset_image _ _ (is_compl.symm hUV),
             submodule.compl_invariant_under_iff_linear_proj_and_T_commute U V hUV,
             submodule.commutes_with_linear_proj_iff_linear_proj_eq],
  rw [commute, semiconj_by],
  intros h,
  rw ← h,
  simp_rw [← linear_map.mul_eq_comp, mul_assoc _ _ ↑(T.inverse)] at *,
  have gs : ∀ S I : E →L[R] E, (S : E →ₗ[R] E) * ↑I = ↑(S*I) := λ S I, rfl,
  rw [gs, continuous_linear_map.mul_inv_self, h],
  refl,
end
