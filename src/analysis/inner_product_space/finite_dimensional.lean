/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.inner_product_space.adjoint
import analysis.inner_product_space.spectrum

/-!
# Finite-dimensional inner product spaces

In this file, we prove some results in finite-dimensional inner product spaces.

## Notation

This file uses the local notation `P _` for `orthogonal_projection _`
and `↥P _` for the extended orthogonal projection `V →L[ℂ] V`.

We let `V` be an inner product space over `ℂ`.
-/

variables {V : Type*} [inner_product_space ℂ V]
local notation `P` := orthogonal_projection

/-- `U` is `T` invariant: `∀ u : V`, if `u ∈ U` then `T u ∈ U`-/
def submodule.invariant (U : submodule ℂ V) (T : V →ₗ[ℂ] V) : Prop := U ≤ U.comap T
lemma submodule.invariant_iff (U : submodule ℂ V) (T : V →ₗ[ℂ] V) :
  submodule.invariant U T ↔ T '' U ⊆ U :=
by simp only [set.image_subset_iff]; refl

/-- `↥P _` is the extended version of `P _` -/
noncomputable def orthogonal_projection.extend [finite_dimensional ℂ V]
  (U : submodule ℂ V) : V →L[ℂ] V := U.subtypeL.comp (P U)
local notation `↥P` := orthogonal_projection.extend

lemma orthogonal_projection.extend_iff [finite_dimensional ℂ V] (U : submodule ℂ V) (x : V) :
  ↥P U x = ↑(P U x) := rfl

-- the extended orthogonal projection is an invariant subspace
lemma submodule.invariant_of_ortho_proj (U : submodule ℂ V) [finite_dimensional ℂ V] :
  submodule.invariant U (↥P U) :=
begin
  intros x hx,
  rw [submodule.mem_comap, continuous_linear_map.coe_coe,
      orthogonal_projection.extend_iff U, orthogonal_projection_eq_self_iff.mpr hx],
  exact hx,
end

/-- if `U` is `T` invariant, then `(P U).comp T.comp (P U) = T.comp (P U)` -/
lemma submodule.invariant_imp_ortho_proj_comp_T_comp_ortho_proj_eq_T_comp_ortho_proj
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →ₗ[ℂ] V)
  (h : submodule.invariant U T) (x : V) : ↑(P U (T ↑(P U x))) = T ↑(P U x) :=
begin
  obtain ⟨w, hw, v, hv, hvw⟩ := submodule.exists_sum_mem_mem_orthogonal U x,
  rw [hvw, map_add,
      orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv,
      add_zero, orthogonal_projection_eq_self_iff.mpr hw],
  exact orthogonal_projection_eq_self_iff.mpr (h hw),
end

/-- if `(P U).comp T.comp (P U) = T.comp (P U)`, then `U` is `T` invariant  -/
lemma submodule.ortho_proj_comp_T_comp_ortho_proj_eq_T_comp_ortho_proj_imp_invariant
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →ₗ[ℂ] V)
  (h : ∀ x : V, ↑(P U (T ↑(P U x))) = T ↑(P U x)) : submodule.invariant U T :=
begin
  intros u h_1,
  rw [submodule.mem_comap,
      ← orthogonal_projection_eq_self_iff, ← orthogonal_projection_eq_self_iff.mpr h_1, h],
end

lemma submodule.invariant_iff_ortho_proj_comp_T_comp_ortho_proj_eq_T_comp_ortho_proj
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →ₗ[ℂ] V) :
  submodule.invariant U T ↔ ∀ x : V, ↑(P U (T ↑(P U x))) = T ↑(P U x) :=
⟨λ h, submodule.invariant_imp_ortho_proj_comp_T_comp_ortho_proj_eq_T_comp_ortho_proj _ _ h,
 λ h, submodule.ortho_proj_comp_T_comp_ortho_proj_eq_T_comp_ortho_proj_imp_invariant _ _ h⟩

/-- `U,Uᗮ` are `T` invariant if and only if `commute (P U) T` -/
lemma submodule.invariant_and_ortho_invariant_iff_ortho_proj_and_T_commute
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →ₗ[ℂ] V) :
  (submodule.invariant U T ∧ submodule.invariant Uᗮ T) ↔ commute ↑(↥P U) T :=
begin
  rw [commute, semiconj_by, linear_map.ext_iff],
   simp only [linear_map.mul_apply, continuous_linear_map.coe_coe,
              orthogonal_projection.extend_iff],
  simp only [submodule.invariant_iff_ortho_proj_comp_T_comp_ortho_proj_eq_T_comp_ortho_proj],
  have : ∀ x : V,
        ↑(P Uᗮ x) = (continuous_linear_map.id ℂ V) x - ↑(P U x) := λ x, by
       rw [ eq_sub_iff_add_eq, add_comm,
            ← eq_sum_orthogonal_projection_self_orthogonal_complement U x,
            continuous_linear_map.id_apply ],
  simp only [this], clear this,
  simp only [continuous_linear_map.id_apply, map_sub, sub_eq_self,
             add_subgroup_class.coe_sub, sub_eq_zero,
             ← submodule.invariant_iff_ortho_proj_comp_T_comp_ortho_proj_eq_T_comp_ortho_proj],
  exact ⟨λ ⟨h1,h2⟩ x, by simp only [h2 x];
                         exact orthogonal_projection_eq_self_iff.mpr
                               (h1 (orthogonal_projection_fn_mem x)),
         λ h, ⟨λ u h', by specialize h u;
                          simp only [orthogonal_projection_eq_self_iff.mpr h'] at h;
                          rw submodule.mem_comap;
                          exact orthogonal_projection_eq_self_iff.mp h,
               λ x, by simp only [← h, orthogonal_projection_mem_subspace_eq_self]⟩⟩,
end

/-- Given an invertible operator, multiplying it by its inverse gives the identity. -/
lemma continuous_linear_map.inv_mul_self (T : V →L[ℂ] V) [invertible T] : T.inverse * T = 1 :=
by simp only [ ← continuous_linear_map.ring_inverse_eq_map_inverse,
               ring.inverse_mul_cancel, ring.mul_inverse_cancel,
               is_unit_of_invertible T, and_self ]
lemma continuous_linear_map.mul_inv_self (T : V →L[ℂ] V) [invertible T] : T * T.inverse = 1 :=
by simp only [ ← continuous_linear_map.ring_inverse_eq_map_inverse,
               ring.inverse_mul_cancel, ring.mul_inverse_cancel,
               is_unit_of_invertible T, and_self ]

/-- `commute (P U) T` if and only if `T⁻¹.comp (P U).comp T = P U` -/
lemma ortho_proj_and_T_commute_iff_Tinv_comp_ortho_proj_comp_T_eq_ortho_proj
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
  commute (↥P U) T ↔ T.inverse.comp ((↥P U).comp T) = ↥P U :=
begin
  rw [commute, semiconj_by],
  simp only [continuous_linear_map.mul_def],
  split,
  { intro h, rw h, simp only [← continuous_linear_map.mul_def],
   rw [← mul_assoc, continuous_linear_map.inv_mul_self], refl },
  { intro h, rw ← h, simp only [← continuous_linear_map.mul_def],
   rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
       continuous_linear_map.mul_inv_self, one_mul, mul_assoc T.inverse _ _ ],
   simp only [continuous_linear_map.mul_def, h] }
end

/-- `T⁻¹(U) ⊆ U` is equivalent to `U ⊆ T(U)`
in other words, `U` is `T⁻¹` invariant if and only if `U ⊆ T(U)` -/
lemma submodule.invariant_inverse_iff_U_subseteq_T_image
(U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
  submodule.invariant U T.inverse ↔ ↑U ⊆ T '' U :=
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

/-- `T⁻¹ * (P U) * T = P U` if and only if `T(U) = U` and `T(Uᗮ) = Uᗮ` -/
theorem T_inv_P_U_T_eq_P_U_iff_image_T_of_U_eq_U_and_image_T_of_U_ortho_eq_U_ortho
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
  T.inverse.comp ((↥P U).comp T) = ↥P U ↔ T '' U = U ∧ T '' Uᗮ = Uᗮ :=
begin
  rw [← ortho_proj_and_T_commute_iff_Tinv_comp_ortho_proj_comp_T_eq_ortho_proj],
  have : ∀ U : submodule ℂ V, ∀ T : V →L[ℂ] V,
    commute (↥P U) T ↔ commute ↑(↥P U) (T : V →ₗ[ℂ] V) := λ W S,
  by simp only [commute, semiconj_by, continuous_linear_map.ext_iff,
                linear_map.ext_iff, continuous_linear_map.mul_apply,
                linear_map.mul_apply, continuous_linear_map.coe_coe],
  rw [this, ← submodule.invariant_and_ortho_invariant_iff_ortho_proj_and_T_commute U T],
  simp only [set.subset.antisymm_iff],
  have Hu : ∀ p q r s, ((p ∧ q) ∧ r ∧ s) = ((p ∧ r) ∧ (q ∧ s)) := λ _ _ _ _, by
    { simp only [ and.assoc, eq_iff_iff, and.congr_right_iff],
      simp only [← and.assoc, and.congr_left_iff],
      simp only [and.comm], simp only [iff_self, implies_true_iff], },
  rw [← continuous_linear_map.coe_coe T, Hu, ← submodule.invariant_iff U T,
      ← submodule.invariant_iff Uᗮ T, continuous_linear_map.coe_coe T, iff_self_and ],
  clear Hu,
  simp only [← submodule.invariant_inverse_iff_U_subseteq_T_image,
             submodule.invariant_and_ortho_invariant_iff_ortho_proj_and_T_commute,
             ← this,
             ortho_proj_and_T_commute_iff_Tinv_comp_ortho_proj_comp_T_eq_ortho_proj],
  rw [commute, semiconj_by], simp only [← continuous_linear_map.mul_def],
  intros h, rw [← h, mul_assoc _ _ T.inverse, mul_assoc _ _ T.inverse,
                continuous_linear_map.mul_inv_self, mul_one, h],
end

/-- `U` is `T` invariant if and only if `Uᗮ` is `T.adjoint` invariant -/
theorem submodule.invariant_iff_ortho_adjoint_invariant
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →ₗ[ℂ] V) :
  submodule.invariant U T ↔ submodule.invariant Uᗮ T.adjoint :=
begin
  suffices : ∀ U : submodule ℂ V, ∀ T : V →ₗ[ℂ] V,
   submodule.invariant U T → submodule.invariant Uᗮ T.adjoint,
     {  split,
        exact this U T,
        intro h,
        rw [← linear_map.adjoint_adjoint T,
            ← submodule.orthogonal_orthogonal U],
        apply this,
        exact h, },
  clear U T,
  simp only [ submodule.invariant_iff, set_like.mem_coe,
              set.image_subset_iff, set.subset_def, set.mem_image,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂ ],
  intros U T h x hx y hy,
  rw linear_map.adjoint_inner_right,
  apply (submodule.mem_orthogonal U x).mp hx,
  apply h y hy,
end

/-- `T` is self adjoint implies
`U` is `T` invariant if and only if `Uᗮ` is `T` invariant -/
lemma is_self_adjoint.submodule_invariant_iff_ortho_submodule_invariant
  [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →ₗ[ℂ] V) (h : is_self_adjoint T) :
  submodule.invariant U T ↔ submodule.invariant Uᗮ T :=
by rw [ submodule.invariant_iff_ortho_adjoint_invariant,
        linear_map.is_self_adjoint_iff'.mp h ]

/-- `T.ker = (T.adjoint.range)ᗮ` -/
lemma ker_is_ortho_adjoint_range [finite_dimensional ℂ V] (T : V →ₗ[ℂ] V) :
  T.ker = (T.adjoint.range)ᗮ :=
begin
  ext,
  simp only [linear_map.mem_ker, submodule.mem_orthogonal,
             linear_map.mem_range, forall_exists_index,
             forall_apply_eq_imp_iff', linear_map.adjoint_inner_left],
  exact ⟨ λ h, by simp only [h, inner_zero_right, forall_const],
          λ h, inner_self_eq_zero.mp (h (T x))⟩,
end

/-- given any idempotent operator `T ∈ L(V)`, then `is_compl T.ker T.range`,
in other words, there exists unique `v ∈ T.ker` and `w ∈ T.range` such that `x = v + w` -/
lemma linear_map.is_idempotent.is_compl_range_ker (T : V →ₗ[ℂ] V) (h : is_idempotent_elem T) :
  is_compl T.ker T.range :=
begin
 split,
   { rw disjoint_iff,
     ext,
     simp only [submodule.mem_bot, submodule.mem_inf, linear_map.mem_ker,
                linear_map.mem_range, continuous_linear_map.to_linear_map_eq_coe,
                continuous_linear_map.coe_coe],
     split,
       { intro h',
         cases h'.2 with y hy,
         rw [← hy, ← is_idempotent_elem.eq h, linear_map.mul_apply, hy],
         exact h'.1, },
       { intro h',
         rw [h', map_zero],
         simp only [eq_self_iff_true, true_and],
         use x,
         simp only [h', map_zero, eq_self_iff_true], }, },
    { suffices : ∀ x : V, ∃ v : T.ker, ∃ w : T.range, x = v + w,
        { rw [codisjoint_iff, ← submodule.add_eq_sup],
          ext,
          rcases this x with ⟨v,w,hvw⟩,
          simp only [submodule.mem_top, iff_true, hvw],
          apply submodule.add_mem_sup (set_like.coe_mem v) (set_like.coe_mem w), },
      intro x,
      use (x-(T x)), rw [linear_map.mem_ker, map_sub,
                         ← linear_map.mul_apply, is_idempotent_elem.eq h, sub_self],
      use (T x), rw [linear_map.mem_range]; simp only [exists_apply_eq_apply],
      simp only [submodule.coe_mk, sub_add_cancel], }
end

/-- idempotent `T` is self-adjoint if and only if `(T.ker)ᗮ = T.range` -/
theorem linear_map.is_idempotent_is_self_adjoint_iff_ker_is_ortho_to_range
  [finite_dimensional ℂ V] (T : V →ₗ[ℂ] V) (h : is_idempotent_elem T) :
  is_self_adjoint T ↔ (T.ker)ᗮ = T.range :=
begin
  rw linear_map.is_self_adjoint_iff',
  split,
    { intros l, rw [ker_is_ortho_adjoint_range, submodule.orthogonal_orthogonal],
      revert l, exact congr_arg linear_map.range, },
    { intro h1, apply eq_of_sub_eq_zero,
      simp only [← inner_map_self_eq_zero],
      intro x,
      obtain ⟨v, w, hvw, hunique⟩ :=
        submodule.exists_unique_add_of_is_compl
        (linear_map.is_idempotent.is_compl_range_ker T h) x,
      simp only [linear_map.sub_apply, inner_sub_left, linear_map.adjoint_inner_left],
      cases (set_like.coe_mem w) with y hy,
      rw [← hvw, map_add, linear_map.mem_ker.mp (set_like.coe_mem v),
          ← hy, ← linear_map.mul_apply, is_idempotent_elem.eq h, zero_add, hy, inner_add_left,
          inner_add_right, ← inner_conj_sym ↑w ↑v, (submodule.mem_orthogonal T.ker ↑w).mp
            (by { rw h1, exact set_like.coe_mem w }) v (set_like.coe_mem v),
          map_zero, zero_add, sub_self], },
end

/-- `U` and `W` are mutually orthogonal if and only if `(P U).comp (P W) = 0` -/
lemma ortho_spaces_iff_ortho_proj_comp_ortho_proj_eq_0 [finite_dimensional ℂ V]
  (U W : submodule ℂ V) : (∀ x y, x ∈ U ∧ y ∈ W → ⟪x,y⟫_ℂ = 0) ↔ (↥P U).comp (↥P W) = 0 :=
begin
  split,
  { intros h,
    ext v,
    rw [continuous_linear_map.comp_apply, continuous_linear_map.zero_apply,
        ← inner_self_eq_zero, orthogonal_projection.extend_iff, orthogonal_projection.extend_iff,
        ← inner_orthogonal_projection_left_eq_right,
        orthogonal_projection_mem_subspace_eq_self],
    apply h, simp only [submodule.coe_mem, and_self], },
  { intros h x y hxy,
    rw [← orthogonal_projection_eq_self_iff.mpr hxy.1,
        ← orthogonal_projection_eq_self_iff.mpr hxy.2,
        inner_orthogonal_projection_left_eq_right,
        ← orthogonal_projection.extend_iff, ← orthogonal_projection.extend_iff,
        ← continuous_linear_map.comp_apply, h,
        continuous_linear_map.zero_apply, inner_zero_right], }
end

section is_star_normal
open linear_map

/-- linear map `is_star_normal` if and only if it commutes with its adjoint -/
lemma linear_map.is_star_normal_iff_adjoint [finite_dimensional ℂ V] (T : V →ₗ[ℂ] V) :
  is_star_normal T ↔ commute T T.adjoint :=
by rw commute.symm_iff; exact ⟨λ hT, hT.star_comm_self, is_star_normal.mk⟩

/-- `T` is normal if and only if `∀ v, ‖T v‖ = ‖T.adjoint v‖` -/
lemma linear_map.is_star_normal.norm_eq_adjoint [finite_dimensional ℂ V] (T : V →ₗ[ℂ] V) :
  is_star_normal T ↔ ∀ v : V, (norm (T v)) = (norm (T.adjoint v)) :=
begin
  rw [T.is_star_normal_iff_adjoint, commute, semiconj_by, ← sub_eq_zero],
  simp only [← inner_map_self_eq_zero, sub_apply, inner_sub_left, mul_apply,
             adjoint_inner_left, inner_self_eq_norm_sq_to_K],
  simp only [← adjoint_inner_right T, inner_self_eq_norm_sq_to_K, sub_eq_zero,
             ← sq_eq_sq (norm_nonneg _) (norm_nonneg _)],
  norm_cast,
  exact ⟨λ h x, (h x).symm, λ h x, (h x).symm⟩,
end

/-- if `T` is normal, then `T.ker = T.adjoint.ker` -/
lemma linear_map.is_star_normal.ker_eq_ker_adjoint [finite_dimensional ℂ V]
  (T : V →ₗ[ℂ] V) (h : is_star_normal T) : T.ker = T.adjoint.ker :=
by ext; rw [mem_ker, mem_ker, ← norm_eq_zero, iff.comm,
            ← norm_eq_zero, ← (linear_map.is_star_normal.norm_eq_adjoint T).mp h]
/-- if `T` is normal, then `T.range = T.adjoint.range` -/
lemma linear_map.is_star_normal.range_eq_range_adjoint [finite_dimensional ℂ V]
  (T : V →ₗ[ℂ] V) (h : is_star_normal T) : T.range = T.adjoint.range :=
by rw [← submodule.orthogonal_orthogonal T.adjoint.range, ← ker_is_ortho_adjoint_range,
       linear_map.is_star_normal.ker_eq_ker_adjoint T h,
       ker_is_ortho_adjoint_range, adjoint_adjoint,
       submodule.orthogonal_orthogonal]

open_locale complex_conjugate
/-- if `T` is normal, then `∀ x : V, x ∈ eigenspace T μ ↔ x ∈ eigenspace T.adjoint (conj μ)` -/
lemma linear_map.is_star_normal.eigenve_in_eigenspace_iff_eigenvec_in_adjoint_conj_eigenspace
  [finite_dimensional ℂ V] (T : V →ₗ[ℂ] V) (h : is_star_normal T) (μ : ℂ) :
  ∀ x : V, x ∈ module.End.eigenspace T μ ↔ x ∈ module.End.eigenspace T.adjoint (conj μ) :=
begin
  suffices : ∀ T : V →ₗ[ℂ] V, is_star_normal T →
    ∀ μ : ℂ, ∀ v : V, v ∈ module.End.eigenspace T μ → v ∈ module.End.eigenspace T.adjoint (conj μ),
  { intro v, refine ⟨this T h μ v,_⟩,
    intro hv, rw [← adjoint_adjoint T, ← is_R_or_C.conj_conj μ],
    apply this _ _ _ _ hv, exact is_star_normal_star_self, },
  clear h μ T,
  intros T h μ v hv,
  have t1 : (T - μ•1) v = 0,
  { rw [sub_apply, smul_apply, one_apply, sub_eq_zero],
    exact module.End.mem_eigenspace_iff.mp hv, },
  suffices : (T.adjoint - (conj μ)•1) v = 0,
  { rw [module.End.mem_eigenspace_iff, ← sub_eq_zero],
    rw [sub_apply, smul_apply, one_apply] at this, exact this, },
  rw ← norm_eq_zero,
  have nh : is_star_normal (T-μ•1),
  { apply is_star_normal.mk,
    rw [star_sub, star_smul, is_R_or_C.star_def, star_one, commute, semiconj_by],
    simp only [sub_mul, mul_sub, commute.eq h.star_comm_self],
    simp only [smul_one_mul, smul_smul, mul_smul_comm, mul_one],
    rw [mul_comm, sub_sub_sub_comm], },
  have : (T-μ•1).adjoint = T.adjoint - (conj μ)•1 :=
  by simp only [← star_eq_adjoint, star_sub, star_smul, is_R_or_C.star_def, star_one],
  rw [← this, ← (linear_map.is_star_normal.norm_eq_adjoint (T-μ•1)).mp nh, t1, norm_zero],
end
end is_star_normal
