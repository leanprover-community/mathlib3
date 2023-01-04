/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.inner_product_space.adjoint

/-!
# Finite-dimensional inner product spaces

In this file, we prove some results in finite-dimensional inner product spaces.

## Notation

This file uses the local notation `P _` for `orthogonal_projection _`
and `P _ᗮ` for `orthogonal_projection _ᗮ`.

We let `V` be a finite-dimensional inner product space over `ℂ`.
-/

variables {V : Type*} [inner_product_space ℂ V]
local notation `P`U := (orthogonal_projection U)
local notation `P`U`ᗮ` := (orthogonal_projection Uᗮ)

/-- `U` is `T` invariant: `∀ u : V`, if `u ∈ U` then `T u ∈ U`-/
def invariant_subspace (U : submodule ℂ V) (T : V →L[ℂ] V) : Prop := U ≤ U.comap T
lemma invariant_subspace_def (U : submodule ℂ V) (T : V →L[ℂ] V) :
invariant_subspace U T ↔ T '' U ⊆ U :=
by simp only [set.image_subset_iff]; refl

/-- `U` is `T` invariant if and only if `(P U) * T * (P U) = T * (P U)` -/
lemma subspace_is_invariant_iff_ortho_proj_mul_T_mul_ortho_proj_eq_T_mul_ortho_proj
[finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) :
invariant_subspace U T ↔ ∀ x : V, ↑((P U) (T ↑((P U) x))) = T ↑((P U) x) :=
begin
  split,
  { intros h x,
    obtain ⟨w, hw, v, hv, hvw⟩ := submodule.exists_sum_mem_mem_orthogonal U x,
    rw [hvw, map_add,
      orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv,
      add_zero, orthogonal_projection_eq_self_iff.mpr hw],
    exact orthogonal_projection_eq_self_iff.mpr (h hw) },
  { intros h u h_1,
    rw [submodule.mem_comap,
      ← orthogonal_projection_eq_self_iff, ← orthogonal_projection_eq_self_iff.mpr h_1, h] }
end

/-- `U,Uᗮ` are `T` invariant if and only if `(P U) * T = T * (P U)` -/
lemma U_and_U_ortho_are_T_invariant_iff_ortho_proj_mul_T_eq_T_mul_ortho_proj
[finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) :
(invariant_subspace U T ∧ invariant_subspace Uᗮ T) ↔ ∀ x : V, ↑((P U) (T x)) = T ↑((P U) x) :=
begin
  simp only [subspace_is_invariant_iff_ortho_proj_mul_T_mul_ortho_proj_eq_T_mul_ortho_proj],
  have : ∀ x : V,
        ↑((P Uᗮ) x) = ((continuous_linear_map.id ℂ V) x) - ↑((P U) x) := λ x, by
       rw [ eq_sub_iff_add_eq, add_comm,
            ← eq_sum_orthogonal_projection_self_orthogonal_complement U x,
            continuous_linear_map.id_apply ],
  simp only [this], clear this,
  simp only [continuous_linear_map.id_apply, map_sub, sub_eq_self,
             add_subgroup_class.coe_sub, sub_eq_zero,
             ← subspace_is_invariant_iff_ortho_proj_mul_T_mul_ortho_proj_eq_T_mul_ortho_proj],
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

-- `(P U) * T = T * (P U)` if and only if `T⁻¹ * (P U) * T = P U`
lemma ortho_proj_mul_T_eq_T_mul_ortho_proj_iff_Tinv_mul_ortho_proj_mul_T_eq_ortho_proj
[finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] (x : V) :
↑((P U) (T x)) = T ↑((P U) x) ↔ T.inverse ↑((P U) (T x)) = ↑((P U) x)
:= ⟨ λ h, by rw h; simp only [ ← continuous_linear_map.comp_apply,
                               ← continuous_linear_map.mul_def ];
                   rw continuous_linear_map.inv_mul_self; refl,
     λ h, by rw ← h; simp only [ ← continuous_linear_map.comp_apply,
                                 ← continuous_linear_map.mul_def,
                                 continuous_linear_map.mul_inv_self ]; refl ⟩

/-- `T⁻¹(U) ⊆ U` is equivalent to `U ⊆ T(U)`
in other words, `U` is `T⁻¹` invariant if and only if `U ⊆ T(U)` -/
lemma U_is_Tinv_invariant_iff_U_subseteq_T_image
(U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
invariant_subspace U T.inverse ↔ ↑U ⊆ T '' U
:= ⟨ λ h x hx, by simp only [set.mem_image, set_like.mem_coe];
                  use T.inverse x;
                  rw [ ← continuous_linear_map.comp_apply,
                       ← continuous_linear_map.mul_def,
                       continuous_linear_map.mul_inv_self,
                       continuous_linear_map.one_apply ];
                  simp only [eq_self_iff_true, and_true];
                  apply h; exact hx,
     λ h x hx, by rw submodule.mem_comap;
                  simp only [set.subset_def, set.mem_image] at h;
                  cases h x hx with y hy;
                  rw [ ← hy.2,
                       ← continuous_linear_map.comp_apply,
                       ← continuous_linear_map.mul_def,
                       continuous_linear_map.inv_mul_self ];
                  exact hy.1 ⟩

/-- `T⁻¹ * (P U) * T = P U` if and only if `T(U) = U` and `T(Uᗮ) = Uᗮ` -/
theorem T_inv_P_U_T_eq_P_U_iff_image_T_of_U_eq_U_and_image_T_of_U_ortho_eq_U_ortho
[finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
(∀ x : V, T.inverse ↑((P U) (T x)) = ↑((P U) x)) ↔ T '' U = U ∧ T '' Uᗮ = Uᗮ :=
begin
  simp only [← ortho_proj_mul_T_eq_T_mul_ortho_proj_iff_Tinv_mul_ortho_proj_mul_T_eq_ortho_proj,
             ← U_and_U_ortho_are_T_invariant_iff_ortho_proj_mul_T_eq_T_mul_ortho_proj U T],
  simp only [set.subset.antisymm_iff],
  have Hu : ∀ p q r s, ((p ∧ q) ∧ r ∧ s) = ((p ∧ r) ∧ (q ∧ s)) := λ _ _ _ _, by
    { simp only [ and.assoc, eq_iff_iff, and.congr_right_iff],
      simp only [← and.assoc, and.congr_left_iff],
      simp only [and.comm], simp only [iff_self, implies_true_iff], },
  rw [ Hu, ← invariant_subspace_def U T, ← invariant_subspace_def Uᗮ T, iff_self_and ],
  clear Hu,
  simp only [← U_is_Tinv_invariant_iff_U_subseteq_T_image],
  simp only [U_and_U_ortho_are_T_invariant_iff_ortho_proj_mul_T_eq_T_mul_ortho_proj,
            ortho_proj_mul_T_eq_T_mul_ortho_proj_iff_Tinv_mul_ortho_proj_mul_T_eq_ortho_proj],
  intros h x, rw [← h], simp only [← continuous_linear_map.comp_apply],
  rw [ ← continuous_linear_map.mul_def, continuous_linear_map.mul_inv_self ], refl,
end

/-- `U` is `T` invariant if and only if `Uᗮ` is `T.adjoint` invariant -/
theorem subspace_is_operator_invariant_iff_ortho_subspace_is_adjoint_invariant
[finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) :
invariant_subspace U T ↔ invariant_subspace Uᗮ T.adjoint :=
begin
  suffices : ∀ U : submodule ℂ V, ∀ T : V →L[ℂ] V,
   invariant_subspace U T → invariant_subspace Uᗮ T.adjoint,
     {  split,
        exact this U T,
        intro h,
        rw [← continuous_linear_map.adjoint_adjoint T,
            ← submodule.orthogonal_orthogonal U],
        apply this,
        exact h, },
  clear U T,
  simp only [ invariant_subspace_def, continuous_linear_map.to_linear_map_eq_coe,
              set_like.mem_coe, set.image_subset_iff, set.subset_def, set.mem_image,
              continuous_linear_map.coe_coe, forall_exists_index,
              and_imp, forall_apply_eq_imp_iff₂ ],
  intros U T h x hx y hy,
  rw continuous_linear_map.adjoint_inner_right,
  apply (submodule.mem_orthogonal U x).mp hx,
  apply h y hy,
end

/-- `T` is self adjoint implies
`U` is `T` invariant if and only if `Uᗮ` is `T` invariant -/
lemma operator_is_self_adjoint_implies_subspace_invariant_iff_ortho_subspace_invariant
[finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) (h : is_self_adjoint T) :
invariant_subspace U T ↔ invariant_subspace Uᗮ T
:= by rw [ subspace_is_operator_invariant_iff_ortho_subspace_is_adjoint_invariant,
           continuous_linear_map.is_self_adjoint_iff'.mp h ]

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

-- copied from `analysis/von_neumann_algebra/finite_dimensional (PR #18054)`
-- I think this probably belongs here?
lemma idempotent_operator_exists_ker_add_range
(T : V →ₗ[ℂ] V) (h : T^2 = T) (x : V) :
∃ v : T.ker, ∃ w : T.range, x = v + w
:= by { use x - T x,
        rw [linear_map.mem_ker, linear_map.map_sub,
            ← linear_map.mul_apply, ← pow_two, h, sub_self],
        use T x,
        rw [linear_map.mem_range],
        simp only [exists_apply_eq_apply],
        simp only [submodule.coe_mk, sub_add_cancel], }

/-- idempotent `T` is self-adjoint if and only if `(T.ker)ᗮ = T.range` -/
theorem idempotent_is_self_adjoint_iff_ker_is_ortho_to_range
[finite_dimensional ℂ V] (T : V →ₗ[ℂ] V) (h : T^2 = T) :
is_self_adjoint T ↔ (T.ker)ᗮ = T.range :=
begin
  rw linear_map.is_self_adjoint_iff',
  split,
    { intros l, rw [ker_is_ortho_adjoint_range, submodule.orthogonal_orthogonal],
      revert l, exact congr_arg linear_map.range, },
    { intro h1, apply eq_of_sub_eq_zero,
      simp only [← inner_map_self_eq_zero],
      intro x,
      obtain ⟨v,w,hvw⟩ := idempotent_operator_exists_ker_add_range T h x,
      simp only [linear_map.sub_apply, inner_sub_left, linear_map.adjoint_inner_left],
      cases (set_like.coe_mem w) with y hy,
      rw [hvw, map_add, linear_map.mem_ker.mp (set_like.coe_mem v),
          ← hy, ← linear_map.mul_apply, ← pow_two, h, zero_add, hy, inner_add_left,
          inner_add_right, ← inner_conj_sym ↑w ↑v, (submodule.mem_orthogonal T.ker ↑w).mp
            (by { rw h1, exact set_like.coe_mem w }) v (set_like.coe_mem v),
          map_zero, zero_add, sub_self], },
end
