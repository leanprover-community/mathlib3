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
def invariant_subspace (U : submodule ℂ V) (T : V →L[ℂ] V) :
 Prop := (∀ u : V, u ∈ U → T u ∈ U)
lemma invariant_subspace_def (U : submodule ℂ V) (T : V →L[ℂ] V) :
 invariant_subspace U T ↔ (T '' U ⊆ U)
  := by simp only [set.image_subset_iff]; refl

/-- `U` is `T` invariant if and only if `(P U) * T * (P U) = T * (P U)` -/
lemma subspace_is_invariant_iff_ortho_proj_mul_T_mul_ortho_proj_eq_T_mul_ortho_proj
 [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) :
 (invariant_subspace U T) ↔ ∀ x : V, ↑((P U) (T ↑((P U) x))) = (T ↑((P U) x))
  := by exact ⟨ λ h x, by
	                     obtain ⟨w,hw,v,hv,hvw⟩ := submodule.exists_sum_mem_mem_orthogonal U x;
                       rw [ hvw,
                            map_add,
                            orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv,
                            add_zero,
                            orthogonal_projection_eq_self_iff.mpr hw,
                            orthogonal_projection_eq_self_iff.mpr (h w hw) ],
                λ h u h_1, by rw [ ← orthogonal_projection_eq_self_iff,
                                   ← orthogonal_projection_eq_self_iff.mpr h_1,
                                   h] ⟩

/-- `U,Uᗮ` are `T` invariant if and only if `(P U) * T = T * (P U)` -/
lemma U_and_U_bot_are_T_invariant_iff_ortho_proj_mul_T_eq_T_mul_ortho_proj
 [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) :
 (invariant_subspace U T ∧ invariant_subspace Uᗮ T) ↔ ∀ x : V, ↑((P U) (T x)) = (T ↑((P U) x)) :=
   begin
     simp only [subspace_is_invariant_iff_ortho_proj_mul_T_mul_ortho_proj_eq_T_mul_ortho_proj],
     have : ∀ x : V,
      ↑((P Uᗮ) x) = ((continuous_linear_map.id ℂ V) x) - ↑((P U) x)
        := λ x, by rw [ eq_sub_iff_add_eq,
                        add_comm,
                        ← eq_sum_orthogonal_projection_self_orthogonal_complement U x,
                        continuous_linear_map.id_apply ],
     simp only [this],
     clear this,
     simp only [ continuous_linear_map.id_apply,
                 map_sub,
                 sub_eq_self,
                 add_subgroup_class.coe_sub,
                 sub_eq_zero,
                 ← subspace_is_invariant_iff_ortho_proj_mul_T_mul_ortho_proj_eq_T_mul_ortho_proj],
     exact ⟨λ ⟨h1,h2⟩ x, by
            simp only [h2 x,
             orthogonal_projection_eq_self_iff.mpr
              (h1 ((P U) x) (orthogonal_projection_fn_mem x))],
            λ h, ⟨λ u h', by specialize h u;
                            simp only [orthogonal_projection_eq_self_iff.mpr h'] at h;
                            exact orthogonal_projection_eq_self_iff.mp h,
                  λ x, by simp only [← h, orthogonal_projection_mem_subspace_eq_self]⟩⟩,
   end

-- Given an invertible operator, multiplying it by its inverse gives the identity.
lemma mul_inv_operator (T : V →L[ℂ] V) [invertible T] :
 T.inverse * T = 1 ∧ T * T.inverse = 1 :=
   by simp only [ ← continuous_linear_map.ring_inverse_eq_map_inverse,
                  ring.inverse_mul_cancel,
									ring.mul_inverse_cancel,
                  is_unit_of_invertible T,
									and_self ]

-- `(P U) * T = T * (P U)` if and only if `T⁻¹ * (P U) * T = P U`
lemma ortho_proj_mul_T_eq_T_mul_ortho_proj_iff_Tinv_mul_ortho_proj_mul_T_eq_ortho_proj
 [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
 ∀ x : V, ↑((P U) (T x)) = T ↑((P U) x) ↔ T.inverse ↑((P U) (T x)) = ↑((P U) x)
  := λ x, ⟨ λ h, by rw h;
                    simp only [ ← continuous_linear_map.comp_apply,
                                ← continuous_linear_map.mul_def ];
                    rw (mul_inv_operator T).1;
                    refl,
            λ h, by rw ← h;
                    simp only [ ← continuous_linear_map.comp_apply,
                                ← continuous_linear_map.mul_def,
                                (mul_inv_operator T).2 ];
                    refl ⟩

-- `T⁻¹(U) ⊆ U` is equivalent to `U ⊆ T(U)`
-- or `U` is `T⁻¹` invariant if and only if `U ⊆ T(U)`
lemma U_is_Tinv_invariant_iff_U_subseteq_T_image
 (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
  (invariant_subspace U (T.inverse)) ↔ (↑U ⊆ T '' U)
  := ⟨ λ h x hx, by simp only [set.mem_image, set_like.mem_coe];
                    use T.inverse x;
                    rw [ ← continuous_linear_map.comp_apply,
                         ← continuous_linear_map.mul_def,
                         (mul_inv_operator T).2,
                         continuous_linear_map.one_apply ];
                    simp only [eq_self_iff_true, and_true];
                    apply h;
										exact hx,
       λ h x hx, by simp only [set.subset_def, set.mem_image] at h;
                    cases h x hx with y hy;
                    rw ← hy.2;
                    rw [ ← continuous_linear_map.comp_apply,
                         ← continuous_linear_map.mul_def,
                         (mul_inv_operator T).1 ];
                    exact hy.1 ⟩

/-- `T⁻¹ * (P U) * T = P U` if and only if `T(U) = U` and `T(Uᗮ) = Uᗮ` -/
theorem T_inv_P_U_T_eq_P_U_iff_T''U_eq_U_and_T''U_bot_eq_U_bot
 [finite_dimensional ℂ V] (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
 (∀ x : V, T.inverse ↑((P U) (T x)) = ↑((P U) x)) ↔ T '' U = U ∧ T '' Uᗮ = Uᗮ :=
  begin
    simp only [ ← ortho_proj_mul_T_eq_T_mul_ortho_proj_iff_Tinv_mul_ortho_proj_mul_T_eq_ortho_proj,
                ← U_and_U_bot_are_T_invariant_iff_ortho_proj_mul_T_eq_T_mul_ortho_proj U T ],
    simp only [set.subset.antisymm_iff],
    have Hu : ∀ p q r s, ((p ∧ q) ∧ r ∧ s) = ((p ∧ r) ∧ (q ∧ s)) := λ _ _ _ _, by
        { simp only [ and.assoc,
                      eq_iff_iff,
                      and.congr_right_iff],
          simp only [← and.assoc, and.congr_left_iff],
          simp only [and.comm],
          simp only [iff_self, implies_true_iff], },
    rw [ Hu,
         ← invariant_subspace_def U T,
         ← invariant_subspace_def Uᗮ T,
         iff_self_and ],
    clear Hu,
    simp only [← U_is_Tinv_invariant_iff_U_subseteq_T_image],
    simp only [ U_and_U_bot_are_T_invariant_iff_ortho_proj_mul_T_eq_T_mul_ortho_proj,
                ortho_proj_mul_T_eq_T_mul_ortho_proj_iff_Tinv_mul_ortho_proj_mul_T_eq_ortho_proj ],
    intros h x,
    rw [← h],
    simp only [← continuous_linear_map.comp_apply],
    rw [ ← continuous_linear_map.mul_def,
         (mul_inv_operator T).2 ],
    refl,
  end
