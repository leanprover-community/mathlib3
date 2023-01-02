/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Monica Omar
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

variables {V : Type*} [inner_product_space ℂ V] [finite_dimensional ℂ V]
local notation `P`U := (orthogonal_projection U)
local notation `P`U`ᗮ` := (orthogonal_projection Uᗮ)

/-- `U` is `T` invariant is equivalent to `T(U) ⊆ U` -/
lemma U_is_T_invariant_def (U : submodule ℂ V) (T : V →L[ℂ] V) :
 (∀ u : V, u ∈ U → T u ∈ U) ↔ (T '' U ⊆ U)
  := by { simp only [set.image_subset_iff],
          exact ⟨ λ ᾰ, λ x hx, by simp only [set.mem_preimage]; exact ᾰ x hx,
                  λ ᾰ u ᾰ_1, by apply ᾰ ᾰ_1 ⟩, }

/-- `U` is `T` invariant if and only if `(P U) * T * (P U) = T * (P U)` -/
lemma U_is_T_invariant_iff_P_U_T_P_U_eq_T_P_U (U : submodule ℂ V) (T : V →L[ℂ] V) :
 (T '' U ⊆ U) ↔ ∀ x : V, ↑((P U) (T ↑((P U) x))) = (T ↑((P U) x))
  := by rw ← U_is_T_invariant_def U T;
        exact ⟨ λ ᾰ x, by obtain ⟨w,hw,v,hv,hvw⟩ := submodule.exists_sum_mem_mem_orthogonal U x;
                          rw [ hvw,
                               map_add,
                               orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv,
                               add_zero,
                               orthogonal_projection_eq_self_iff.mpr hw,
                               orthogonal_projection_eq_self_iff.mpr (ᾰ w hw) ],
                λ ᾰ u ᾰ_1, by rw [ ← orthogonal_projection_eq_self_iff,
                                   ← orthogonal_projection_eq_self_iff.mpr ᾰ_1,
                                   ᾰ] ⟩

/-- `U,Uᗮ` are `T` invariant if and only if `(P U) * T = T * (P U)` -/
lemma U_and_U_bot_are_T_invariant_iff_P_U_T_eq_T_P_U (U : submodule ℂ V) (T : V →L[ℂ] V) :
 (T '' U ⊆ U ∧ T '' Uᗮ ⊆ Uᗮ) ↔ ∀ x : V, ↑((P U) (T x)) = (T ↑((P U) x)) :=
   begin
     simp only [U_is_T_invariant_iff_P_U_T_P_U_eq_T_P_U],
     have : ∀ x : V, ↑((P Uᗮ) x) = ((continuous_linear_map.id ℂ V) x) - ↑((P U) x) := λ x, by rw [ eq_sub_iff_add_eq,
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
                 ← U_is_T_invariant_iff_P_U_T_P_U_eq_T_P_U],
     simp only [← U_is_T_invariant_def],
     exact ⟨λ ⟨h1,h2⟩ x, by simp only [h2 x, orthogonal_projection_eq_self_iff.mpr (h1 ((P U) x) (orthogonal_projection_fn_mem x))],
            λ h, ⟨λ u ᾰ, by specialize h u;
                            simp only [orthogonal_projection_eq_self_iff.mpr ᾰ] at h;
                            exact orthogonal_projection_eq_self_iff.mp h,
                  λ x, by simp only [← h, orthogonal_projection_mem_subspace_eq_self]⟩⟩,
   end

-- Given an invertible operator, multiplying it by its inverse gives the identity.
lemma Tinv_mul_T_eq_1 (T : V →L[ℂ] V) [invertible T] : T.inverse * T = 1 :=
   by simp only [ ← continuous_linear_map.ring_inverse_eq_map_inverse,
                  ring.inverse_mul_cancel,
                  is_unit_of_invertible T ]
lemma T_mul_Tinv_eq_1 (T : V →L[ℂ] V) [invertible T] : T * T.inverse = 1 :=
   by simp only [ ← continuous_linear_map.ring_inverse_eq_map_inverse,
                  ring.mul_inverse_cancel,
                  is_unit_of_invertible ]

-- `(P U) * T = T * (P U)` if and only if `T⁻¹ * (P U) * T = P U`
lemma P_U_T_eq_T_P_U_iff_Tinv_P_U_T_eq_P_U (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
 ∀ x : V, ↑((P U) (T x)) = T ↑((P U) x) ↔ T.inverse ↑((P U) (T x)) = ↑((P U) x)
  := λ x, ⟨ λ h, by rw h;
                    simp only [ ← continuous_linear_map.comp_apply,
                                ← continuous_linear_map.mul_def ];
                    rw Tinv_mul_T_eq_1;
                    refl,
            λ h, by rw ← h;
                    simp only [ ← continuous_linear_map.comp_apply,
                                ← continuous_linear_map.mul_def,
                                T_mul_Tinv_eq_1 ];
                    refl ⟩

/-- `T⁻¹(U) ⊆ U` is equivalent to `U ⊆ T(U)` -/
lemma Tinv_image_subseteq_iff_subseteq_T_image (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
 ((T.inverse) '' U ⊆ U) ↔ (↑U ⊆ T '' U)
  := ⟨ λ h x hx, by simp only [set.mem_image, set_like.mem_coe];
                    use T.inverse x;
                    rw [ ← continuous_linear_map.comp_apply,
                         ← continuous_linear_map.mul_def,
                         T_mul_Tinv_eq_1 T,
                         continuous_linear_map.one_apply ];
                    simp only [eq_self_iff_true, and_true];
                    apply h;
                    rw set.mem_image;
                    use x;
                    simp only [eq_self_iff_true, and_true];
                    exact hx,
       λ h x hx, by simp only [set.mem_image, set_like.mem_coe] at hx;
                    cases hx with y hy;
                    rw ← hy.2;
                    cases set.mem_of_subset_of_mem h hy.1 with z hz;
                    rw [ ← hz.2,
                         ← continuous_linear_map.comp_apply,
                         ← continuous_linear_map.mul_def,
                         Tinv_mul_T_eq_1 ];
                    exact hz.1 ⟩

/-- `T⁻¹ * (P U) * T = P U` if and only if `T(U) = U` and `T(Uᗮ) = Uᗮ` -/
lemma T_inv_P_U_T_eq_P_U_iff_image_T_U_eq_U_and_image_T_U_bot_eq_U_bot (U : submodule ℂ V) (T : V →L[ℂ] V) [invertible T] :
 (∀ x : V, T.inverse ↑((P U) (T x)) = ↑((P U) x)) ↔ T '' U = U ∧ T '' Uᗮ = Uᗮ :=
  begin
    simp only [ ← P_U_T_eq_T_P_U_iff_Tinv_P_U_T_eq_P_U,
                ← U_and_U_bot_are_T_invariant_iff_P_U_T_eq_T_P_U U T ],
    simp only [set.subset.antisymm_iff],
    have Hu : ∀ p q r s, ((p ∧ q) ∧ r ∧ s) = ((p ∧ r) ∧ (q ∧ s)) := λ _ _ _ _, by  { simp only [ and.assoc,
                      eq_iff_iff,
                      and.congr_right_iff],
          simp only [← and.assoc, and.congr_left_iff],
          simp only [and.comm],
          simp only [iff_self, implies_true_iff], },
    rw [ Hu,
         ← U_is_T_invariant_def U T,
         ← U_is_T_invariant_def Uᗮ T,
         iff_self_and ],
    clear Hu,
    simp only [← Tinv_image_subseteq_iff_subseteq_T_image],
    simp only [U_is_T_invariant_def],
    simp only [ U_and_U_bot_are_T_invariant_iff_P_U_T_eq_T_P_U,
                P_U_T_eq_T_P_U_iff_Tinv_P_U_T_eq_P_U ],
    intros,
    rw [← ᾰ],
    simp only [← continuous_linear_map.comp_apply],
    rw [ ← continuous_linear_map.mul_def,
         T_mul_Tinv_eq_1 ],
    refl,
  end
