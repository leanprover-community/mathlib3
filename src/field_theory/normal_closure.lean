/-
Copyright (c) 2023 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import field_theory.normal

/-!
# Normal closures

In this file we define the normal closure of an `intermediate_field`.

## Main Definitions

- `intermediate_field.normal_closure K` for `K : intermediate_field F L`.
-/

namespace intermediate_field

variables {F L : Type*} [field F] [field L] [algebra F L] (K K' : intermediate_field F L)

/-- The normal closure of an `intermediate_field`. -/
noncomputable def normal_closure : intermediate_field F L :=
(normal_closure F K L).restrict_scalars F

instance [normal F L] : normal F K.normal_closure :=
let h := normal_closure.normal F K L in h

instance [finite_dimensional F K] : finite_dimensional F K.normal_closure :=
let h := normal_closure.is_finite_dimensional F K L in h

lemma normal_closure_def : K.normal_closure = ⨆ f : K →ₐ[F] L, f.field_range :=
rfl

variables {K K'}

lemma normal_closure_le_iff : K.normal_closure ≤ K' ↔ ∀ f : K →ₐ[F] L, f.field_range ≤ K' :=
supr_le_iff

lemma field_range_le_normal_closure (f : K →ₐ[F] L) : f.field_range ≤ K.normal_closure :=
le_supr alg_hom.field_range f

variables (K K')

lemma le_normal_closure : K ≤ K.normal_closure :=
begin
  refine le_of_eq_of_le _ (field_range_le_normal_closure K.val),
  exact set_like.ext' subtype.range_val.symm,
end

lemma normal_closure_of_normal [normal F K] : K.normal_closure = K :=
begin
  haveI : is_scalar_tower F K K := by apply_instance,
  refine le_antisymm (normal_closure_le_iff.mpr (λ f, _)) K.le_normal_closure,
  rintros - ⟨a, rfl⟩,
  exact f.restrict_normal_commutes K a ▸ (f.restrict_normal K a).2,
end

variables [normal F L]

lemma normal_closure_normal_closure : K.normal_closure.normal_closure = K.normal_closure :=
K.normal_closure.normal_closure_of_normal

lemma normal_closure_def' : K.normal_closure = ⨆ f : L →ₐ[F] L, K.map f :=
begin
  refine K.normal_closure_def.trans (le_antisymm (supr_le (λ f, _)) (supr_le (λ f, _))),
  { exact le_supr_of_le (f.lift_normal L) (λ b ⟨a, h⟩, ⟨a, a.2, h ▸ f.lift_normal_commutes L a⟩) },
  { exact le_supr_of_le (f.comp K.val) (λ b ⟨a, h⟩, ⟨⟨a, h.1⟩, h.2⟩) },
end

lemma normal_closure_def'' : K.normal_closure = ⨆ f : L ≃ₐ[F] L, K.map f :=
begin
  refine K.normal_closure_def'.trans (le_antisymm (supr_le (λ f, _)) (supr_le (λ f, _))),
  { exact le_supr_of_le (f.restrict_normal' L)
      (λ b ⟨a, h⟩, ⟨a, h.1, h.2 ▸ f.restrict_normal_commutes L a⟩) },
  { exact le_supr_of_le f le_rfl },
end

variables {K K'}

lemma normal_closure_eq_self_iff_normal : K.normal_closure = K ↔ normal F K :=
⟨λ h, h ▸ normal_closure.normal K, @normal_closure_of_normal F L _ _ _ K⟩

lemma normal_closure_le_self_iff_normal : K.normal_closure ≤ K ↔ normal F K :=
K.le_normal_closure.le_iff_eq.trans normal_closure_eq_self_iff_normal

lemma normal_iff_forall_field_range_le : normal F K ↔ ∀ σ : K →ₐ[F] L, σ.field_range ≤ K :=
by rw [←normal_closure_le_self_iff_normal, normal_closure_def, supr_le_iff]

lemma normal_iff_forall_map_le : normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ ≤ K :=
by rw [←normal_closure_le_self_iff_normal, normal_closure_def', supr_le_iff]

lemma normal_iff_forall_map_le' : normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ ≤ K :=
by rw [←normal_closure_le_self_iff_normal, normal_closure_def'', supr_le_iff]

lemma normal_iff_forall_field_range_eq : normal F K ↔ ∀ σ : K →ₐ[F] L, σ.field_range = K :=
begin
  haveI : is_scalar_tower F K K := by apply_instance,
  refine ⟨_, λ h, normal_iff_forall_field_range_le.mpr (λ σ, (h σ).le)⟩,
  introsI h σ,
  exact le_antisymm (normal_iff_forall_field_range_le.mp h σ)
    (λ x hx, ⟨(σ.restrict_normal' K).symm ⟨x, hx⟩,
    (σ.restrict_normal_commutes K ((σ.restrict_normal' K).symm ⟨x, hx⟩)).symm.trans
    (congr_arg (algebra_map K L) ((σ.restrict_normal' K).apply_symm_apply ⟨x, hx⟩))⟩),
end

lemma normal_iff_forall_map_eq : normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ = K :=
begin
  refine ⟨λ h σ, _, λ h, normal_iff_forall_map_le.mpr (λ σ, (h σ).le)⟩,
  refine eq.trans _ (normal_iff_forall_field_range_eq.mp h (σ.comp K.val)),
  refine eq.trans _ (K.val.map_field_range σ),
  exact congr_arg (map σ) (set_like.ext' subtype.range_val.symm),
end

lemma normal_iff_forall_map_eq' : normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ = K :=
⟨λ h σ, normal_iff_forall_map_eq.mp h σ, λ h, normal_iff_forall_map_le'.mpr (λ σ, (h σ).le)⟩

end intermediate_field
