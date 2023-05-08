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

instance {F L : Type*} [field F] [field L] [algebra F L] (K : intermediate_field F L) :
  nonempty (K →ₐ[F] L) := ⟨K.val⟩

namespace intermediate_field

variables {F L : Type*} [field F] [field L] [algebra F L] (K : intermediate_field F L)

/-- The normal closure of an `intermediate_field`. -/
noncomputable def normal_closure : intermediate_field F L :=
(normal_closure F K L).restrict_scalars F

instance [normal F L] : normal F K.normal_closure :=
let h := normal_closure.normal F K L in h

instance [finite_dimensional F K] : finite_dimensional F K.normal_closure :=
let h := normal_closure.is_finite_dimensional F K L in h

lemma normal_closure_def : K.normal_closure = ⨆ f : K →ₐ[F] L, f.field_range :=
rfl

variables {K}

lemma normal_closure_le_iff {K' : intermediate_field F L} :
  K.normal_closure ≤ K' ↔ ∀ f : K →ₐ[F] L, f.field_range ≤ K' :=
supr_le_iff

lemma field_range_le_normal_closure (f : K →ₐ[F] L) : f.field_range ≤ K.normal_closure :=
le_supr alg_hom.field_range f

variables (K)

lemma le_normal_closure : K ≤ K.normal_closure :=
K.field_range_val.symm.trans_le (field_range_le_normal_closure K.val)

lemma normal_closure_of_normal [normal F K] : K.normal_closure = K :=
by simp only [normal_closure_def, alg_hom.field_range_of_normal, supr_const]

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

variables {K}

lemma normal_iff_normal_closure_eq : normal F K ↔ K.normal_closure = K :=
⟨@normal_closure_of_normal F L _ _ _ K, λ h, h ▸ normal_closure.normal K⟩

lemma normal_iff_normal_closure_le : normal F K ↔ K.normal_closure ≤ K :=
normal_iff_normal_closure_eq.trans K.le_normal_closure.le_iff_eq.symm

lemma normal_iff_forall_field_range_le : normal F K ↔ ∀ σ : K →ₐ[F] L, σ.field_range ≤ K :=
by rw [normal_iff_normal_closure_le, normal_closure_def, supr_le_iff]

lemma normal_iff_forall_map_le : normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ ≤ K :=
by rw [normal_iff_normal_closure_le, normal_closure_def', supr_le_iff]

lemma normal_iff_forall_map_le' : normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ ≤ K :=
by rw [normal_iff_normal_closure_le, normal_closure_def'', supr_le_iff]

lemma normal_iff_forall_field_range_eq : normal F K ↔ ∀ σ : K →ₐ[F] L, σ.field_range = K :=
⟨@alg_hom.field_range_of_normal F L _ _ _ K, normal_iff_forall_field_range_le.2 ∘ λ h σ, (h σ).le⟩

lemma normal_iff_forall_map_eq : normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ = K :=
begin
  refine ⟨λ h σ, K.field_range_val ▸ _, λ h, normal_iff_forall_map_le.2 (λ σ, (h σ).le)⟩,
  rw [K.val.map_field_range, normal_iff_forall_field_range_eq.1 h, field_range_val],
end

lemma normal_iff_forall_map_eq' : normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ = K :=
⟨λ h σ, normal_iff_forall_map_eq.1 h σ, λ h, normal_iff_forall_map_le'.2 (λ σ, (h σ).le)⟩

end intermediate_field
