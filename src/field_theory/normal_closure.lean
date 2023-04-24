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
  haveI : is_scalar_tower F K K := ⟨smul_mul_assoc⟩,
  refine le_antisymm (normal_closure_le_iff.mpr (λ f, _)) K.le_normal_closure,
  rintros - ⟨a, rfl⟩,
  exact f.restrict_normal_commutes K a ▸ (f.restrict_normal K a).2,
end

lemma normal_closure_normal_closure [normal F L] :
  K.normal_closure.normal_closure = K.normal_closure :=
K.normal_closure.normal_closure_of_normal

end intermediate_field
