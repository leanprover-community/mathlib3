import field_theory.normal

namespace intermediate_field

variables {F L : Type*} [field F] [field L] [algebra F L] (K K' : intermediate_field F L)

noncomputable def normal_closure : intermediate_field F L :=
(normal_closure F K L).restrict_scalars F

instance [normal F L] : normal F K.normal_closure :=
begin
  have := normal_closure.normal F K L,
  exact this,
end

instance [finite_dimensional F K] : finite_dimensional F K.normal_closure :=
begin
  have := normal_closure.is_finite_dimensional F K L,
  exact this,
end

lemma normal_closure_def : K.normal_closure = ⨆ f : K →ₐ[F] L, f.field_range :=
rfl

variables {K K'}

lemma field_range_le_normal_closure (f : K →ₐ[F] L) : f.field_range ≤ K.normal_closure :=
le_supr alg_hom.field_range f

lemma le_normal_closure : K ≤ K.normal_closure :=
begin
  refine le_trans _ (field_range_le_normal_closure K.val),
  change (K : set L) ≤ set.range K.val,
  exact subtype.range_val.ge,
end

variables {K K'}

lemma normal_closure_le_iff : K.normal_closure ≤ K' ↔ ∀ f : K →ₐ[F] L, f.field_range ≤ K' :=
supr_le_iff

lemma normal_closure_of_normal [h : normal F K] : K.normal_closure = K :=
begin
  haveI : is_scalar_tower F K K := ⟨λ a b c, begin
    rw [smul_eq_mul, smul_eq_mul, algebra.smul_def, algebra.smul_def, mul_assoc],
  end⟩,
  refine le_antisymm (normal_closure_le_iff.mpr _) K.le_normal_closure,
  rintros f - ⟨a, rfl⟩,
  exact (congr_arg (∈ K) (f.restrict_normal_commutes K a)).mp (f.restrict_normal K a).2,
end

end intermediate_field
