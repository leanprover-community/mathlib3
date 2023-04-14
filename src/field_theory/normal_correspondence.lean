import field_theory.galois

lemma normal_iff_fixing (F L : Type*)
  [field F] [field L] [algebra F L] [is_galois F L]
  (K : intermediate_field F L) :
  K.fixing_subgroup.normal ↔ ∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K :=
begin
  split,
  {
    sorry
  },
  {

  },
end

theorem normal_correspondence (F L : Type*)
  [field F] [field L] [algebra F L] [is_galois F L]
  (K : intermediate_field F L) :
  normal F K ↔ K.fixing_subgroup.normal :=
begin
  split,
  { intro normal_fk,
    -- rw normal_iff at normal_fk,
    refine ⟨λ n hn g x, _⟩,
    have hx_normal := normal.splits normal_fk x,
    have hx : g⁻¹ • (x : L) ∈ K := sorry,
    specialize hn ⟨g⁻¹ • x, hx⟩,
    rw subtype.coe_mk at hn,
    rw [mul_smul, mul_smul, hn],
    rw smul_inv_smul, },
  { intro hk_normal,
    have hk_conj := hk_normal.conj_mem,
    rw normal_iff,
    intro x,
    rw intermediate_field.is_integral_iff,
    refine ⟨is_galois.integral F (x : L), _⟩,

  },
end
