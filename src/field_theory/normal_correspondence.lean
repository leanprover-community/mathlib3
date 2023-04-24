import field_theory.galois

lemma normal_iff_stabilizing {F L : Type*}
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  K.fixing_subgroup.normal ↔ ∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K :=
begin
  split,
  {
    intros hk_normal g x hxk,
    have hk_fixing := is_galois.fixed_field_fixing_subgroup K,
    rw ← hk_fixing,
    rw intermediate_field.fixed_field,
    rw fixed_points.intermediate_field,
    dsimp,
    rintro ⟨ϕ, hϕ⟩,
    change ϕ (g x) = g x,
    suffices: g⁻¹ (ϕ (g x)) = x,
    {
      apply_fun g at this,
      rw ←alg_equiv.mul_apply at this,
      simpa,
    },
    have := hk_normal.conj_mem ϕ hϕ g⁻¹ ⟨x, hxk⟩,
    simpa,
  },
  {
    intro hgfix,
    refine ⟨λ n hn g x, _⟩,
    rw [mul_smul, mul_smul],
    have hx := hgfix g⁻¹ x x.mem,
    specialize hn ⟨g⁻¹ • x, hx⟩,
    rw subtype.coe_mk at hn,
    rw [hn, smul_inv_smul],
  },
end

lemma stabilizing_iff_res_stabilizing {F L : Type*}
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  (∀ (g : L →ₐ[F] L) (x : L), x ∈ K → g x ∈ K) ↔ (∀ (g : K →ₐ[F] L) (x : K), g x ∈ K) :=
begin
  split,
  {
    intros hL g x,
    have hgliftcomm := alg_hom.lift_normal_commutes g L x,
    change g.lift_normal L x = g x at hgliftcomm,
    rw ← hgliftcomm,
    apply hL,
    exact x.mem,
  },
  {
    intros hK g x hxk,
    have gres := g ∘ K.val,
  },
end

lemma stabilizing_iff_normal_ext {F L : Type*}
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  (∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K) ↔ normal F K :=
begin
  split,
  {
    sorry,
  },
  {
    -- intros hsplit g,
    sorry,
  },
end

theorem normal_correspondence (F L : Type*)
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  normal F K ↔ K.fixing_subgroup.normal :=
begin
  rw [normal_iff_stabilizing, stabilizing_iff_normal_ext],
end
