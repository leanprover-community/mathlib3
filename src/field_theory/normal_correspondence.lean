import field_theory.galois
import field_theory.normal_closure

lemma normal_sbgp_iff_stabilizing {F L : Type*}
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
    let gres := g.comp K.val,
    exact hK gres ⟨x, hxk⟩,
  },
end

lemma res_stabilizing_iff_normal_closure_contained {F L : Type*}
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  (∀ (g : K →ₐ[F] L) (x : K), g x ∈ K) ↔ K.normal_closure ≤ K :=
begin
  rw intermediate_field.normal_closure_le_iff,
  apply forall_congr,
  intro a,
  have := @set.range_subset_iff L K a K,
  exact this.symm,
end

lemma normal_closure_contained_iff_normal {F L : Type*}
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  K.normal_closure ≤ K ↔ normal F K :=
begin
  split,
  {
    intro hncont,
    rw ← le_antisymm hncont (intermediate_field.le_normal_closure K),
    apply_instance,
  },
  {
    introI hknormal,
    rw intermediate_field.normal_closure_of_normal K,
    exact le_rfl,
  },
end

lemma stabilizing_iff_normal_ext {F L : Type*}
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  (∀ (g : L ≃ₐ[F] L) (x : L), x ∈ K → g • x ∈ K) ↔ normal F K :=
begin
  rw equiv.forall_congr_left' (alg_equiv_equiv_alg_hom F L).to_equiv,
  change (∀ (g : L →ₐ[F] L) x, x ∈ K → g x ∈ K) ↔ _,
  rw [stabilizing_iff_res_stabilizing, res_stabilizing_iff_normal_closure_contained,
    normal_closure_contained_iff_normal],
end

theorem normal_correspondence (F L : Type*)
  [field F] [field L] [algebra F L] [is_galois F L]
  [finite_dimensional F L] (K : intermediate_field F L) :
  normal F K ↔ K.fixing_subgroup.normal :=
begin
  rw [normal_sbgp_iff_stabilizing, stabilizing_iff_normal_ext],
end
