import topology.algebra.valued_field
import topology.algebra.localization
import ring_theory.localization.at_prime

open_locale topological_space

class v_topologyy (R : Type*) [field R] [topological_space R] [topological_division_ring R] :=
(cond₁ [] : ∀ W ∈ 𝓝 (0 : R), ∃ U ∈ 𝓝 (0 : R), ∀ x y, x * y ∈ U → x ∈ W ∨ y ∈ W )
(cond₂ [] : ∃ (U : set R) (hU : U ∈ 𝓝 (0 : R)), (1 : R) ∉ U)

class v_topological_ring (R : Type*) [ring R] [topological_space R] [topological_ring R] :=
(cond₁ [] : ∀ W ∈ 𝓝 (0 : R), ∃ U ∈ 𝓝 (0 : R), ∀ x y, x * y ∈ U → x ∈ W ∨ y ∈ W )
(cond₂ [] : ∃ (U : set R) (hU : U ∈ 𝓝 (0 : R)), (1 : R) ∉ U)

variables (K : Type*) [comm_ring K] [topological_space K] [topological_ring K]
  [v_topological_ring K]

@[simp]
def infinitesimal_ideal : ideal K :=
{ carrier := ⋂ (U : set K) (hU : U ∈ 𝓝 (0 : K)), U,
  add_mem' := begin
    intros a b ha hb,
    simp_rw set.mem_Inter at *,
    let M : K × K → K := λ x, x.1 + x.2,
    have hM : continuous M := continuous_add,
    have : continuous_at M (a,b) := hM.continuous_at,
    intros U hU,
    rw mem_nhds_iff at hU,
    obtain ⟨T,h1,h2,h3⟩ := hU,
    have hMT : is_open (M ⁻¹' T) := is_open.preimage hM h2,
    have hh : ((0 : K),(0 : K)) ∈ M ⁻¹' T,
    { change (0 : K) + 0 ∈ T, simpa },
    have : M ⁻¹' T ∈ 𝓝 ((0 : K),(0 : K)), sorry,
    rw nhds_prod_eq at this,
    obtain ⟨P1,h1,P2,h2,h⟩ := this,
    dsimp [filter.comap] at h1 h2,
    obtain ⟨U1,hU1,hU1'⟩ := h1_1,
    obtain ⟨U2,hU2,hU2'⟩ := h2_1,
    specialize ha _ hU1,
    specialize hb _ hU2,
    apply h1,
    change (a,b) ∈ M ⁻¹' T, rw h,
    split,
    apply hU1', exact ha,
    apply hU2', exact hb,
  end,
  zero_mem' := begin
    simp only [set.mem_Inter], intros U hU, refine mem_of_mem_nhds hU,
  end,
  smul_mem' := begin
    intros c x hu,
    simp_rw set.mem_Inter at *,
    intros U hU,
    rw smul_eq_mul,
    let M : K → K := λ t, c * t,
    have hM : continuous M := by refine continuous_mul_left c,
    rw mem_nhds_iff at hU,
    obtain ⟨T,h1,h2,h3⟩ := hU,
    have hMT : is_open (M ⁻¹' T) := h2.preimage hM,
    specialize hu (M ⁻¹' T) _,
    { rw mem_nhds_iff, use (M ⁻¹' T), split, refl, use hMT,
      change c * 0 ∈ T, simpa },
    apply h1,
    exact hu,
  end }

lemma fooprime : ideal.is_prime (infinitesimal_ideal K) :=
begin
  constructor,
  { suffices : (1 : K) ∉ infinitesimal_ideal K,
    { contrapose! this, simp [this] },
    obtain ⟨U,hU,h⟩ := v_topological_ring.cond₂ K,
    dsimp [infinitesimal_ideal],
    simp_rw set.mem_Inter, push_neg, use U, use hU },
  { intros u v hu,
    dsimp [infinitesimal_ideal] at *,
    simp_rw [set.mem_Inter] at *,
    simp_rw ← forall_or_distrib_left,
    simp_rw ← forall_or_distrib_right,
    intros U hU V hV,
    obtain ⟨W,hW1,hW2⟩ := v_topological_ring.cond₁ (U ∩ V) (filter.inter_sets _ hU hV),
    specialize hW2 u v _,
    apply hu _ hW1,
    cases hW2,
    left, exact hW2.2,
    right, exact hW2.1 }
end

variables (R α β : Type*) [comm_ring R] [topological_space R] [topological_ring R]
[ring β]

#check (localization.monoid_of (non_zero_divisors R)).to_monoid_hom.to_fun

lemma local_is_open_map :
  is_open_map
(localization.monoid_of (non_zero_divisors R)).to_monoid_hom.to_fun :=
begin
  intros s s_op,
  let H := (localization.monoid_of (non_zero_divisors R)).to_monoid_hom.to_fun,
  change is_open (H '' s),
  have := @is_open_coinduced R (localization (non_zero_divisors  R)) (infer_instance) (H '' s) H,
  sorry,
end

instance foop2 :
  v_topological_ring (fraction_ring ( K ⧸ (infinitesimal_ideal K) )) :=
{ cond₁ := begin
    intros W hW,
    have := @local_is_open_map K _ _ _,
    sorry,
  end,
  cond₂ := _ }

#check topological_ring_quotient (infinitesimal_ideal K),
#check @localization.topological_ring K _ _ (non_zero_divisors K),
#check @localization.ring_topology K _ _ (non_zero_divisors K)
#check ring_topology.coinduced_continuous (ideal.quotient.mk _)

/-
lemma quotient_ring_is_open_map_coe : is_open_map (ideal.quotient.mk N) :=
begin
  intros s s_op,
  change is_open (mk N ⁻¹' (mk N '' s)),
  rw quotient_ring_saturate,
  exact is_open_Union (λ ⟨n, _⟩, is_open_map_add_left n s s_op)
end
-/
#check algebra_map (K ⧸ (infinitesimal_ideal K)) (fraction_ring (K ⧸ (infinitesimal_ideal K)))
