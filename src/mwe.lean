import measure_theory.measure.haar
import measure_theory.constructions.pi

open topological_space set filter function

lemma is_open_pi_iff {ι : Type*} [fintype ι] {α : ι → Type*} [Π i, topological_space (α i)]
  {s : set (Π i, α i)} :
  is_open s ↔
  (∀ f, f ∈ s → ∃ (u : Π i, set (α i)), (∀ i, is_open (u i) ∧ f i ∈ u i) ∧ set.univ.pi u ⊆ s) :=
begin
  rw [is_open_iff_nhds],
  simp_rw [le_principal_iff],
  simp_rw nhds_pi,
  simp_rw filter.mem_pi',
  simp_rw mem_nhds_iff,
  simp_rw [exists_prop],
  split,
  { intros h f hf,
    specialize h f hf,
    obtain ⟨I, ⟨t, ht⟩⟩ := h,
    let ht1 := ht.1,
    use λ i, (ht1 i).some,
    split,
    { intro i,
      have := (ht1 i).some_spec,
      exact ⟨this.2.1, this.2.2⟩, },
    { intros p hp,
      rw set.mem_pi at hp,
      suffices : p ∈ (I : set ι).pi t,
      { exact ht.2 this, },
      rw set.mem_pi,
      intros i _,
      specialize hp i (set.mem_univ _),
      exact (ht1 i).some_spec.1 hp, }},
  { intros h a ha,
    use finset.univ,
    specialize h a ha,
    obtain ⟨u, hu⟩ := h,
    use u,
    split,
    { intro i,
      use u i,
      split,
      { exact rfl.subset, },
      { exact (hu.1 i), }},
    { simp only [*, finset.coe_univ], }}
end

open measure_theory measure_theory.measure

instance {ι : Type*} {G : ι → Type*} [fintype ι] [Π i, topological_space (G i)]
  {mG : Π i, measurable_space (G i)} (μ : Π i, measure (G i))
  [Π i, is_open_pos_measure (μ i)] [Π i, sigma_finite (μ i)]:
  is_open_pos_measure (measure_theory.measure.pi μ) :=
begin
  constructor,
  rintros U U_open ⟨a, ha⟩,
  obtain ⟨s, ⟨hs, hsU⟩⟩ := is_open_pi_iff.1 U_open a ha,
  have t1 : ∀ i, 0 < (μ i) (s i),
  begin
    intro i,
    refine (hs i).1.measure_pos (μ i) _,
    exact ⟨a i, (hs i).2⟩,
  end,
  contrapose! t1,
  have t2 := @measure_mono_null _ _ (measure.pi μ) _ _ hsU t1,
  rw measure.pi_pi at t2,
  rw finset.prod_eq_zero_iff at t2,
  obtain ⟨i, ⟨_, hi⟩⟩ := t2,
  use i,
  exact le_of_eq hi,
end

instance {ι : Type*} {G : ι → Type*} [fintype ι] [Π i, topological_space (G i)]
  {mG : Π i, measurable_space (G i)} (μ : Π i, measure (G i)) [Π i, sigma_finite (μ i)]
  [Π i, is_finite_measure_on_compacts (μ i)] :
  is_finite_measure_on_compacts (measure_theory.measure.pi μ) :=
begin
  constructor,
  intros K hK,
  let K0 : Π (i : ι), set (G i) :=
  begin
    intro j,
    refine (function.eval j) '' K,
  end,
  have t1 : ∀ i, is_compact (eval i '' K) :=
  begin
    intro i,
    refine is_compact.image hK _,
    refine continuous_apply i,
  end,
  have t2 : K ⊆ set.univ.pi K0 := by refine univ.subset_pi_eval_image K,
  suffices : measure.pi μ (set.univ.pi K0) < ⊤,
  { have t3 := @measure_mono _ _ ( measure.pi μ) _ _ t2,
    exact lt_of_le_of_lt t3 this, },
  rw measure.pi_pi,
  have : ∀ i, (μ i) (K0 i) < ⊤,
  begin
    intro i,
    exact is_compact.measure_lt_top (t1 i),
  end,
  refine with_top.prod_lt_top _,
  intros i _,
  refine ne_of_lt (this i),
end

@[to_additive]
instance {ι : Type*} {G : ι → Type*} [fintype ι] [Π i, group (G i)] [Π i, topological_space (G i)]
  {mG : Π i, measurable_space (G i)}
  (μ : Π i, measure (G i)) [Π i, is_haar_measure (μ i)]
  [Π i, sigma_finite (μ i)]
  [Π i, has_measurable_mul (G i)] :
  is_haar_measure (measure_theory.measure.pi μ) := {}
