import measure_theory.measure.haar
import measure_theory.constructions.pi

open topological_space set filter function measure_theory measure_theory.measure

lemma is_open_pi_iff {ι : Type*} [fintype ι] {α : ι → Type*} [Π i, topological_space (α i)]
  {s : set (Π i, α i)} :
  is_open s ↔
  (∀ f, f ∈ s → ∃ (u : Π i, set (α i)), (∀ i, is_open (u i) ∧ f i ∈ u i) ∧ set.univ.pi u ⊆ s) :=
begin
  rw is_open_iff_nhds,
  simp_rw [le_principal_iff, nhds_pi, filter.mem_pi', mem_nhds_iff, exists_prop],
  refine ball_congr (λ a h, ⟨_, _⟩),
  { rintros ⟨I, t, ⟨h1, h2⟩⟩,
    refine ⟨λ i, (h1 i).some, ⟨λ i, ⟨(h1 i).some_spec.2.1, (h1 i).some_spec.2.2⟩,
        (set.pi_mono (λ i _, (h1 i).some_spec.1)).trans (subset.trans _ h2)⟩⟩,
    rw ← set.pi_inter_compl (I : set ι),
    exact inter_subset_left _ _, },
  { exact λ ⟨u, ⟨h1, _⟩⟩, ⟨finset.univ, u, ⟨λ i, ⟨u i, ⟨rfl.subset, h1 i⟩⟩,
      by rwa finset.coe_univ⟩⟩, }
end

instance {ι : Type*} {G : ι → Type*} [fintype ι] [Π i, topological_space (G i)]
  {mG : Π i, measurable_space (G i)} (μ : Π i, measure (G i))
  [Π i, is_open_pos_measure (μ i)] [Π i, sigma_finite (μ i)]:
  is_open_pos_measure (measure_theory.measure.pi μ) :=
begin
  constructor,
  rintros U U_open ⟨a, ha⟩,
  obtain ⟨s, ⟨hs, hsU⟩⟩ := is_open_pi_iff.1 U_open a ha,
  by_contra,
  suffices : (measure.pi μ) (univ.pi s) = 0,
  { rw [measure.pi_pi, finset.prod_eq_zero_iff] at this,
    obtain ⟨i, ⟨_, hi⟩⟩ := this,
    exact (ne_of_gt ((hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩)) hi, },
  exact measure_mono_null hsU h,
end

instance {ι : Type*} {G : ι → Type*} [fintype ι] [Π i, topological_space (G i)]
  {mG : Π i, measurable_space (G i)} (μ : Π i, measure (G i)) [Π i, sigma_finite (μ i)]
  [Π i, is_finite_measure_on_compacts (μ i)] :
  is_finite_measure_on_compacts (measure_theory.measure.pi μ) :=
begin
  constructor,
  intros K hK,
  suffices : measure.pi μ (set.univ.pi ( λ j, (function.eval j) '' K)) < ⊤,
  { exact lt_of_le_of_lt (measure_mono (univ.subset_pi_eval_image K)) this, },
  rw measure.pi_pi,
  refine with_top.prod_lt_top _,
  exact λ i _, ne_of_lt (is_compact.measure_lt_top (is_compact.image hK (continuous_apply i))),
end

@[to_additive]
instance {ι : Type*} {G : ι → Type*} [fintype ι] [Π i, group (G i)] [Π i, topological_space (G i)]
  {mG : Π i, measurable_space (G i)}
  (μ : Π i, measure (G i)) [Π i, is_haar_measure (μ i)]
  [Π i, sigma_finite (μ i)]
  [Π i, has_measurable_mul (G i)] :
  is_haar_measure (measure_theory.measure.pi μ) := {}
