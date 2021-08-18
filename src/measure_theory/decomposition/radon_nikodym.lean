import measure_theory.decomposition.lebesgue

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace measure

/-- **The Radon-Nikodym theorem**: Given two finite measures `μ` and `ν`, if `ν` is absolutely
continuous with respect to `μ`, then there exists a measurable function `f` such that
`f` is the derivative of `ν` with respect to `μ`. -/
theorem with_density_radon_nikodym_deriv_eq_of_finite
  (μ ν : measure α) (hl : have_lebesgue_decomposition μ ν) (h : μ ≪ ν) :
  ν.with_density (radon_nikodym_deriv μ ν) = μ :=
begin
  obtain ⟨hf₁, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩:= have_lebesgue_decomposition_spec hl,
  have : singular_part μ ν = 0,
  { apply le_antisymm,
    { intros A hA,
      suffices : singular_part μ ν set.univ = 0,
      { rw [measure.coe_zero, pi.zero_apply, ← this],
        exact measure_mono (set.subset_univ _) },
      rw [← set.union_compl_self E, measure_union (@disjoint_compl_right _ E _) hE₁ hE₁.compl,
          hE₂, zero_add],
      have : (singular_part μ ν + ν.with_density (radon_nikodym_deriv μ ν)) Eᶜ = μ Eᶜ,
      { rw ← hadd },
      rw [measure.coe_add, pi.add_apply, h hE₃] at this,
      exact (add_eq_zero_iff.1 this).1 },
    { exact measure.zero_le _} },
  rw [this, zero_add] at hadd,
  exact hadd.symm
end

section sigma_finite

def disjointed_finite_spanning_sets_in {μ : measure α}
  (S : μ.finite_spanning_sets_in {s | measurable_set s}) :
   μ.finite_spanning_sets_in {s | measurable_set s} :=
⟨disjointed S.set, measurable_set.disjointed S.set_mem,
  λ n, lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
  S.spanning ▸ Union_disjointed⟩

lemma disjoint_disjointed_finite_spanning_sets_in {μ : measure α}
  (S : μ.finite_spanning_sets_in {s | measurable_set s}) :
  pairwise (disjoint on (disjointed_finite_spanning_sets_in S).set) :=
disjoint_disjointed _

lemma set.Union_unpair_inter (s t : ℕ → set α) :
  (⋃ n : ℕ, s n.unpair.1 ∩ t n.unpair.2) = ⋃ i j : ℕ, s i ∩ t j :=
begin
  have : (⋃ i : ℕ × ℕ, s i.1 ∩ t i.2) = ⋃ i j : ℕ, s i ∩ t j,
  { ext, simp only [set.mem_Union, prod.exists] },
  rw [← this, ← nat.surjective_unpair.Union_comp],
end

lemma exists_eq_finite_spanning_sets_in
  (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
  ∃ (S : μ.finite_spanning_sets_in {s | measurable_set s})
    (T : ν.finite_spanning_sets_in {s | measurable_set s}), S.set = T.set :=
begin
  set S := μ.to_finite_spanning_sets_in,
  set T := ν.to_finite_spanning_sets_in,
  set W := λ n : ℕ, S.set n.unpair.1 ∩ T.set n.unpair.2 with hW,
  have hW₁ : ∀ n, measurable_set (W n) :=
    λ n, (S.set_mem n.unpair.1).inter (T.set_mem n.unpair.2),
  have hW₂ : (⋃ i, W i) = set.univ,
  { simp_rw [hW, set.Union_unpair_inter, ← set.inter_Union, ← set.Union_inter,
             S.spanning, T.spanning, set.inter_univ] },
  refine ⟨⟨W, hW₁, _, hW₂⟩, ⟨W, hW₁, _, hW₂⟩, rfl⟩,
  { intro i,
    refine lt_of_le_of_lt (measure_mono _) (S.finite i.unpair.1),
    exact set.inter_subset_left _ _ },
  { intro i,
    refine lt_of_le_of_lt (measure_mono _) (T.finite i.unpair.2),
    exact set.inter_subset_right _ _ },
end

lemma exists_eq_disjoint_finite_spanning_sets_in
  (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
  ∃ (S : μ.finite_spanning_sets_in {s | measurable_set s})
    (T : ν.finite_spanning_sets_in {s | measurable_set s}),
    S.set = T.set ∧ pairwise (disjoint on S.set) :=
begin
  obtain ⟨S, T, hST⟩ := exists_eq_finite_spanning_sets_in μ ν,
  refine ⟨disjointed_finite_spanning_sets_in S, disjointed_finite_spanning_sets_in T, _, _⟩,
  { simp [disjointed_finite_spanning_sets_in, hST] },
  { exact disjoint_disjointed_finite_spanning_sets_in _ }
end

end sigma_finite

end measure

end measure_theory
