import measure_theory.decomposition.lebesgue

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace measure

/-- **The Radon-Nikodym theorem**: Given two finite measures `μ` and `ν`, if `ν` is absolutely
continuous with respect to `μ`, then there exists a measurable function `f` such that
`f` is the derivative of `ν` with respect to `μ`. -/
theorem exists_with_density_of_absolute_continuous
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] (h : ν ≪ μ) :
  ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν = μ.with_density f :=
begin
  obtain ⟨ν₁, ν₂, _, _, hν, ⟨E, hE₁, hE₂, hE₃⟩, f, hf₁, hf₂⟩ :=
    exists_singular_with_density μ ν,
  have : ν₁ = 0,
  { apply le_antisymm,
    { intros A hA,
      suffices : ν₁ set.univ = 0,
      { rw [measure.coe_zero, pi.zero_apply, ← this],
        exact measure_mono (set.subset_univ _) },
      rw [← set.union_compl_self E, measure_union (@disjoint_compl_right _ E _) hE₁ hE₁.compl,
          hE₂, zero_add],
      have : (ν₁ + ν₂) Eᶜ = ν Eᶜ, { rw hν },
      rw [measure.coe_add, pi.add_apply, h hE₃] at this,
      exact (add_eq_zero_iff.1 this).1 },
    { exact measure.zero_le _} },
  rw [this, zero_add] at hν,
  exact ⟨f, hf₁, hν.symm ▸ hf₂⟩,
end

section sigma_finite

lemma exists_disjoint_finite_spanning_sets_in (μ : measure α) [sigma_finite μ] :
  ∃ S : μ.finite_spanning_sets_in {s | measurable_set s},
    pairwise (disjoint on S.set) :=
let T := μ.to_finite_spanning_sets_in in
⟨⟨disjointed T.set, measurable_set.disjointed T.set_mem,
  λ n, lt_of_le_of_lt (measure_mono (disjointed_subset T.set n)) (T.finite _),
  T.spanning ▸ Union_disjointed⟩, disjoint_disjointed _⟩

lemma exists_eq_finite_spanning_sets_in
  (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
  ∃ (S : μ.finite_spanning_sets_in {s | measurable_set s})
    (T : ν.finite_spanning_sets_in {s | measurable_set s}), S.set = T.set :=
begin
  obtain ⟨S, hS⟩ := exists_disjoint_finite_spanning_sets_in μ,
  obtain ⟨T, hT⟩ := exists_disjoint_finite_spanning_sets_in ν,
  set W := disjointed (λ n, S.set n ∩ T.set n),
  refine ⟨⟨W, measurable_set.disjointed (λ n, (S.set_mem n).inter (T.set_mem n)), _, _⟩, _⟩,
  { sorry },
  { rw [Union_disjointed], sorry

    --set.Union_inter_distrib, S.spanning, T.spanning, set.union_univ]
  },
  { sorry }
end

-- lemma exists_eq_disjoint_finite_spanning_sets_in
--   (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
--   ∃ (S : μ.finite_spanning_sets_in {s | measurable_set s})
--     (T : ν.finite_spanning_sets_in {s | measurable_set s}),
--     S.set = T.set ∧ pairwise (disjoint on S.set) ∧ pairwise (disjoint on T.set) :=
-- begin
--   obtain ⟨S, T, hST⟩ := exists_eq_finite_spanning_sets_in μ ν,
--   refine ⟨⟨diff_le S.set, _, _, S.spanning ▸ Union_diff_le_eq _⟩,
--           ⟨diff_le T.set, _, _, T.spanning ▸ Union_diff_le_eq _⟩,
--            _, diff_le_pairwsie_disjoint _, diff_le_pairwsie_disjoint _⟩,
--   { intros n, cases n,
--     { exact S.set_mem 0 },
--     { exact measurable_set.diff (S.set_mem _) (measurable_set.Union
--         (λ _, measurable_set.Union_Prop (λ _, S.set_mem _))) } },
--   { intro n,
--     exact lt_of_le_of_lt (measure_mono (diff_le_subset S.set n)) (S.finite _) },
--   { intros n, cases n,
--     { exact T.set_mem 0 },
--     { exact measurable_set.diff (T.set_mem _) (measurable_set.Union
--         (λ _, measurable_set.Union_Prop (λ _, T.set_mem _))) } },
--   { intro n,
--     exact lt_of_le_of_lt (measure_mono (diff_le_subset T.set n)) (T.finite _) },
--   { simp [hST] },
-- end

theorem exists_with_density_of_absolute_continuous'
  (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] (h : ν ≪ μ) :
  ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν = μ.with_density f :=
begin
  sorry
end

end sigma_finite

end measure

end measure_theory
