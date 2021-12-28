/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import topology.constructions
import topology.homeomorph

lemma homeo_of_equiv_compact_to_t2.t1_counterexample :
  ∃ (α β : Type) (Iα : topological_space α) (Iβ : topological_space β), by exactI
  compact_space α ∧ t1_space β ∧ ∃ f : α ≃ β, continuous f ∧ ¬ continuous f.symm :=
begin
  let topα : topological_space ℕ := topological_space.nhds_adjoint 0 filter.cofinite,
  let topβ : topological_space ℕ := topological_space.cofinite_topology ℕ,
  refine ⟨ℕ , ℕ, topα, topβ, _, t1_space_cofinite, equiv.refl ℕ, _, _⟩,
  { constructor,
    rw is_compact_iff_ultrafilter_le_nhds,
    intros f,
    suffices : ∃ a, ↑f ≤ @nhds _ topα a, by simpa,
    by_cases hf : ↑f ≤ @nhds _ topα 0,
    { exact ⟨0, hf⟩ },
    { obtain ⟨U, h0U, hU_fin, hUf⟩ : ∃ U : set ℕ, 0 ∈ U ∧ Uᶜ.finite ∧ U ∉ f,
      { rw [nhds_adjoint_nhds, filter.le_def] at hf,
        push_neg at hf,
        simpa [and_assoc] using hf },
      rw ← ultrafilter.compl_mem_iff_not_mem at hUf,
      obtain ⟨n, hn', hn⟩ := ultrafilter.eq_principal_of_finite_mem hU_fin hUf,
      use n,
      intros s' hns',
      rw hn,
      exact @mem_of_mem_nhds _ topα n _ hns' } },
  { rw continuous_iff_coinduced_le,
    change topα ≤ topβ,
    rw gc_nhds,
    simp [nhds_cofinite] },
  { intros h,
    replace h : topβ ≤ topα, by simpa [continuous_iff_coinduced_le, coinduced_id] using h,
    rw le_nhds_adjoint_iff at h,
    exact  (finite_singleton 1).infinite_compl (h.2 1 one_ne_zero ⟨1, mem_singleton 1⟩) }
end