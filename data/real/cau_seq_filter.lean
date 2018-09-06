/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Reconcile the filter notion of Cauchy-ness with the cau_seq notion on normed spaces.
-/

import analysis.topology.uniform_space analysis.normed_space data.real.cau_seq
section

variables
  {β : Type*} [normed_field β]

instance normed_field.is_absolute_value : is_absolute_value (norm : β → ℝ) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := norm_eq_zero,
  abv_add := norm_triangle,
  abv_mul := normed_field.norm_mul }

open filter

lemma cauchy_of_filter_cauchy (f : ℕ → β) (hf : cauchy (at_top.map f)) :
  is_cau_seq norm f :=
begin
  cases cauchy_iff.1 hf with hf1 hf2,
  intros ε hε,
  rcases hf2 {x | dist x.1 x.2 < ε} (dist_mem_uniformity hε) with ⟨t, ⟨ht, htsub⟩⟩,
  simp at ht, cases ht with N hN,
  existsi N,
  intros j hj,
  rw ←dist_eq_norm,
  apply @htsub (f j, f N),
  apply set.mk_mem_prod; solve_by_elim {discharger := `[apply le_refl]}
end

lemma filter_cauchy_of_cauchy (f : cau_seq β norm) : cauchy (at_top.map f) :=
begin
  apply cauchy_iff.2,
  split,
  { exact map_ne_bot at_top_ne_bot },
  { intros s hs,
    rcases mem_uniformity_dist.1 hs with ⟨ε, ⟨hε, hεs⟩⟩,
    cases cau_seq.cauchy₂ f hε with N hN,
    existsi {n | n ≥ N}.image f,
    simp, split,
    { existsi N, intros b hb, existsi b, simp [hb] },
    { rintros ⟨a, b⟩ ⟨⟨a', ⟨ha'1, ha'2⟩⟩, ⟨b', ⟨hb'1, hb'2⟩⟩⟩,
      dsimp at ha'1 ha'2 hb'1 hb'2,
      rw [←ha'2, ←hb'2],
      apply hεs,
      rw dist_eq_norm,
      apply hN; assumption }},
  { apply_instance }
end


end