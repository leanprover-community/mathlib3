
#exit

import data.padics.padic_integers data.polynomial analysis.limits data.real.basic

section
variables {p : ℕ} {hp : p.prime}


open filter
lemma cauchy_of_filter_cauchy (f : ℕ → ℤ_[hp]) (hf : cauchy (at_top.map f)) :
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

lemma filter_cauchy_of_cauchy (f : cau_seq ℤ_[hp] norm) : cauchy (at_top.map f) :=
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

section
open filter


lemma tendsto_coe_iff {f : ℕ → ℕ} : tendsto f at_top at_top ↔ tendsto (λ n, (f n : ℝ)) at_top at_top :=
⟨ λ h, tendsto.comp h tendsto_of_nat_at_top_at_top,
  λ h, tendsto_infi.2 $ λ i, tendsto_principal.2
    (have _, from tendsto_infi.1 h i, by simpa using tendsto_principal.1 this) ⟩

lemma tendsto_pow_at_top_at_top_of_gt_1_nat {k : ℕ} (h : k > 1) : tendsto (λn:ℕ, k ^ n) at_top at_top :=
tendsto_coe_iff.2 $
  have hr : (k : ℝ) > 1, from show (k : ℝ) > (1 : ℕ), from nat.cast_lt.2 h,
  by simpa using tendsto_pow_at_top_at_top_of_gt_1 hr

end