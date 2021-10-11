import analysis.specific_limits

variables {E F : Type*} [semi_normed_group E] [semi_normed_group F]

open set filter
open_locale big_operators topological_space uniformity

lemma controlled_sum_of_mem_closure {s : add_subgroup E} {g : E}
  (hg : g ∈ closure (s : set E)) {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ v : ℕ → E, summable (λ n, ∥v n∥) ∧ has_sum v g ∧
    (∀ n, v n ∈ s) ∧
    ∥v 0 - g∥ < b 0 ∧
    ∀ n > 0, ∥v n∥ < b n :=
begin
  set b' : ℕ → ℝ := λ n, min (b n) ((1 / 2) ^ n),
  have b'_pos : ∀ n, 0 < b' n, from λ n, lt_min (b_pos n) (pow_pos one_half_pos n),
  have mem_𝓤 : ∀ n, {p : E × E | ∥p.1 - p.2∥ < b' n} ∈ 𝓤 E,
   from λ n, by simpa only [← dist_eq_norm] using metric.dist_mem_uniformity (b'_pos n),
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : tendsto u at_top (𝓝 g)⟩ :=
    mem_closure_iff_seq_limit.mp hg,
  rcases lim_u.subseq_mem_entourage mem_𝓤 with ⟨φ, φ_mono, h0, h_norm⟩,
  set v : ℕ → E := λ n, nat.cases_on n (u (φ 0)) (λ n, u (φ (n + 1)) - u (φ n)),
  have hv : ∀ n, 1 ≤ n → ∥v n∥ < b' n,
  { intros n hn, rcases le_iff_exists_add.1 hn with ⟨n, rfl⟩,
    rw add_comm, exact h_norm n },
  have hv_le : ∀ᶠ n in at_top, ∥v n∥ ≤ 1 * (1 / 2) ^ n,
  { filter_upwards [mem_at_top 1], intros n hn,
    simpa only [one_mul] using ((hv n hn).le.trans (min_le_right _ _)) },
  have hv_cauchy : cauchy_seq (λ s, ∑ k in s, v k),
    from cauchy_seq_finset_of_geometric_bound one_half_lt_one hv_le,
  have hv_summable : summable (λ n, ∥v n∥),
    from summable_of_geometric_bound one_half_lt_one (by simpa only [norm_norm] using hv_le),
  have hvs : ∀ n, v n ∈ s,
  { rintro (_|n), exacts [u_in (φ 0), s.sub_mem (u_in _) (u_in _)] },
  refine ⟨v, hv_summable, _, hvs, lt_of_lt_of_le h0 (min_le_left _ _),
    λ k hk, (hv k hk).trans_le (min_le_left _ _)⟩,
  refine tendsto_nhds_of_cauchy_seq_of_subseq hv_cauchy
    (tendsto_finset_range.comp (tendsto_add_at_top_nat 1)) _,
  exact (lim_u.comp φ_mono.tendsto_at_top).congr (finset.eq_sum_range_sub' _)
end

lemma controlled_sum_of_mem_closure_range {j : E →+ F} {h : F}
  (Hh : h ∈ (closure $ (j.range : set F))) {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ g : ℕ → E, summable (λ n, ∥j (g n)∥) ∧ has_sum (j ∘ g) h ∧
    ∥j (g 0) - h∥ < b 0 ∧
    ∀ n > 0, ∥j (g n)∥ < b n :=
begin
  rcases controlled_sum_of_mem_closure Hh b_pos with ⟨v, sum_v, sum_vh, v_in, hv₀, hv_pos⟩,
  choose g hg using v_in,
  obtain rfl : j ∘ g = v := funext hg,
  exact ⟨g, sum_v, sum_vh, hv₀, hv_pos⟩
end
