import measure_theory.regular
import measure_theory.simple_func_dense
import topology.urysohns_lemma

open measure_theory topological_space continuous_map
open_locale ennreal

variables  {α : Type*} (E : Type*) [measurable_space α] [topological_space α] [borel_space α]
  [measurable_space E] [normed_group E] [borel_space E] [second_countable_topology E] (p : ℝ≥0∞)
  (μ : measure α)

/-- An additive subgroup of `ae_eq_fun α E μ`, consisting of the equivalence classes which are in
`Lp` and also contain a continuous representative. -/
def continuous_and_Lp_in_ae_eq :=
(@add_monoid_hom.range C(α, E) _ _ _ (to_ae_eq_fun_add_hom μ)) ⊓ (Lp E p μ)

/-- The subgroup `continuous_and_Lp_in_ae_eq` in `ae_eq_fun α E μ` is contained in the subgroup
`Lp E p μ`. -/
lemma continuous_and_Lp_in_ae_eq_le : continuous_and_Lp_in_ae_eq E p μ ≤ (Lp E p μ) :=
inf_le_right

/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
continuous representative. -/
def continuous_and_Lp : add_subgroup (Lp E p μ) :=
(add_subgroup.inclusion (continuous_and_Lp_in_ae_eq_le E p μ)).range

variables {E p μ}

/-- By definition, the elements of `continuous_and_Lp` are the elements of `Lp` which contain a
continuous representative. -/
lemma mem_continuous_and_Lp_iff {f : (Lp E p μ)} :
  f ∈ (continuous_and_Lp E p μ) ↔ ∃ f₀ : C(α, E), to_ae_eq_fun μ f₀ = (f : ae_eq_fun α E μ) :=
begin
  split,
  { rintros ⟨⟨f, ⟨⟨f₀, hff₀⟩, hf⟩⟩, rfl⟩,
    exact ⟨f₀, hff₀⟩ },
  { rintros f',
    exact ⟨⟨f, ⟨f', f.2⟩⟩, subtype.ext rfl⟩ }
end

variables [normal_space α] [normed_space ℝ E]

/-- A simple function in `Lp` can be approximated in `Lp` by continuous functions. -/
lemma measure_theory.simple_func.mem_closure_continuous' [_i : fact (1 ≤ p)] [μ.weakly_regular]
  (hp' : p ≠ ⊤) :
  ∀ f : Lp E p μ, f ∈ (continuous_and_Lp E p μ).topological_closure :=
begin
  refine Lp.induction hp' _ _ _ _,
  { -- The characteristic function of a measurable set can be approximated by continuous functions
    intros c s hs hsμ,
    refine mem_closure_iff_frequently.mpr _,
    rw metric.nhds_basis_ball.frequently_iff,
    intros ε' hε',
    obtain ⟨η, hη_pos, hη_lt⟩ : ∃ η, (0:nnreal) < η ∧ (norm c) * (2 * η) ^ (1 / p.to_real) < ε',
    { sorry },
    have hη_pos' : (0 : ℝ≥0∞) < ↑η := by exact_mod_cast hη_pos,
    -- use the regularity of the measure to approximate `s` by an open superset and a closed subset
    obtain ⟨u, u_open, su, μu⟩ : ∃ u, is_open u ∧ s ⊆ u ∧ μ u < μ s + ↑η,
    { refine hs.exists_is_open_lt_of_lt _ _,
      simpa using (ennreal.add_lt_add_iff_left hsμ).2 hη_pos' },
    obtain ⟨F, F_closed, Fs, μF⟩ : ∃ F, is_closed F ∧ F ⊆ s ∧ μ s < μ F + ↑η :=
      hs.exists_lt_is_closed_of_lt_top_of_pos hsμ hη_pos',
    have : disjoint uᶜ F,
    { rw [set.disjoint_iff_inter_eq_empty, set.inter_comm, ← set.subset_compl_iff_disjoint],
      simpa using Fs.trans su },
    -- apply Urysohn's lemma to get a continuous approximation to the characteristic function of
    -- the set `s`
    obtain ⟨g, hg_cont, hgu, hgF, hg_range⟩ :=
      exists_continuous_zero_one_of_closed u_open.is_closed_compl F_closed this,
    -- multiply this by `c` to get a continuous approximation to the function `f`
    have hgc_cont : continuous (λ x, g x • c),
    { exact continuous_smul.comp (hg_cont.prod_mk continuous_const) },
    have hgc_ℒp : mem_ℒp (λ x, g x • c) p μ,
    { have hu_ℒp : mem_ℒp (set.indicator u (λ x, c)) p μ,
      { refine mem_ℒp_indicator_const p u_open.measurable_set c (or.inr _),
        sorry },
      refine hu_ℒp.of_le (hgc_cont.ae_measurable μ) (filter.eventually_of_forall _),
      intros a,
      by_cases ha : a ∈ uᶜ,
      { have : g a = 0 := by simpa using hgu ha,
        simp [this] },
      { have : ∥g a∥ ≤ 1,
        { rw [real.norm_eq_abs, abs_of_nonneg (hg_range a).1],
          exact (hg_range a).2 },
        have ha' : a ∈ u := by simpa using ha,
        simp [ha'],
        sorry } },
    refine ⟨mem_ℒp.to_Lp (λ x, g x • c) hgc_ℒp, _, _⟩,
    { rw mem_ball_iff_norm,
      -- rw ← mem_ℒp.to_Lp_sub,
      -- rw Lp.norm_to_Lp,
      sorry },
    { rw [set_like.mem_coe, mem_continuous_and_Lp_iff],
      exact ⟨⟨_, hgc_cont⟩, rfl⟩ } },
  { -- If two functions in `Lp` with disjoint support can be approximated by continuous functions,
    -- then so can their sum
    exact λ f g hf hg hfg', add_subgroup.add_mem _ },
  { exact add_subgroup.is_closed_topological_closure }
end

/-- A simple function in `Lp` can be approximated in `Lp` by continuous functions. -/
lemma measure_theory.simple_func.mem_closure_continuous [_i : fact (1 ≤ p)] [μ.weakly_regular]
  (hp' : p ≠ ⊤) :
  ∀ f : simple_func α E, ∀ hf : mem_ℒp f p μ,
  hf.to_Lp f ∈ (continuous_and_Lp E p μ).topological_closure :=
begin
  have hp : 0 < p := lt_of_lt_of_le ennreal.zero_lt_one _i.elim,
  refine simple_func.induction _ _,
  { -- The characteristic function of a measurable set can be approximated by continuous functions
    intros c s hs hf,
    refine mem_closure_iff_frequently.mpr _,
    rw metric.nhds_basis_ball.frequently_iff,
    intros ε' hε',
    by_cases hc : c = 0,
    { exact ⟨0, ⟨by simp [hc, hε'], by simpa using add_subgroup.zero_mem _⟩⟩ },
    have hc' : 0 < nnnorm c := norm_pos_iff.mpr hc,
    have hs' : μ s < ⊤,
    { exact (simple_func.finite_measure_of_mem_ℒp_piecewise hs c hp hp' hf).resolve_left hc },
    obtain ⟨η, hη_pos, hη_lt⟩ : ∃ η, (0:nnreal) < η ∧ (norm c) * (2 * η) ^ (1 / p.to_real) < ε',
    { sorry },
    have hη_pos' : (0 : ℝ≥0∞) < ↑η := by exact_mod_cast hη_pos,
    -- use the regularity of the measure to approximate `s` by an open superset and a closed subset
    obtain ⟨u, u_open, su, μu⟩ : ∃ u, is_open u ∧ s ⊆ u ∧ μ u < μ s + ↑η,
    { refine hs.exists_is_open_lt_of_lt _ _,
      simpa using (ennreal.add_lt_add_iff_left hs').2 hη_pos' },
    obtain ⟨F, F_closed, Fs, μF⟩ : ∃ F, is_closed F ∧ F ⊆ s ∧ μ s < μ F + ↑η :=
      hs.exists_lt_is_closed_of_lt_top_of_pos hs' hη_pos',
    have : disjoint uᶜ F,
    { rw [set.disjoint_iff_inter_eq_empty, set.inter_comm, ← set.subset_compl_iff_disjoint],
      simpa using Fs.trans su },
    -- apply Urysohn's lemma to get a continuous approximation to the characteristic function of
    -- the set `s`
    obtain ⟨g, hg_cont, hgu, hgF, hg_range⟩ :=
      exists_continuous_zero_one_of_closed u_open.is_closed_compl F_closed this,
    -- multiply this by `c` to get a continuous approximation to the function `f`
    have hgc_cont : continuous (λ x, g x • c),
    { exact continuous_smul.comp (hg_cont.prod_mk continuous_const) },
    have hgc_ℒp : mem_ℒp (λ x, g x • c) p μ,
    { have hu_ℒp : mem_ℒp (set.indicator u (λ x, c)) p μ,
      { refine (simple_func.const α c).mem_ℒp_piecewise_of_finite_measure u_open.measurable_set _,
        sorry },
      refine hu_ℒp.of_le (hgc_cont.ae_measurable μ) (filter.eventually_of_forall _),
      intros a,
      by_cases ha : a ∈ uᶜ,
      { have : g a = 0 := by simpa using hgu ha,
        simp [this] },
      { have : ∥g a∥ ≤ 1,
        { rw [real.norm_eq_abs, abs_of_nonneg (hg_range a).1],
          exact (hg_range a).2 },
        have ha' : a ∈ u := by simpa using ha,
        simp [ha'],
        sorry } },
    refine ⟨mem_ℒp.to_Lp (λ x, g x • c) hgc_ℒp, _, _⟩,
    { rw mem_ball_iff_norm,
      rw ← mem_ℒp.to_Lp_sub,
      rw Lp.norm_to_Lp,
      sorry },
    { rw [set_like.mem_coe, mem_continuous_and_Lp_iff],
      exact ⟨⟨_, hgc_cont⟩, rfl⟩ } },
  { -- If two functions in `Lp` with disjoint support can be approximated by continuous functions,
    -- then so can their sum
    intros f g hfg hf hg hfg',
    have h_f_mem : mem_ℒp f p μ := hfg'.of_add_right_disjoint f.ae_measurable hfg,
    have h_g_mem : mem_ℒp g p μ := hfg'.of_add_left_disjoint g.ae_measurable hfg,
    exact add_subgroup.add_mem _ (hf h_f_mem) (hg h_g_mem) },
end
