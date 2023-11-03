import probability.ident_distrib
import probability.notation

noncomputable theory

open_locale classical big_operators nnreal ennreal topology

open_locale probability_theory

open nnreal ennreal set filter

lemma is_pi_system.closed {E : Type*} [topological_space E] : is_pi_system ({A : set E | is_closed A}) :=
begin
--  dsimp [is_pi_system],
  intros A hA B hB h,
  exact is_closed.inter hA hB,
end

namespace measure_theory

-- instance measure_theory.probability_measure_map {Ω E : Type*} {mea_Om : measurable_space Ω} [mea_E : measurable_space E] {P : measure Ω} [is_probP : is_probability_measure P] {X : Ω → E} [ae_meas : fact (ae_measurable X P)] : is_probability_measure (measure.map X P)  :=
-- is_probability_measure_map ae_meas.out

section use_topology

variables {Ω Ω' E : Type*} [measurable_space Ω]  [measurable_space Ω'] [measurable_space E] [topological_space E] {X : Ω → E} {Y : Ω' → E}

--include mea_Om
lemma push_forward_iff  {P : measure Ω}
{X : Ω → E} [ae_meas : fact (ae_measurable X P)]
(A : set E) (hA : measurable_set A) : (measure.map X P) A = P (X⁻¹'A) :=
begin
  rw measure_theory.measure.map_apply_of_ae_measurable ae_meas.out hA,
end

lemma ident_distrib_iff
{P : measure Ω} {P' : measure Ω'}
(ae_measX : ae_measurable X P) (ae_measY : ae_measurable Y P') :
((probability_theory.ident_distrib X Y P P') ↔ measure.map X P = measure.map Y P') :=
begin
  split,
  {
    intro h, rw h.map_eq,
  },
  {
    intro h1, exact ⟨ ae_measX, ae_measY, h1⟩,
  },
end

#lint

/-- Two measures are the same iff they are equal on all closed sets.
-/

theorem measure_eq_iff_closed [borel_space E]
{P : measure E} {P' : measure E}
[is_probP : is_probability_measure P] [is_probP' : is_probability_measure P']
 : P = P' ↔ (∀ (A : set E), is_closed A → P A = P' A) :=
begin
  split,
  {
    intros hP A hA, congr, exact hP,
  },
  {
    intro h,
    let C := {A : set E | is_closed A},
    apply measure_theory.ext_of_generate_finite C _ is_pi_system.closed _ _,
    {
      rw ← borel_eq_generate_from_is_closed,
      borelize E,
      refl,
    },
    {
      exact is_probability_measure.to_is_finite_measure P,
    },
    {
      intros A hAC,
      exact h A hAC,
    },
    {
      simp only [measure_theory.is_probability_measure.measure_univ],
    },
  },
end

/-- Two random variables have the same distribution iff their image measures agree on all closed sets.
-/

theorem ident_distrib_iff_closed {E Ω Ω': Type*} {mea_Om : measurable_space Ω} {mea_Om' : measurable_space Ω'} [mea_E : measurable_space E] [top_E : topological_space E] [bor_E : borel_space E] {P : measure Ω} {P' : measure Ω'} {X : Ω → E} {Y : Ω' → E} [is_probability_measure P] [is_probability_measure P'] [ae_meaX : fact (ae_measurable X P)] [ae_meaY : fact (ae_measurable Y P')] : ( (probability_theory.ident_distrib X Y P P') ↔ (∀ (A : set E), is_closed A → P (X⁻¹'A) = P' (Y⁻¹'A))) :=
begin
  split,
  {
    intros h A hA,
    apply probability_theory.ident_distrib.measure_mem_eq h (is_closed.measurable_set hA),
  },
  {
    intro h,
    refine ⟨ ae_meaX.out, ae_meaY.out, _⟩,
    apply measure_eq_iff_closed.2,
    {
      intros A hA,
      rw push_forward_iff,
      rw push_forward_iff,
      exact h A hA,
      exact is_closed.measurable_set hA,
      exact is_closed.measurable_set hA,
    },
    {
      assumption,
    },
    {
      exact is_probability_measure_map ae_meaX.out,
    },
    {
      exact is_probability_measure_map ae_meaY.out,
    },
  },
end

end use_topology

variables {Ω Ω' E : Type*} [measurable_space Ω]  [measurable_space Ω'] [measurable_space E] [pseudo_emetric_space E] [borel_space E] {X : Ω → E} {Y : Ω' → E}

lemma expectation_indicator {E : Type*} {mea_E : measurable_space E} {P : measure E} [is_probability_measure P] (A : set E) (hA : measurable_set A) : ∫ (x : E), A.indicator 1 x ∂P = (P A).to_real :=
begin
  exact measure_theory.integral_indicator_one hA,
end

lemma lexpectation_indicator {E : Type*} {mea_E : measurable_space E} {P : measure E} [is_probability_measure P] (A : set E) (hA : measurable_set A) : ∫⁻ (a : E), A.indicator 1 a ∂P = (P A) :=
begin
  have h1 : P A = 1* (P A), by rw one_mul,
  rw h1,
  rw ← measure_theory.lintegral_indicator_const hA 1,
  congr,
end

lemma lintegral_of_thickened_eq_thickened_aux {E : Type*} [mea_E : measurable_space E] [met_E : pseudo_emetric_space E] [bor_E : borel_space E] {P : measure E} [is_probability_measure P]  {δ : ℝ} (δ_pos : 0 < δ) (A : set E) : ∫⁻ a, (thickened_indicator_aux δ A) a ∂P = ∫⁻ a, (thickened_indicator δ_pos A) a ∂P :=
begin
  congr,
  simp only [thickened_indicator_apply, ennreal.coe_eq_coe, option.mem_def, ennreal.some_eq_coe],
  ext,
  rw ennreal.coe_to_nnreal,
  exact thickened_indicator_aux_lt_top.ne,
end

/-- The lintegral of thickened indicators tends to the measure of a closed set.
-/

theorem lintegral_of_thickened_indicator_tendsto_indicator_closure {E : Type*} {mea_E : measurable_space E} [met_E : pseudo_emetric_space E] [bor_E : borel_space E] {P : measure E} [is_probability_measure P]  {δseq : ℕ → ℝ} (δseq_pos : ∀ (n : ℕ), 0 < δseq n) (δseq_lim : tendsto δseq filter.at_top (nhds 0)) (A : set E) : tendsto (λ n, ∫⁻ a, (thickened_indicator_aux (δseq n) A) a ∂P) at_top (𝓝 (P (closure A))) :=
begin
  have h : measurable_set (closure A),
  {
    apply is_closed.measurable_set, simp only [is_closed_closure],
  },
  rw ← lexpectation_indicator (closure A),
  apply tendsto_lintegral_of_dominated_convergence,
  intro n, apply continuous.measurable,
  simp,
  apply (continuous_thickened_indicator_aux (δseq_pos n) A),
  simp [thickened_indicator_aux_le_one],
  intro n,
  apply eventually_of_forall,
  apply thickened_indicator_aux_le_one (δseq n) A,
  simp only [measure_theory.is_probability_measure.measure_univ, measure_theory.lintegral_one, ne.def, ennreal.one_ne_top, not_false_iff],
  apply eventually_of_forall,
  intro x,
  exact tendsto_pi_nhds.mp (thickened_indicator_aux_tendsto_indicator_closure δseq_lim A) x,
  exact h,
  assumption,
end

lemma lint {E Ω : Type*} {mea_Om : measurable_space Ω} [top_E : topological_space E] [mea_E : measurable_space E] [bor_E : borel_space E] {P : measure Ω} [is_probability_measure P] {X : Ω → E} (ae_mea : ae_measurable X P) (f : bounded_continuous_function E ℝ≥0) : (∫⁻ x, f (x) ∂(measure.map X P) = ∫⁻ ω, f (X ω) ∂P) :=
begin
  apply measure_theory.lintegral_map',
  apply measurable.ae_measurable,
  refine continuous.measurable _,
  continuity,
  exact continuous_coe,
end



/-- Two measures are the same iff their integrals of all bounded continuous functions agree.
-/
theorem measure_eq_iff_bounded_continuous {E : Type*} [mea_E : measurable_space E] [met_E : pseudo_emetric_space E] [bor_E : borel_space E] {P : measure E} {P' : measure E} [is_probability_measure P] [is_probability_measure P'] : (P = P' ↔ ∀ (f : bounded_continuous_function E ℝ≥0), ∫⁻ a, f a ∂P = ∫⁻ a, f a ∂P') :=
begin
  split,
  {
    intros hP f,
    congr, exact hP,
  },
  {
    intro hf,
    rw measure_eq_iff_closed,
    intros A hA,
    rw ← is_closed.closure_eq hA,
    let δseq : ℕ → ℝ := λ n, (1/((n : ℝ) +1)),
    have δseq_pos : ∀ (n : ℕ), 0 < (δseq n),
    {
      intro n, simp [δseq], norm_cast, linarith,
    },
    have δseq_lim : tendsto δseq filter.at_top (nhds 0),
    {
      simp only [δseq],
      apply tendsto_one_div_add_at_top_nhds_0_nat,
    },
    have h_thick : ∀ (δ : ℝ) ( δ_pos : δ > 0) (A : set E), ∫⁻ (a : E), thickened_indicator_aux δ A a ∂P = ∫⁻ (a : E), thickened_indicator_aux δ A a ∂P',
      {
        intros δ δ_pos A,
        rw lintegral_of_thickened_eq_thickened_aux δ_pos,
        rw lintegral_of_thickened_eq_thickened_aux δ_pos,
        exact hf (thickened_indicator δ_pos A),
        assumption,
        assumption,
        assumption,
        assumption,
      },
    have hlim1 : tendsto (λ n, ∫⁻ a, (thickened_indicator_aux (δseq n) A) a ∂P) at_top (𝓝 (P (closure A))),
    {
      apply lintegral_of_thickened_indicator_tendsto_indicator_closure δseq_pos δseq_lim A,
      assumption,
      assumption,
    },
    have hlim2 : tendsto (λ n, ∫⁻ a, (thickened_indicator_aux (δseq n) A) a ∂P') at_top (𝓝 (P' (closure A))),
    {
      apply lintegral_of_thickened_indicator_tendsto_indicator_closure δseq_pos δseq_lim A,
      assumption,
      assumption,
    },
    let x1 := λ n, ∫⁻ (a : E), thickened_indicator_aux (δseq n) A a ∂P,
    let x2 := λ n, ∫⁻ (a : E), thickened_indicator_aux (δseq n) A a ∂P',
    change tendsto x1 at_top (𝓝 (P (closure A))) at hlim1,
    change tendsto x2 at_top (𝓝 (P' (closure A))) at hlim2,
    have h_eq : x1 = x2,
    {
      simp [x1, x2],
      ext n,
      split,
      intro h,
      rw h_thick (δseq n) (δseq_pos n) A at h,
      exact h,
      intro h,
      rw ← h_thick (δseq n) (δseq_pos n) A at h,
      exact h,
    },
    rw h_eq at hlim1,
    exact tendsto_nhds_unique hlim1 hlim2,
  },
end

/-- Two random variables have the same distribution iff their expectations of all bounded continuous functions agree. -/
theorem ident_distrib_iff_bounded_continuous {P : measure Ω} {P' : measure Ω'} {X : Ω → E} {Y : Ω' → E} [is_probability_measure P] [is_probability_measure P'] (ae_meaX : ae_measurable X P) (ae_meaY : ae_measurable Y P') : ( (probability_theory.ident_distrib X Y P P') ↔ (∀ (f : bounded_continuous_function E ℝ≥0),
--P[λ ω, (f (X ω) : ℝ)] = P'[λ ω', f (Y ω')]
∫⁻ ω, f (X ω) ∂P = ∫⁻ ω', f (Y ω') ∂P'
))
:=
begin
  rw ident_distrib_iff ae_meaX ae_meaY,
--  simp_rw integral_to_real,
--  simp_rw integral_eq_lintegral_of_nonneg_ae,
  simp_rw [← lint ae_meaX _, ← lint ae_meaY _],
  haveI : is_probability_measure (P.map X) := is_probability_measure_map ae_meaX,
  haveI : is_probability_measure (P'.map Y) := is_probability_measure_map ae_meaY,
  rw ← measure_eq_iff_bounded_continuous,
end

#lint

end measure_theory

#lint
