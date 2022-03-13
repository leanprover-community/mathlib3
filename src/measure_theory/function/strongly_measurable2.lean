import measure_theory.function.simple_func_dense
import measure_theory.function.strongly_measurable


open measure_theory filter topological_space function
open_locale ennreal topological_space measure_theory

namespace measure_theory



section second_countable_topology

variables {α G : Type*} {p : ℝ≥0∞} {m m0 : measurable_space α} {μ : measure α}
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure, `fin_strongly_measurable`
  and `measurable` are equivalent. -/
lemma fin_strongly_measurable_iff_measurable {m0 : measurable_space α} (μ : measure α)
  [sigma_finite μ] :
  fin_strongly_measurable f μ ↔ measurable f :=
⟨λ h, h.measurable, λ h, (measurable.strongly_measurable h).fin_strongly_measurable μ⟩

/-- In a space with second countable topology and a sigma-finite measure,
  `ae_fin_strongly_measurable` and `ae_measurable` are equivalent. -/
lemma ae_fin_strongly_measurable_iff_ae_measurable {m0 : measurable_space α} (μ : measure α)
  [sigma_finite μ] :
  ae_fin_strongly_measurable f μ ↔ ae_measurable f μ :=
by simp_rw [ae_fin_strongly_measurable, ae_measurable, fin_strongly_measurable_iff_measurable]

lemma mem_ℒp.fin_strongly_measurable_of_measurable (hf : mem_ℒp f p μ) (hf_meas : measurable f)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
begin
  let fs := simple_func.approx_on f hf_meas set.univ 0 (set.mem_univ _),
  refine ⟨fs, _, _⟩,
  { have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ, from simple_func.mem_ℒp_approx_on_univ hf_meas hf,
    exact λ n, (fs n).measure_support_lt_top_of_mem_ℒp (h_fs_Lp n) hp_ne_zero hp_ne_top, },
  { exact λ x, simple_func.tendsto_approx_on hf_meas (set.mem_univ 0) (by simp), },
end

lemma mem_ℒp.ae_fin_strongly_measurable (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  ae_fin_strongly_measurable f μ :=
⟨hf.ae_measurable.mk f,
  ((mem_ℒp_congr_ae hf.ae_measurable.ae_eq_mk).mp hf).fin_strongly_measurable_of_measurable
    hf.ae_measurable.measurable_mk hp_ne_zero hp_ne_top,
  hf.ae_measurable.ae_eq_mk⟩

lemma integrable.ae_fin_strongly_measurable (hf : integrable f μ) :
  ae_fin_strongly_measurable f μ :=
(mem_ℒp_one_iff_integrable.mpr hf).ae_fin_strongly_measurable one_ne_zero ennreal.coe_ne_top

lemma Lp.fin_strongly_measurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
(Lp.mem_ℒp f).fin_strongly_measurable_of_measurable (Lp.measurable f) hp_ne_zero hp_ne_top

end second_countable_topology

end measure_theory
