import measure_theory.borel_space
import measure_theory.measure_space

open measure_theory set filter
open_locale classical topological_space

variables {α β : Type*} [measurable_space α] [topological_space α]

class locally_finite_measure (μ : measure α) : Prop :=
(locally_finite : ∀ x : α, ∃ s ∈ 𝓝 x, μ s < ⊤)

variables (x : α) (μ : measure α) [locally_finite_measure μ]

lemma exists_mem_nhds_finite_meas : ∃ s ∈ 𝓝 x, μ s < ⊤ :=
locally_finite_measure.locally_finite x

-- lemma is_compact.finite_measure {s : set α} (hs : is_compact s) :
--   μ s < ⊤ :=
-- begin
--   rw ← measure.compl_mem_cofinite,
--   refine hs.compl_mem_sets_of_nhds_within (λ a ha, _),
--   rcases exists_mem_nhds_finite_meas a μ with ⟨t, hta, ht⟩,
--   rw ← measure.compl_mem_cofinite at ht,
--   exact ⟨t, hta, mem_sets_of_superset ht (subset_union_left _ _)⟩
-- end

/-- A locally finite measure on a compact space is finite. -/
def finite_measure_of_locally_finite [compact_space α] : finite_measure μ :=
⟨compact_univ.finite_measure _⟩
