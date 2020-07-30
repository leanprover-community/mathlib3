import measure_theory.borel_space
import measure_theory.measure_space

open measure_theory set filter
open_locale classical topological_space

variables {α β : Type*} [measurable_space α] [topological_space α]

class locally_finite_measure (μ : measure α) : Prop :=
(locally_finite : ∀ x : α, ∃ s ∈ 𝓝 x, μ s < ⊤)

@[priority 100]
instance loaclly_finite_measure_of_finite (μ : measure α) [finite_measure μ] :
  locally_finite_measure μ :=
⟨λ x, ⟨univ, univ_mem_sets, meas_univ_lt_top⟩⟩

variables (x : α) (μ : measure α) [locally_finite_measure μ]

lemma exists_mem_nhds_finite_meas : ∃ s ∈ 𝓝 x, μ s < ⊤ :=
locally_finite_measure.locally_finite x

lemma exists_mem_finite_meas_of_le_nhds {f : filter α} {x} (hf : f ≤ 𝓝 x) : ∃ s ∈ f, μ s < ⊤ :=
let ⟨s, hs, hμ⟩ := exists_mem_nhds_finite_meas x μ in ⟨s, hf hs, hμ⟩

lemma is_compact.finite_measure {s : set α} (hs : is_compact s) :
  μ s < ⊤ :=
hs.finite_measure_of_nhds_within $ λ a ha,
  let ⟨s, hs, hμ⟩ := exists_mem_nhds_finite_meas a μ
  in ⟨s, mem_nhds_within_of_mem_nhds hs, hμ⟩

/-- A locally finite measure on a compact space is finite. -/
def finite_measure_of_locally_finite [compact_space α] : finite_measure μ :=
⟨compact_univ.finite_measure _⟩
