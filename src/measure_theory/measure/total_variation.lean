import measure_theory.decomposition.jordan
import data.setoid.partition

noncomputable theory
open_locale classical measure_theory ennreal

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

namespace vector_measure

include m

variables {M : Type*} [normed_group M] [topological_space M]

-- def total_variation (v : vector_measure α M) : set α → ℝ≥0∞ :=
-- λ s, ⨆ (t : ℕ → set s) (ht : indexed_partition t), ∑' n, ∥v ↑(t n)∥₊

variables {v : vector_measure α M}

end vector_measure

end measure_theory
