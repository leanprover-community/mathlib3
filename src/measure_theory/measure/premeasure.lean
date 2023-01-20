import measure_theory.measure.outer_measure

open_locale ennreal topological_space

namespace measure_theory

open filter

variables {α : Type*} {P : set α → Prop} {m : Π (s : set α), P s → ℝ≥0∞}


#check induced_outer_measure
/-
Given non-negative, finite function defined on a subset of sets which is additive saitisfying
the continuity from above, then it is countably additive.

As a result, if the domain is a algebra (closed under union and complements), it is a premeasure
and hence, induces a measure via `induced_outer_measure` and `outer_measure.to_measure`.
-/

-- lemma Union_eq_sum_of
--   (hP : ∀ {s t}, P s → P t → P (s ∪ t))
--   (hm₁ : ∀ {s t} (hs : P s) (ht : P t), disjoint s t → m (s ∪ t) (hP hs ht) = m s hs + m t ht)
--   (hm₂ : ∀ {s : ℕ → set α} (hs : ∀ ),  antitone s → ⋂ n, s n = ∅ →  )



end measure_theory
