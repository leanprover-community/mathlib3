import .integral_eq_improper
import ..function.conditional_expectation

open measure_theory set
open_locale classical

variables {α β ι : Type*}

namespace measurable_space

-- def restrict (m : measurable_space α) (s : set α) : measurable_space α :=
-- measurable_space.generate_from { t : set α | t ⊆ s ∧ measurable_set t }

-- variables {m : measurable_space α}
-- lemma restrict_mono  {s t : set α} (h : s ⊆ t) : m.restrict s ≤ m.restrict t :=
-- generate_from_mono $ λ t ht, ⟨ht.1.trans h, ht.2⟩

-- lemma restrict_univ : m.restrict univ = m :=
-- by simp_rw [restrict, subset_univ, true_and, generate_from_measurable_set]

-- lemma restrict_le_self {s : set α} : m.restrict s ≤ m :=
-- by { convert restrict_mono (subset_univ s), rw [restrict_univ] }

-- lemma restrict_Union [encodable ι] (m : measurable_space α) (s : ι → set α)
--   (hs : ∀ i, m.measurable_set' (s i)) :
--   m.restrict (⋃ i, s i) = ⨆ i, m.restrict (s i) :=
-- begin
--   apply le_antisymm,
--   { rw [restrict, generate_from_le_iff, set_of_subset_set_of],
--     rintros t ⟨h1t, h2t⟩,
--     rw [← inter_eq_left_iff_subset, inter_Union] at h1t,
--     rw [← h1t], refine @measurable_set.Union _ _ (⨆ i, m.restrict (s i)) _ _ _,
--     intros i, rw [measurable_set_supr],
--     apply generate_measurable.basic,
--     refine ⟨i, measurable_set_generate_from ⟨inter_subset_right _ _, h2t.inter (hs i)⟩⟩ },
--   { rw [supr_le_iff], intro i, apply restrict_mono, apply subset_Union }
-- end

def discrete_outside (m : measurable_space α) (s : set α) : measurable_space α :=
measurable_space.generate_from { t : set α | t ⊆ s → measurable_set t }

variables {m : measurable_space α}
lemma discrete_outside_mono  {s t : set α} (h : s ⊆ t) :
  m.discrete_outside t ≤ m.discrete_outside s :=
generate_from_mono $ λ u hu hus, hu $ hus.trans h

lemma discrete_outside_univ : m.discrete_outside univ = m :=
by simp_rw [discrete_outside, subset_univ, true_implies_iff, generate_from_measurable_set]

lemma le_discrete_outside {s : set α} : m ≤ m.discrete_outside s :=
by { convert discrete_outside_mono (subset_univ s), rw [discrete_outside_univ] }

lemma discrete_outside_Union [encodable ι] (m : measurable_space α) (s : ι → set α)
  (hs : ∀ i, m.measurable_set' (s i)) :
  m.discrete_outside (⋃ i, s i) = ⨅ i, m.discrete_outside (s i) :=
begin
  -- apply le_antisymm,
  -- { rw [discrete_outside, generate_from_le_iff, set_of_subset_set_of],
  --   rintros t ⟨h1t, h2t⟩,
  --   rw [← inter_eq_left_iff_subset, inter_Union] at h1t,
  --   rw [← h1t], refine @measurable_set.Union _ _ (⨆ i, m.discrete_outside (s i)) _ _ _,
  --   intros i, rw [measurable_set_supr],
  --   apply generate_measurable.basic,
  --   refine ⟨i, measurable_set_generate_from ⟨inter_subset_right _ _, h2t.inter (hs i)⟩⟩ },
  -- { rw [supr_le_iff], intro i, apply discrete_outside_mono, apply subset_Union }
  sorry
end

end measurable_space
open measurable_space

variables {m : measurable_space α} [measurable_space α] [measurable_space β] {μ : measure α}
variables {f : α → β}

open_locale measure_theory

lemma ae_measurable_discrete_outside_iff {s : set α} (hs : measurable_set s) :
  ae_measurable' (measurable_space.discrete_outside ‹_› s) f μ ↔ ae_measurable f (μ.restrict s) :=
begin
  split,
  { rintro ⟨g, hg, hfg⟩,
    by_cases nonempty β,
    cases h with y₀,
    refine ⟨λ x, if x ∈ s then g x else y₀, _, _⟩, sorry, sorry, sorry },
  { rintro ⟨g, hg, hfg⟩, refine ⟨λ x, if x ∈ s then g x else f x, _, _⟩, sorry,
    sorry }
end

lemma ae_measurable'_Inf {m : ι → measurable_space α} :
  ae_measurable' (⨅ i, m i) f μ ↔ ∀ i, ae_measurable' (m i) f μ :=
begin
  split,
  { rintro ⟨g, hg, hfg⟩ i, exact ⟨g, hg.mono (infi_le m i) le_rfl, hfg⟩ },
  { intros h, choose g hg hfg using h,  }
end


open filter
variables {l : filter ι}

lemma filter.eventually_generate {g : set (set α)} {p : α → Prop} :
  (generate g).eventually p ↔ sorry :=
begin
  rw [filter.eventually, mem_generate_iff],
end

lemma ae_cover.ae_measurable {β : Type*} [has_zero β] [metric_space β] [measurable_space β]
  [borel_space β] [l.is_countably_generated] [l.ne_bot] {f : α → β} {φ : ι → set α}
  (hφ : ae_cover μ l φ) (hfm : ∀ i, ae_measurable f (μ.restrict $ φ i)) (i : ι) :
  ae_measurable f μ :=
begin
  simp_rw [← ae_measurable_discrete_outside_iff (hφ.measurable _)] at hfm,

end
