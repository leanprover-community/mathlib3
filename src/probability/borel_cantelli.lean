import probability.conditional_expectation
import probability.independence
import probability.stopping

open_locale measure_theory
open measure_theory probability_theory measurable_space

namespace probability_theory

variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω}

def filt (s : ℕ → set Ω) (hs : ∀ n, measurable_set (s n)) : filtration ℕ m0 :=
{ seq := λ n, generate_from {t | ∃ k ≤ n, s k = t},
  mono' := λ n m hnm, generate_from_mono (λ t ⟨k, hk₁, hk₂⟩, ⟨k, hk₁.trans hnm, hk₂⟩),
  le' := λ n, generate_from_le (λ t ⟨k, hk₁, hk₂⟩, hk₂ ▸ hs k) }

include m0

lemma filt_indep_sets {s : ℕ → set Ω} (hs : ∀ n, measurable_set (s n))
  (hsindep : Indep_set s μ) (n : ℕ) :
  indep_sets {s (n + 1)} {t | ∃ k ≤ n, s k = t} μ :=
begin
  rintros a b ha ⟨k, hk, rfl⟩,
  exact hsindep.indep_sets ((lt_of_le_of_lt hk n.lt_succ_self).ne.symm) _ _
    (measurable_set_generate_from ha) (measurable_set_generate_from $ set.mem_singleton _),
end

lemma indep_generate_from_singleton (μ : measure Ω . volume_tac)
  {s : set Ω} {m : measurable_space Ω}
  (h : @indep_sets Ω m0 {s} {t : set Ω | measurable_set[m] t} μ) :
  @indep Ω (generate_from {s}) m m0 μ :=
begin
  sorry
end

lemma filt_indep {s : ℕ → set Ω} (hs : ∀ n, measurable_set (s n))
  (hsindep : Indep_set s μ) (n : ℕ) :
  indep (generate_from {s (n + 1)}) (filt s hs n) μ :=
begin
  refine indep_generate_from_singleton _ (λ a t ha ht, _),
  have : filt s hs n = generate_from _ := rfl,
  sorry,
end


end probability_theory
