/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.convergence

/-!

# Generalized Borel-Cantelli lemma

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {α : Type*} {m0 : measurable_space α} {μ : measure α}

/-
for a (sub)martingale `f` with bounded difference,
`∀ᵐ x ∂μ, f n x converges ↔ (f n x) is bounded in n`
-/

noncomputable
def least_ge (f : ℕ → α → ℝ) (r : ℝ) (n : ℕ) := hitting f (set.Ici r) 0 n

variables {ℱ : filtration ℕ m0} {f : ℕ → α → ℝ} (r : ℝ) (n : ℕ)

lemma adapted.is_stopping_time_least_ge (hf : adapted ℱ f) :
  is_stopping_time ℱ (least_ge f r n) :=
hitting_is_stopping_time hf measurable_set_Ici

section move

lemma eventually_le.add_le_add {α β : Type*} [ordered_semiring β] {l : filter α}
  {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ + g₁ ≤ᶠ[l] f₂ + g₂ :=
by filter_upwards [hf, hg] with x hfx hgx using add_le_add hfx hgx

variables {u : ℕ → α → ℝ} {τ : α → ℕ}

lemma stopped_process_eq' (n : ℕ) :
  stopped_process u τ n =
  set.indicator {a | n + 1 ≤ τ a} (u n) +
    ∑ i in finset.range (n + 1), set.indicator {a | τ a = i} (u i) :=
begin
  have : {a | n ≤ τ a}.indicator (u n) =
    {a | n + 1 ≤ τ a}.indicator (u n) + {a | τ a = n}.indicator (u n),
  { ext x,
    rw [add_comm, pi.add_apply, ← set.indicator_union_of_not_mem_inter],
    { simp_rw [@eq_comm _ _ n, @le_iff_eq_or_lt _ _ n, nat.succ_le_iff],
      refl },
    { rintro ⟨h₁, h₂⟩,
      exact (nat.succ_le_iff.1 h₂).ne h₁.symm } },
  rw [stopped_process_eq, this, finset.sum_range_succ_comm, ← add_assoc],
end

end move

lemma submartingale.stopped_process_least_ge
  [is_finite_measure μ] (hf : submartingale f ℱ μ) :
  submartingale (stopped_process f (least_ge f r n)) ℱ μ :=
begin
  refine submartingale_nat (hf.adapted.stopped_process_of_nat
    (hf.adapted.is_stopping_time_least_ge r n))
    (integrable_stopped_process (hf.adapted.is_stopping_time_least_ge r n) hf.integrable)
    (λ i, _),
  have hst := hf.adapted.is_stopping_time_least_ge r n,
  have hsint : integrable (∑ i in finset.range (i + 1),
    {a | least_ge f r n a = i}.indicator (f i)) μ :=
    integrable_finset_sum' _ (λ j _, (hf.integrable j).indicator $
      ℱ.le _ _ ((hf.adapted.is_stopping_time_least_ge r n).measurable_set_eq j)),
  have hmeas : measurable_set[ℱ i] {a | i + 1 ≤ least_ge f r n a},
  { simp_rw [nat.succ_le_iff, ← not_le],
    exact (hst.measurable_set_le i).compl },
  rw [stopped_process_eq', stopped_process_eq],
  refine eventually_le.trans _ (condexp_add ((hf.integrable (i + 1)).indicator $
    (ℱ.le _ _ hmeas)) hsint).symm.le,
  have hmeas' : strongly_measurable[ℱ i]
    (∑ i in finset.range (i + 1), {a | least_ge f r n a = i}.indicator (f i)) :=
    finset.strongly_measurable_sum' _ (λ j hj,
      ((hf.strongly_measurable j).mono (ℱ.mono $ finset.mem_range_succ_iff.1 hj)).indicator $
      ℱ.mono (finset.mem_range_succ_iff.1 hj) _ (hst.measurable_set_eq j)),
  rw condexp_of_strongly_measurable (ℱ.le _) hmeas' hsint,
  exact eventually_le.add_le_add (eventually_le.trans (indicator_eventually_le_indicator $
    eventually.filter_mono inf_le_left (hf.2.1 i _ (i.le_succ)))
    (condexp_indicator (hf.integrable _) hmeas).symm.le) (eventually_le.refl _ _),
end

variables {R : ℝ≥0}

-- #check snorm_le_of_ae_bound

-- add something like not_mem_of_lt_hitting

lemma stopped_process_least_ge_le [is_finite_measure μ]
  (hbdd : ∀ i, snorm (f (i + 1) - f i) 1 μ ≤ R) (m : ℕ) (x : α) (hf0 : f 0 x = 0) :
  stopped_process f (least_ge f r n) m x ≤ n + R :=
begin
  rw least_ge,
  -- refine le_trans (stopped_value_hitting_mem _) _,
  -- have : f (least_ge f r n x) x ∈ set.Ici r, refine hitting_mem_set _,
  sorry
end

lemma stopped_process_least_ge_snorm_le [is_finite_measure μ]
  (hf0 : f 0 = 0) (hbdd : ∀ i, snorm (f (i + 1) - f i) 1 μ ≤ R) (m : ℕ) :
  snorm (stopped_process f (least_ge f r n) m) 1 μ ≤ 2 * μ set.univ * (n + R) :=
begin
  sorry,
end

lemma foo [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hfnonneg : 0 ≤ f) (hbdd : ∀ n, snorm (f (n + 1) - f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, bdd_above (set.range $ λ n, f n x) → ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  sorry
end

end measure_theory
