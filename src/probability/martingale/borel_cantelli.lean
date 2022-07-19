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
  {ℱ : filtration ℕ m0} {f : ℕ → α → ℝ}

/-
for a (sub)martingale `f` with bounded difference,
`∀ᵐ x ∂μ, f n x converges ↔ (f n x) is bounded in n`
-/

noncomputable
def least_ge (f : ℕ → α → ℝ) (r : ℝ) (n : ℕ) := hitting f (set.Ici r) 0 n

lemma adapted.is_stopping_time_least_ge (r : ℝ) (n : ℕ) (hf : adapted ℱ f) :
  is_stopping_time ℱ (least_ge f r n) :=
hitting_is_stopping_time hf measurable_set_Ici

section move

lemma eventually_le.add_le_add {α β : Type*} [ordered_semiring β] {l : filter α}
  {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ + g₁ ≤ᶠ[l] f₂ + g₂ :=
by filter_upwards [hf, hg] with x hfx hgx using add_le_add hfx hgx

variables {β : Type*}
variables {u : ℕ → α → β} {τ : α → ℕ}

lemma stopped_process_eq' [add_comm_monoid β] (n : ℕ) :
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

lemma not_mem_of_lt_hitting {ι : Type*}
  [conditionally_complete_linear_order ι] [is_well_order ι (<)]
  {u : ι → α → β} {s : set β} {x : α} {n m k : ι}
  (hk₁ : k < hitting u s n m x) (hk₂ : n ≤ k) :
  u k x ∉ s :=
begin
  classical,
  intro h,
  have hexists : ∃ j ∈ set.Icc n m, u j x ∈ s,
  refine ⟨k, ⟨hk₂, le_trans hk₁.le $ hitting_le _⟩, h⟩,
  refine not_le.2 hk₁ _,
  simp_rw [hitting, if_pos hexists],
  exact cInf_le bdd_below_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le $ hitting_le _⟩, h⟩,
end

end move

lemma stopped_value_least_ge_eq (i : ℕ) (r : ℝ) :
  stopped_value f (least_ge f r i) = stopped_process f (least_ge f r i) i :=
begin
  ext x,
  exact congr_arg2 _ (min_eq_right (hitting_le x : least_ge f r i x ≤ i)).symm rfl
end

-- lemma stopped_process_least_ge_succ

lemma submartingale.stopped_value_least_ge [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (r : ℝ) :
  submartingale (λ i, stopped_value f (least_ge f r i)) ℱ μ :=
begin
  -- have hst := hf.adapted.is_stopping_time_least_ge r n,
  refine submartingale_nat (λ N, strongly_measurable_stopped_value_of_le
      hf.adapted.prog_measurable_of_nat
      (hf.adapted.is_stopping_time_least_ge _ _) (λ x, hitting_le _))
    (λ i, integrable_stopped_value (hf.adapted.is_stopping_time_least_ge _ _)
      hf.integrable (λ x, hitting_le _)) (λ i, _),
  have hsint : integrable (∑ j in finset.range (i + 1),
    {a | least_ge f r (i + 1) a = j}.indicator (f j)) μ := sorry,
    -- integrable_finset_sum' _ (λ j _, (hf.integrable j).indicator $
    --   ℱ.le _ _ ((hf.adapted.is_stopping_time_least_ge r j).measurable_set_eq j)),
  have hmeas : measurable_set[ℱ i] {a | i + 1 ≤ least_ge f r (i + 1) a}, sorry,
  -- { simp_rw [nat.succ_le_iff, ← not_le],
  --   exact (hst.measurable_set_le i).compl },
  have hmeas' : strongly_measurable[ℱ i]
    (∑ j in finset.range (i + 1), {a | least_ge f r (i + 1) a = j}.indicator (f j)) := sorry,
  --   finset.strongly_measurable_sum' _ (λ j hj,
  --     ((hf.strongly_measurable j).mono (ℱ.mono $ finset.mem_range_succ_iff.1 hj)).indicator $
  --     ℱ.mono (finset.mem_range_succ_iff.1 hj) _ (hst.measurable_set_eq j)),
  simp_rw [stopped_value_least_ge_eq],
  rw [stopped_process_eq, stopped_process_eq],
  refine eventually_le.trans _ (condexp_add ((hf.integrable (i + 1)).indicator $
    ℱ.le _ _ hmeas) hsint).symm.le,
  rw condexp_of_strongly_measurable (ℱ.le _) hmeas' hsint,
  refine eventually_le.add_le_add _ (eventually_eq.le $ eventually_of_forall $ λ x, _),
  { sorry },
  { rw [finset.sum_apply, finset.sum_apply],
    refine finset.sum_congr rfl (λ j hj, _),
    congr,
    ext y,
    simp_rw [least_ge],
    refine ⟨λ h, _, λ h, _⟩,
    { rw [← h, eq_comm],
      refine hitting_eq_hitting_of_exists (zero_le _) i.le_succ _,
      obtain ⟨j, hj⟩ := (hitting_lt_iff _ _).1 (lt_of_le_of_lt h.le (finset.mem_range.1 hj)),
      -- refine hitting_mem_set _,
    },

  }
  -- (eventually_le.trans (indicator_eventually_le_indicator $
  --   eventually.filter_mono inf_le_left (hf.2.1 i _ (i.le_succ)))
  --   (condexp_indicator (hf.integrable _) hmeas).symm.le) (eventually_le.refl _ _),
end

variables {r : ℝ} {R : ℝ≥0}

-- #check snorm_le_of_ae_bound

lemma norm_stopped_process_least_ge_le [is_finite_measure μ]
  {r : ℝ} (hr : 0 ≤ r) (hf : 0 ≤ f) (hbdd : ∀ᵐ x ∂μ, ∀ i, f (i + 1) x - f i x ≤ R) (n m : ℕ) :
  ∀ᵐ x ∂μ, ∥stopped_process f (least_ge f r n) m x∥ ≤ r + R + f 0 x :=
begin
  filter_upwards [hbdd] with x hbddx,
  change ∥f (min m $ least_ge f r n x) x∥ ≤ r + R + f 0 x,
  rw [real.norm_eq_abs, abs_of_nonneg (hf (min m $ least_ge f r n x) x)],
  by_cases hlt : m < least_ge f r n x,
  { rw [min_eq_left hlt.le, add_assoc],
    refine (not_le.1 $ not_mem_of_lt_hitting hlt $ zero_le _).le.trans
      (le_add_of_nonneg_right $ add_nonneg R.coe_nonneg (hf 0 x)) },
  { rw min_eq_right (not_lt.1 hlt),
    by_cases heq : least_ge f r n x = 0,
    { exact heq ▸ le_add_of_nonneg_left (add_nonneg hr R.coe_nonneg) },
    { obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero heq,
      exact hk.symm ▸ (sub_le_iff_le_add.1 $ hbddx k).trans
        ((add_le_add_left (not_le.1 $ not_mem_of_lt_hitting
          (hk.symm ▸ k.lt_succ_self : k < least_ge f r n x) (zero_le _)).le _).trans
          (add_comm ↑R r ▸ le_add_of_nonneg_right (hf 0 x))) } }
end

lemma stopped_process_least_ge_snorm_le [is_finite_measure μ]
  {r : ℝ} (hr : 0 ≤ r) (hf : 0 ≤ f) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ x ∂μ, ∀ i, f (i + 1) x - f i x ≤ R) (n m : ℕ) :
  snorm (stopped_process f (least_ge f r n) m) 1 μ ≤ μ set.univ * ennreal.of_real (r + R) :=
begin
  have hbound := norm_stopped_process_least_ge_le hr hf hbdd n m,
  simp only [hf0, pi.zero_apply, add_zero] at hbound,
  refine le_trans (snorm_le_of_ae_bound hbound) _,
  rw [ennreal.one_to_real, inv_one, ennreal.rpow_one],
  exact le_rfl,
end

lemma foo [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hlef : 0 ≤ f) (hf0 : f 0 = 0)
  (hbdd : ∀ n, snorm (f (n + 1) - f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, bdd_above (set.range $ λ n, f n x) → ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  suffices : ∀ᵐ x ∂μ, bdd_above (set.range $ λ n, f n x) →
    ∃ N : ℕ, f = λ n, stopped_process f (least_ge f N n) n,
  { filter_upwards [this] with x hx hbound,
    obtain ⟨N, hN⟩ := hx hbound,
    rw [hN],
    simp,
    -- refine submartingale.exists_ae_trim_tendsto_of_bdd _ _,

   },
  -- have := hf.stopped_process_least_ge,
  sorry
end

end measure_theory
