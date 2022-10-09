import probability.martingale.borel_cantelli
import probability.independence

open_locale measure_theory probability_theory ennreal big_operators topological_space

open measure_theory probability_theory measurable_space

namespace probability_theory

variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω} {s : ℕ → set Ω}

section pi_system

lemma Indep_set.indep_sets_pi_Union_Inter (hs : Indep_set s μ) (n : ℕ) :
  indep_sets {s n} (pi_Union_Inter (λ k : ℕ, {s k}) {T | T ≤ finset.range n}) μ :=
begin
  rintro a b ha ⟨I, hI, f, hf, rfl⟩,
  simp only [set.mem_singleton_iff] at hf,
  rw [set.mem_singleton_iff.1 ha, (set.Inter_congr (λ i, set.Inter_congr $ hf i) :
    (⋂ i ∈ I, f i) = ⋂ i ∈ I, s i), ← finset.set_bInter_insert, hs, finset.prod_insert, ← hs],
  { exact λ i hi, measurable_set_generate_from (set.mem_singleton _) },
  { exact λ hn, finset.not_mem_range_self (hI hn) },
  { exact λ i hi, measurable_set_generate_from (set.mem_singleton _) }
end

lemma generate_from_pi_Union_Inter_range_eq (n : ℕ) :
  generate_from (pi_Union_Inter (λ k : ℕ, {s k}) {T | T ≤ finset.range n}) =
  generate_from {t | ∃ k < n, s k = t} :=
begin
  refine le_antisymm (generate_from_le _) (generate_from_mono _),
  { rintro _ ⟨I, hI, f, hf, rfl⟩,
    exact finset.measurable_set_bInter _ (λ m hm,
      measurable_set_generate_from ⟨m, finset.mem_range.1 $ hI hm, (hf m hm).symm⟩) },
  { rintro _ ⟨k, hk, rfl⟩,
    exact ⟨{k}, λ m hm, (finset.mem_singleton.1 hm).symm ▸ finset.mem_range.2 hk, s,
      λ m hm, (finset.mem_singleton.1 hm).symm ▸ rfl, (finset.set_bInter_singleton k s).symm⟩ }
end

lemma Indep_set.indep_generate_from_lt [is_probability_measure μ]
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  indep (generate_from {s n}) (generate_from {t | ∃ k < n, s k = t}) μ :=
begin
  rw ← generate_from_pi_Union_Inter_range_eq n,
  refine indep_sets.indep' (λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm n)
    (λ t ht, generate_from_pi_Union_Inter_le _ _ _ _ (measurable_set_generate_from ht))
    (is_pi_system.singleton _) _ (hs.indep_sets_pi_Union_Inter _),
  { exact (λ k, generate_from_le $ λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm k) },
  { refine is_pi_system_pi_Union_Inter _ (λ k, is_pi_system.singleton _) _
      (λ a b ha hb, @finset.union_subset _ (λ x y, classical.prop_decidable (x = y)) _ _ _ ha hb) }
end

lemma Indep_set.indep_generate_from_le [is_probability_measure μ]
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  indep (generate_from {s (n + 1)}) (generate_from {t | ∃ k ≤ n, s k = t}) μ :=
begin
  convert hs.indep_generate_from_lt hsm (n + 1),
  simp_rw nat.lt_succ_iff
end

end pi_system

section borel_cantelli

def filtration_of_set {s : ℕ → set Ω} (hsm : ∀ n, measurable_set (s n)) : filtration ℕ m0 :=
{ seq := λ n, generate_from {t | ∃ k ≤ n, s k = t},
  mono' := λ n m hnm, generate_from_mono (λ t ⟨k, hk₁, hk₂⟩, ⟨k, hk₁.trans hnm, hk₂⟩),
  le' := λ n, generate_from_le (λ t ⟨k, hk₁, hk₂⟩, hk₂ ▸ hsm k) }

lemma measurable_set_filtration_of_set {s : ℕ → set Ω}
  (hsm : ∀ n, measurable_set[m0] (s n)) (n : ℕ) {k : ℕ} (hk : k ≤ n) :
  measurable_set[filtration_of_set hsm n] (s k) :=
measurable_set_generate_from ⟨k, hk, rfl⟩

lemma measurable_set_filtration_of_set' {s : ℕ → set Ω}
  (hsm : ∀ n, measurable_set[m0] (s n)) (n : ℕ) :
  measurable_set[filtration_of_set hsm n] (s n) :=
measurable_set_filtration_of_set hsm n le_rfl

variables [is_probability_measure μ]

lemma Indep_set.filt_indep
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  indep (generate_from {s (n + 1)}) (filtration_of_set hsm n) μ :=
hs.indep_generate_from_le hsm _

lemma Indep_set.condexp_indicator_filt_ae_eq
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  μ[(s (n + 1)).indicator (λ ω, 1 : Ω → ℝ) | filtration_of_set hsm n] =ᵐ[μ]
    λ ω, (μ (s (n + 1))).to_real :=
begin
  refine (condexp_indep_eq (generate_from_le
    (λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm _) : generate_from {s (n + 1)} ≤ m0)
    ((filtration_of_set hsm).le n)
    (strongly_measurable_one.indicator (measurable_set_generate_from (set.mem_singleton _)))
    (hs.indep_generate_from_le hsm n)).trans (ae_of_all μ (λ ω, _)),
  convert integral_indicator_const (1 : ℝ) (hsm (n + 1)),
  rw [smul_eq_mul, mul_one],
end

lemma Indep_set.condexp_indicator_filt_ae_eq'
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) :
  ∀ᵐ ω ∂μ, ∀ n, μ[(s (n + 1)).indicator (1 : Ω → ℝ) | filtration_of_set hsm n] ω =
    (μ (s (n + 1))).to_real :=
ae_all_iff.2 (hs.condexp_indicator_filt_ae_eq hsm)

open filter

section tsum

variables {α β : Type*} [add_comm_monoid α] [topological_space α] [t2_space α]

@[simp]
lemma tsum_univ (f : β → α) :
  ∑' x : (set.univ : set β), f x = ∑' x, f x :=
by simp [tsum_subtype]

@[simp]
lemma tsum_singleton (b : β) (f : β → α) :
  ∑' x : ({b} : set β), f x = f b :=
begin
  rw [tsum_subtype, tsum_eq_single b],
  { simp },
  { intros b' hb',
    rw set.indicator_of_not_mem,
    rwa set.mem_singleton_iff },
  { apply_instance }
end

lemma ennreal.tsum_le_of_sum_range_le {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
  (h : ∀ n, ∑ i in finset.range n, f i ≤ c) :
  ∑' n, f n ≤ c :=
le_of_tendsto' ((ennreal.has_sum_iff_tendsto_nat _).1 ennreal.summable.has_sum) h

lemma ennreal.tsum_add_one_eq_top {f : ℕ → ℝ≥0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 ≠ ∞) :
  ∑' n, f (n + 1) = ∞ :=
begin
  classical,
  suffices : f 0 + ∑' (n : ℕ), f (n + 1) = ⊤,
  { obtain h | h := ennreal.add_eq_top.1 this,
    { exact false.elim (hf0 h) },
    { assumption } },
  { rw [← tsum_univ, (_ : set.univ = {0} ∪ set.range nat.succ)] at hf,
    swap,
    { rw [eq_comm, set.eq_univ_iff_forall],
      rintro ⟨-, x⟩,
      { exact or.inl rfl },
      { exact or.inr ⟨x, rfl⟩ } },
    rw [← top_le_iff, ← hf],
    refine (ennreal.tsum_union_le _ _ _).trans _,
    rw [tsum_singleton, ennreal.add_le_add_iff_left hf0, tsum_subtype],
    refine ennreal.tsum_le_of_sum_range_le (λ n, _),
    cases n,
    { simp only [finset.range_zero, finset.sum_empty, zero_le'] },
    { refine le_trans _ (sum_le_tsum (finset.range n) (λ _ _, bot_le) ennreal.summable),
      set i : ℕ ↪ ℕ := ⟨(+1), nat.succ_injective⟩,
      rw [(_ : ∑ k in finset.range n, f (k + 1) = ∑ k in finset.range n, f (i k)),
        ← finset.sum_map (finset.range n) i f, finset.sum_indicator_eq_sum_filter],
      swap, { refl },
      refine le_of_eq (finset.sum_congr _ (λ _ _, rfl)),
      ext m,
      rw [finset.mem_filter, finset.mem_map],
      split,
      { rintro ⟨hk, k, rfl⟩,
        rw [finset.mem_range, nat.succ_lt_succ_iff] at hk,
        exact ⟨k, finset.mem_range.2 hk, rfl⟩ },
      { rintro ⟨k, hk, rfl⟩,
        exact ⟨finset.mem_range.2 $ nat.succ_lt_succ $ finset.mem_range.1 hk, k, rfl⟩ } } }
end

end tsum

/-- **The second Borel-Cantelli lemma**: Given a sequence of independent sets `(sₙ)` such that
`∑ n, μ sₙ = ∞`, `limsup sₙ` has measure 1. -/
lemma measure_limsup_eq_one
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (hs' : ∑' n, μ (s n) = ∞) :
  μ (limsup at_top s) = 1 :=
begin
  rw measure_congr (eventually_eq_set.2 (ae_mem_limsup_at_top_iff μ $
    measurable_set_filtration_of_set' hsm) :
      (limsup at_top s : set Ω) =ᵐ[μ] {ω | tendsto (λ n, ∑ k in finset.range n,
        μ[(s (k + 1)).indicator (1 : Ω → ℝ) | filtration_of_set hsm k] ω) at_top at_top}),
  suffices : {ω | tendsto (λ n, ∑ k in finset.range n,
    μ[(s (k + 1)).indicator (1 : Ω → ℝ) | filtration_of_set hsm k] ω) at_top at_top} =ᵐ[μ] set.univ,
  { rw [measure_congr this, measure_univ] },
  filter_upwards [hs.condexp_indicator_filt_ae_eq' hsm] with ω hω,
  refine eq_true_intro (_ : tendsto _ _ _),
  simp_rw hω,
  have htends : tendsto (λ n, ∑ k in finset.range n, μ (s (k + 1))) at_top (𝓝 ∞),
  { rw ← ennreal.tsum_add_one_eq_top hs' (measure_ne_top _ _),
    exact ennreal.tendsto_nat_tsum _ },
  rw ennreal.tendsto_nhds_top_iff_nnreal at htends,
  refine tendsto_at_top_at_top_of_monotone' _ _,
  { refine monotone_nat_of_le_succ (λ n, _),
    rw [← sub_nonneg, finset.sum_range_succ_sub_sum],
    exact ennreal.to_real_nonneg },
  { rintro ⟨B, hB⟩,
    refine not_eventually.2 _ (htends B.to_nnreal),
    refine frequently_of_forall (λ n, not_lt.2 _),
    rw mem_upper_bounds at hB,
    specialize hB (∑ (k : ℕ) in finset.range n, μ (s (k + 1))).to_real _,
    { refine ⟨n, _⟩,
      rw ennreal.to_real_sum,
      exact λ _ _, measure_ne_top _ _ },
    { rw ← ennreal.to_real_le_to_real (ennreal.sum_lt_top _).ne ennreal.coe_ne_top,
      { exact hB.trans (by simp) },
      { exact λ _ _, measure_ne_top _ _ } } }
end

end borel_cantelli

end probability_theory
