import analysis.asymptotics.asymptotics
import analysis.normed.group.basic
import analysis.complex.basic
import order.filter.basic
import data.nat.basic

open filter finset asymptotics
open_locale nat topological_space big_operators

variables {f g : ℕ → ℝ} {z : ℕ → ℂ}
variables {x : ℝ}

-- The partial sum of `g` starting from 0.
local notation `G` n:80 := ∑ i in range n, g i
local notation `Z` n:80 := ∑ i in range n, z i

/-- The product of a sequence that tends to zero with a bounded sequence also tends to zero. -/
lemma tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type*} [normed_field 𝕜]
  [normed_group 𝔸] [normed_space 𝕜 𝔸] {l : filter ι} {ε : ι → 𝕜} {f : ι → 𝔸}
  (hε : tendsto ε l (𝓝 0)) (hf : filter.is_bounded_under (≤) l (norm ∘ f)) :
  tendsto (ε • f) l (𝓝 0) :=
begin
  rw ← is_o_one_iff 𝕜 at hε ⊢,
  simpa using is_o.smul_is_O hε (hf.is_O_const (one_ne_zero : (1 : 𝕜) ≠ 0))
end

private lemma cauchy_seq.real_const_mul (hf : cauchy_seq f) : cauchy_seq (λ n, x * f n) :=
uniform_continuous.comp_cauchy_seq real.uniform_continuous_mul_const hf

/-- The **direct comparison test** for conditionally convergent series.
See `cauchy_seq_finset_of_norm_bounded` for the same statement about absolutely convergent ones. -/
lemma cauchy_seq_range_of_norm_bounded
  (hf : cauchy_seq (λ n, ∑ i in range n, f i)) (hz : ∀ i, ∥z i∥ ≤ f i) :
  cauchy_seq (λ n, ∑ i in range n, z i) :=
begin
  rw metric.cauchy_seq_iff' at ⊢ hf,

  intros ε hε,
  cases hf ε hε with N hf,
  use N,
  intros n hn,
  specialize hf n hn,

  rw [dist_eq_norm, ←sum_Ico_eq_sub _ hn] at ⊢ hf,
  apply lt_of_le_of_lt (norm_sum_le _ _),
  apply lt_of_le_of_lt _ hf,

  have : ∀ n, 0 ≤ f n := λ n, le_trans (norm_nonneg (z n)) (hz n),
  rw [real.norm_eq_abs, abs_sum_of_nonneg' this],
  exact sum_le_sum (λ x _, hz x),
end

/-- **Dirichlet's Test** for monotone sequences. -/
theorem dirichlet_test_mono
  (hfa : monotone f) (hf0 : tendsto f at_top (𝓝 0)) (hgx : ∀ n, ∥Z n∥ ≤ x) :
  cauchy_seq (λ n, ∑ i in range (n+1), ↑(f i) * z i) :=
begin
  simp_rw [sum_by_parts_range _ _ (nat.succ_pos _), sub_eq_add_neg,
           nat.succ_sub_succ_eq_sub, tsub_zero],

  have := tendsto.cauchy_seq (tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
    ⟨x, eventually_map.mpr (eventually_of_forall (λ n, hgx (n+1)))⟩),
  apply cauchy_seq.add this,

  have : ∀ n, ∥Z (n+1) * (f(n+1) - f(n))∥ ≤ x * |f(n+1) - f(n)| := λ n, begin
    rw normed_field.norm_mul,
    norm_cast,
    rw real.norm_eq_abs,
    exact decidable.mul_le_mul_of_nonneg_right (hgx (n+1)) (abs_nonneg _),
  end,
  apply cauchy_seq.neg (cauchy_seq_range_of_norm_bounded _ this),

  conv in (|_|) { rw abs_of_nonneg (sub_nonneg_of_le (hfa (nat.le_succ _))) },
  simp_rw ←mul_sum,
  apply cauchy_seq.real_const_mul,
  simp_rw [sum_range_sub, sub_eq_add_neg],
  exact cauchy_seq.add_const (tendsto.cauchy_seq hf0),
end

/-- **Dirichlet's test** for antitone sequences. -/
theorem dirichlet_test_anti
  (hfa : antitone f) (hf0 : tendsto f at_top (𝓝 0)) (hzx : ∀ n, ∥Z n∥ ≤ x) :
  cauchy_seq (λ n, ∑ i in range (n+1), ↑(f i) * z i) :=
begin
  have hfa': monotone (λ x, -f x) := λ _ _ hab, neg_le_neg $ hfa hab,
  have hf0': tendsto (λ x, -f x) at_top (𝓝 (-0)) := filter.tendsto.neg hf0,
  have : ∀ i, ↑(f i) * z i = -(↑(-f i) * z i) := λ _, by simp,
  simp_rw [this, sum_neg_distrib],
  rw neg_zero at hf0',
  exact cauchy_seq.neg (dirichlet_test_mono hfa' hf0' hzx),
end

private lemma norm_sum_neg_one_pow_le (n : ℕ) : ∥∑ i in range n, (-1 : ℂ) ^ i∥ ≤ 1 :=
begin
  rw [←geom_sum_def, neg_one_geom_sum],
  split_ifs;
  norm_num,
end

/-- The **alternating series test** for monotone sequences. -/
theorem alternating_series_test_mono (hfa : monotone f) (hf0 : tendsto f at_top (𝓝 0)) :
  cauchy_seq (λ n, ∑ i in range (n+1), ↑(f i) * (-1 : ℂ)^i) :=
dirichlet_test_mono hfa hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for antitone sequences. -/
theorem alternating_series_test_anti (hfa : antitone f) (hf0 : tendsto f at_top (𝓝 0)) :
  cauchy_seq (λ n, ∑ i in range (n+1), ↑(f i) * (-1 : ℂ)^i) :=
dirichlet_test_anti hfa hf0 norm_sum_neg_one_pow_le
