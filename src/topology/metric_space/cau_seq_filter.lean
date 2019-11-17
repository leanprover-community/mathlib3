/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Sébastien Gouëzel
Characterize completeness of metric spaces in terms of Cauchy sequences.
In particular, reconcile the filter notion of Cauchy-ness with the cau_seq notion on normed spaces.
-/

import topology.uniform_space.basic analysis.normed_space.basic data.real.cau_seq analysis.specific_limits
import tactic.linarith

universes u v
open set filter classical emetric
open_locale topological_space

variable {β : Type v}

/- We show that a metric space in which all Cauchy sequences converge is complete, i.e., all
Cauchy filters converge. For this, we approximate any Cauchy filter by a Cauchy sequence,
taking advantage of the fact that there is a sequence tending to `0` in ℝ. The proof also gives
a more precise result, that to get completeness it is enough to have the convergence
of all sequence that are Cauchy in a fixed quantitative sense, for instance satisfying
`dist (u n) (u m) < 2^{- min m n}`. The classical argument to obtain this criterion is to start
from a Cauchy sequence, extract a subsequence that satisfies this property, deduce the convergence
of the subsequence, and then the convergence of the original sequence. All this argument is
completely bypassed by the following proof, which avoids any use of subsequences and is written
partly in terms of filters. -/

namespace ennreal

/-In this paragraph, we prove useful properties of the sequence `half_pow n := 2^{-n}` in ennreal.
Some of them are instrumental in this file to get Cauchy sequences, but others are proved
here only for use in further applications of the completeness criterion
`emetric.complete_of_convergent_controlled_sequences` below. -/

/-- An auxiliary positive sequence that tends to `0` in `ennreal`, with good behavior. -/
noncomputable def half_pow (n : ℕ) : ennreal := ennreal.of_real ((1 / 2) ^ n)

lemma half_pow_pos (n : ℕ) : 0 < half_pow n :=
begin
  have : (0 : real) < (1/2)^n := pow_pos (by norm_num) _,
  simpa [half_pow] using this
end

lemma half_pow_tendsto_zero : tendsto (λn, half_pow n) at_top (𝓝 0) :=
begin
  unfold half_pow,
  rw ← ennreal.of_real_zero,
  apply ennreal.tendsto_of_real,
  exact tendsto_pow_at_top_nhds_0_of_lt_1 (by norm_num) (by norm_num)
end

lemma half_pow_add_succ (n : ℕ) : half_pow (n+1) + half_pow (n+1) = half_pow n :=
begin
  have : (0 : real) ≤ (1/2)^(n+1) := (le_of_lt (pow_pos (by norm_num) _)),
  simp only [half_pow, eq.symm (ennreal.of_real_add this this)],
  apply congr_arg,
  simp only [pow_add, one_div_eq_inv, pow_one],
  ring,
end

lemma half_pow_mono (m k : ℕ) (h : m ≤ k) : half_pow k ≤ half_pow m :=
ennreal.of_real_le_of_real (pow_le_pow_of_le_one (by norm_num) (by norm_num) h)

lemma edist_le_two_mul_half_pow [emetric_space β] {k l N : ℕ} (hk : N ≤ k) (hl : N ≤ l)
  {u : ℕ → β} (h : ∀n, edist (u n) (u (n+1)) ≤ half_pow n) :
  edist (u k) (u l) ≤ 2 * half_pow N :=
begin
  have ineq_rec : ∀m, ∀k≥m, half_pow k + edist (u m) (u (k+1)) ≤ 2 * half_pow m,
  { assume m,
    refine nat.le_induction _ (λk km hk, _),
    { calc half_pow m + edist (u m) (u (m+1)) ≤ half_pow m + half_pow m : add_le_add_left' (h m)
      ... = 2 * half_pow m : by simp [(mul_two _).symm, mul_comm] },
    { calc half_pow (k + 1) + edist (u m) (u (k + 1 + 1))
      ≤ half_pow (k+1) + (edist (u m) (u (k+1)) + edist (u (k+1)) (u (k+2))) :
        add_le_add_left' (edist_triangle _ _ _)
      ... ≤ half_pow (k+1) + (edist (u m) (u (k+1)) + half_pow (k+1)) :
        add_le_add_left' (add_le_add_left' (h (k+1)))
      ... = (half_pow(k+1) + half_pow(k+1)) + edist (u m) (u (k+1)) : by simp [add_comm]
      ... = half_pow k + edist (u m) (u (k+1)) : by rw half_pow_add_succ
      ... ≤ 2 * half_pow m : hk }},
  have Imk : ∀m, ∀k≥m, edist (u m) (u k) ≤ 2 * half_pow m,
  { assume m k hk,
    by_cases h : m = k,
    { simp [h, le_of_lt (half_pow_pos k)] },
    { have I : m < k := lt_of_le_of_ne hk h,
      have : 0 < k := lt_of_le_of_lt (nat.zero_le _) ‹m < k›,
      let l := nat.pred k,
      have : k = l+1 := (nat.succ_pred_eq_of_pos ‹0 < k›).symm,
      rw this,
      have : m ≤ l := begin rw this at I, apply nat.le_of_lt_succ I end,
      calc edist (u m) (u (l+1)) ≤ half_pow l + edist (u m) (u (l+1)) : le_add_left (le_refl _)
        ... ≤ 2 * half_pow m : ineq_rec m l ‹m ≤ l› }},
  by_cases h : k ≤ l,
  { calc edist (u k) (u l) ≤ 2 * half_pow k : Imk k l h
      ... ≤ 2 * half_pow N :
        canonically_ordered_semiring.mul_le_mul (le_refl _) (half_pow_mono N k hk) },
  { simp at h,
    calc edist (u k) (u l) = edist (u l) (u k) : edist_comm _ _
      ... ≤ 2 * half_pow l : Imk l k (le_of_lt h)
      ... ≤ 2 * half_pow N :
        canonically_ordered_semiring.mul_le_mul (le_refl _) (half_pow_mono N l hl) }
end

lemma cauchy_seq_of_edist_le_half_pow [emetric_space β]
  {u : ℕ → β} (h : ∀n, edist (u n) (u (n+1)) ≤ half_pow n) : cauchy_seq u :=
begin
  refine emetric.cauchy_seq_iff_le_tendsto_0.2 ⟨λn:ℕ, 2 * half_pow n, ⟨_, _⟩⟩,
  { exact λk l N hk hl, edist_le_two_mul_half_pow hk hl h },
  { have : tendsto (λn, 2 * half_pow n) at_top (𝓝 (2 * 0)) :=
      ennreal.tendsto_mul_right half_pow_tendsto_zero (by simp),
    simpa using this }
end

end ennreal

namespace sequentially_complete

section
/- We fix a cauchy filter `f`, and a bounding sequence `B` made of positive numbers. We will
prove that, if all sequences satisfying `dist (u n) (u m) < B (min n m)` converge, then
the cauchy filter `f` is converging. The idea is to construct from `f` a Cauchy sequence
that satisfies this property, therefore converges, and then to deduce the convergence of
`f` from this.
We give the argument in the more general setting of emetric spaces, and specialize it to
metric spaces at the end.
-/
variables [emetric_space β] {f : filter β} (hf : cauchy f) (B : ℕ → ennreal) (hB : ∀n, 0 < B n)
open ennreal

/--Auxiliary sequence, which is bounded by `B`, positive, and tends to `0`.-/
noncomputable def B2 (B : ℕ → ennreal) (n : ℕ) :=
  (half_pow n) ⊓ (B n)

lemma B2_pos (hB : ∀n, 0 < B n) (n : ℕ) : 0 < B2 B n :=
by unfold B2; simp [half_pow_pos n, hB n]

lemma B2_lim : tendsto (λn, B2 B n) at_top (𝓝 0) :=
begin
  have : ∀n, B2 B n ≤ half_pow n := λn, lattice.inf_le_left,
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds half_pow_tendsto_zero
    (by simp) (by simp [this])
end

/-- Define a decreasing sequence of sets in the filter `f`, of diameter bounded by `B2 n`. -/
def set_seq_of_cau_filter : ℕ → set β
| 0 := some ((emetric.cauchy_iff.1 hf).2 _ (B2_pos B hB 0))
| (n+1) := (set_seq_of_cau_filter n) ∩ some ((emetric.cauchy_iff.1 hf).2 _ (B2_pos B hB (n + 1)))

/-- These sets are in the filter. -/
lemma set_seq_of_cau_filter_mem_sets : ∀ n, set_seq_of_cau_filter hf B hB n ∈ f
| 0 := some (some_spec ((emetric.cauchy_iff.1 hf).2 _ (B2_pos B hB 0)))
| (n+1) := inter_mem_sets (set_seq_of_cau_filter_mem_sets n)
             (some (some_spec ((emetric.cauchy_iff.1 hf).2 _ (B2_pos B hB (n + 1)))))

/-- These sets are nonempty. -/
lemma set_seq_of_cau_filter_inhabited (n : ℕ) : ∃ x, x ∈ set_seq_of_cau_filter hf B hB n :=
inhabited_of_mem_sets (emetric.cauchy_iff.1 hf).1 (set_seq_of_cau_filter_mem_sets hf B hB n)

/-- By construction, their diameter is controlled by `B2 n`. -/
lemma set_seq_of_cau_filter_spec : ∀ n, ∀ {x y},
  x ∈ set_seq_of_cau_filter hf B hB n → y ∈ set_seq_of_cau_filter hf B hB n → edist x y < B2 B n
| 0 := some_spec (some_spec ((emetric.cauchy_iff.1 hf).2 _ (B2_pos B hB 0)))
| (n+1) := λ x y hx hy,
  some_spec (some_spec ((emetric.cauchy_iff.1 hf).2 _ (B2_pos B hB (n+1)))) x y
    (mem_of_mem_inter_right hx) (mem_of_mem_inter_right hy)

-- this must exist somewhere, no?
private lemma mono_of_mono_succ_aux {α} [partial_order α] (f : ℕ → α) (h : ∀ n, f (n+1) ≤ f n) (m : ℕ) :
  ∀ n, f (m + n) ≤ f m
| 0 := le_refl _
| (k+1) := le_trans (h _) (mono_of_mono_succ_aux _)

lemma mono_of_mono_succ {α} [partial_order α] (f : ℕ → α) (h : ∀ n, f (n+1) ≤ f n) {m n : ℕ}
  (hmn : m ≤ n) : f n ≤ f m :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_le hmn in
by simpa [hk] using mono_of_mono_succ_aux f h m k

lemma set_seq_of_cau_filter_monotone' (n : ℕ) :
  set_seq_of_cau_filter hf B hB (n+1) ⊆ set_seq_of_cau_filter hf B hB n :=
inter_subset_left _ _

/-- These sets are nested. -/
lemma set_seq_of_cau_filter_monotone {n k : ℕ} (hle : n ≤ k) :
  set_seq_of_cau_filter hf B hB k ⊆ set_seq_of_cau_filter hf B hB n :=
mono_of_mono_succ (set_seq_of_cau_filter hf B hB) (set_seq_of_cau_filter_monotone' hf B hB) hle

/-- Define the approximating Cauchy sequence for the Cauchy filter `f`,
obtained by taking a point in each set. -/
noncomputable def seq_of_cau_filter (n : ℕ) : β :=
some (set_seq_of_cau_filter_inhabited hf B hB n)

/-- The approximating sequence indeed belong to our good sets. -/
lemma seq_of_cau_filter_mem_set_seq (n : ℕ) : seq_of_cau_filter hf B hB n ∈ set_seq_of_cau_filter hf B hB n :=
some_spec (set_seq_of_cau_filter_inhabited hf B hB n)

/-- The distance between points in the sequence is bounded by `B2 N`. -/
lemma seq_of_cau_filter_bound {N n k : ℕ} (hn : N ≤ n) (hk : N ≤ k) :
  edist (seq_of_cau_filter hf B hB n) (seq_of_cau_filter hf B hB k) < B2 B N :=
set_seq_of_cau_filter_spec hf B hB N
  (set_seq_of_cau_filter_monotone hf B hB hn (seq_of_cau_filter_mem_set_seq hf B hB n))
  (set_seq_of_cau_filter_monotone hf B hB hk (seq_of_cau_filter_mem_set_seq hf B hB k))

/-- The approximating sequence is indeed Cauchy as `B2 n` tends to `0` with `n`. -/
lemma seq_of_cau_filter_is_cauchy :
  cauchy_seq (seq_of_cau_filter hf B hB) :=
emetric.cauchy_seq_iff_le_tendsto_0.2 ⟨B2 B,
  λ n m N hn hm, le_of_lt (seq_of_cau_filter_bound hf B hB hn hm), B2_lim B⟩

/-- If the approximating Cauchy sequence is converging, to a limit `y`, then the
original Cauchy filter `f` is also converging, to the same limit.
Given `t1` in the filter `f` and `t2` a neighborhood of `y`, it suffices to show that `t1 ∩ t2` is
nonempty.
Pick `ε` so that the ε-eball around `y` is contained in `t2`.
Pick `n` with `B2 n < ε/2`, and `n2` such that `dist(seq n2, y) < ε/2`. Let `N = max(n, n2)`.
We defined `seq` by looking at a decreasing sequence of sets of `f` with shrinking radius.
The Nth one has radius `< B2 N < ε/2`. This set is in `f`, so we can find an element `x` that's
also in `t1`.
`dist(x, seq N) < ε/2` since `seq N` is in this set, and `dist (seq N, y) < ε/2`,
so `x` is in the ε-ball around `y`, and thus in `t2`. -/
lemma le_nhds_cau_filter_lim {y : β} (H : tendsto (seq_of_cau_filter hf B hB) at_top (𝓝 y)) :
  f ≤ 𝓝 y :=
begin
  refine (le_nhds_iff_adhp_of_cauchy hf).2 _,
  refine forall_sets_neq_empty_iff_neq_bot.1 (λs hs, _),
  rcases filter.mem_inf_sets.2 hs with ⟨t1, ht1, t2, ht2, ht1t2⟩,
  rcases emetric.mem_nhds_iff.1 ht2 with ⟨ε, hε, ht2'⟩,
  cases emetric.cauchy_iff.1 hf with hfb _,
  have : ε / 2 > 0 := ennreal.half_pos hε,
  rcases inhabited_of_mem_sets (by simp) ((tendsto_orderable.1 (B2_lim B)).2 _ this)
    with ⟨n, hnε⟩,
  simp only [set.mem_set_of_eq] at hnε, -- hnε : ε / 2 > B2 B hB n
  cases (emetric.tendsto_at_top _).1 H _ this with n2 hn2,
  let N := max n n2,
  have ht1sn : t1 ∩ set_seq_of_cau_filter hf B hB N ∈ f,
    from inter_mem_sets ht1 (set_seq_of_cau_filter_mem_sets hf B hB _),
  have hts1n_ne : t1 ∩ set_seq_of_cau_filter hf B hB N ≠ ∅,
    from forall_sets_neq_empty_iff_neq_bot.2 hfb _ ht1sn,
  cases exists_mem_of_ne_empty hts1n_ne with x hx,
  -- x : β,  hx : x ∈ t1 ∩ set_seq_of_cau_filter hf B hB N
  -- we still have to show that x ∈ t2, i.e., edist x y < ε
  have I1 : seq_of_cau_filter hf B hB N ∈ set_seq_of_cau_filter hf B hB n :=
    (set_seq_of_cau_filter_monotone hf B hB (le_max_left n n2)) (seq_of_cau_filter_mem_set_seq hf B hB N),
  have I2 : x ∈ set_seq_of_cau_filter hf B hB n :=
    (set_seq_of_cau_filter_monotone hf B hB (le_max_left n n2)) hx.2,
  have hdist1 : edist x (seq_of_cau_filter hf B hB N) < B2 B n :=
    set_seq_of_cau_filter_spec hf B hB _ I2 I1,
  have hdist2 : edist (seq_of_cau_filter hf B hB N) y < ε / 2 :=
    hn2 N (le_max_right _ _),
  have hdist : edist x y < ε := calc
    edist x y ≤ edist x (seq_of_cau_filter hf B hB N) + edist (seq_of_cau_filter hf B hB N) y : edist_triangle _ _ _
          ... < B2 B n + ε/2 : ennreal.add_lt_add hdist1 hdist2
          ... ≤ ε/2 + ε/2 : add_le_add_right' (le_of_lt hnε)
          ... = ε : ennreal.add_halves _,
  have hxt2 : x ∈ t2, from ht2' hdist,
  exact ne_empty_iff_exists_mem.2 ⟨x, ht1t2 (mem_inter hx.left hxt2)⟩
end

end
end sequentially_complete

/-- An emetric space in which every Cauchy sequence converges is complete. -/
theorem complete_of_cauchy_seq_tendsto {α : Type u} [emetric_space α]
  (H : ∀u : ℕ → α, cauchy_seq u → ∃x, tendsto u at_top (𝓝 x)) :
  complete_space α :=
⟨begin
  -- Consider a Cauchy filter `f`
  intros f hf,
  -- Introduce a sequence `u` approximating the filter `f`. We don't need the bound `B`,
  -- so take for instance `B n = 1` for all `n`.
  let u := sequentially_complete.seq_of_cau_filter hf (λn, 1) (λn, ennreal.zero_lt_one),
  -- It is Cauchy.
  have : cauchy_seq u := sequentially_complete.seq_of_cau_filter_is_cauchy hf (λn, 1) (λn, ennreal.zero_lt_one),
  -- Therefore, it converges by assumption. Let `x` be its limit.
  rcases H u this with ⟨x, hx⟩,
  -- The original filter also converges to `x`.
  exact ⟨x, sequentially_complete.le_nhds_cau_filter_lim hf (λn, 1) (λn, ennreal.zero_lt_one) hx⟩
end⟩

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem emetric.complete_of_convergent_controlled_sequences {α : Type u} [emetric_space α]
  (B : ℕ → ennreal) (hB : ∀n, 0 < B n)
  (H : ∀u : ℕ → α, (∀N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) → ∃x, tendsto u at_top (𝓝 x)) :
  complete_space α :=
⟨begin
  -- Consider a Cauchy filter `f`.
  intros f hf,
  -- Introduce a sequence `u` approximating the filter `f`.
  let u := sequentially_complete.seq_of_cau_filter hf B hB,
  -- It satisfies the required bound.
  have : ∀N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N := λN n m hn hm, calc
    edist (u n) (u m) < sequentially_complete.B2 B N :
      sequentially_complete.seq_of_cau_filter_bound hf B hB hn hm
    ... ≤ B N : lattice.inf_le_right,
  -- Therefore, it converges by assumption. Let `x` be its limit.
  rcases H u this with ⟨x, hx⟩,
  -- The original filter also converges to `x`.
  exact ⟨x, sequentially_complete.le_nhds_cau_filter_lim hf B hB hx⟩
end⟩

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem metric.complete_of_convergent_controlled_sequences {α : Type u} [metric_space α]
  (B : ℕ → real) (hB : ∀n, 0 < B n)
  (H : ∀u : ℕ → α, (∀N n m : ℕ, N ≤ n → N ≤ m → dist (u n) (u m) < B N) → ∃x, tendsto u at_top (𝓝 x)) :
  complete_space α :=
begin
  -- this follows from the same criterion in emetric spaces. We just need to translate
  -- the convergence assumption from `dist` to `edist`
  apply emetric.complete_of_convergent_controlled_sequences (λn, ennreal.of_real (B n)),
  { simp [hB] },
  { assume u Hu,
    apply H,
    assume N n m hn hm,
    have Z := Hu N n m hn hm,
    rw [edist_dist, ennreal.of_real_lt_of_real_iff] at Z,
    exact Z,
    exact hB N }
end

section

/- Now, we will apply these results to `cau_seq`, i.e., "Cauchy sequences" defined by a
multiplicative absolute value on normed fields. -/

lemma tendsto_limit [normed_ring β] [hn : is_absolute_value (norm : β → ℝ)]
  (f : cau_seq β norm) [cau_seq.is_complete β norm] :
  tendsto f at_top (𝓝 f.lim) :=
_root_.tendsto_nhds.mpr
begin
  intros s os lfs,
  suffices : ∃ (a : ℕ), ∀ (b : ℕ), b ≥ a → f b ∈ s, by simpa using this,
  rcases metric.is_open_iff.1 os _ lfs with ⟨ε, ⟨hε, hεs⟩⟩,
  cases setoid.symm (cau_seq.equiv_lim f) _ hε with N hN,
  existsi N,
  intros b hb,
  apply hεs,
  dsimp [metric.ball], rw [dist_comm, dist_eq_norm],
  solve_by_elim
end

variables [normed_field β]

/-
 This section shows that if we have a uniform space generated by an absolute value, topological
 completeness and Cauchy sequence completeness coincide. The problem is that there isn't
 a good notion of "uniform space generated by an absolute value", so right now this is
 specific to norm. Furthermore, norm only instantiates is_absolute_value on normed_field.
 This needs to be fixed, since it prevents showing that ℤ_[hp] is complete
-/

instance normed_field.is_absolute_value : is_absolute_value (norm : β → ℝ) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := norm_eq_zero,
  abv_add := norm_triangle,
  abv_mul := normed_field.norm_mul }

open metric

lemma cauchy_of_filter_cauchy (f : ℕ → β) (hf : cauchy_seq f) :
  is_cau_seq norm f :=
begin
  cases cauchy_iff.1 hf with hf1 hf2,
  intros ε hε,
  rcases hf2 {x | dist x.1 x.2 < ε} (dist_mem_uniformity hε) with ⟨t, ⟨ht, htsub⟩⟩,
  simp at ht, cases ht with N hN,
  existsi N,
  intros j hj,
  rw ←dist_eq_norm,
  apply @htsub (f j, f N),
  apply set.mk_mem_prod; solve_by_elim [le_refl]
end

lemma filter_cauchy_of_cauchy (f : cau_seq β norm) : cauchy_seq f :=
begin
  apply cauchy_iff.2,
  split,
  { exact map_ne_bot at_top_ne_bot },
  { intros s hs,
    rcases mem_uniformity_dist.1 hs with ⟨ε, ⟨hε, hεs⟩⟩,
    cases cau_seq.cauchy₂ f hε with N hN,
    existsi {n | n ≥ N}.image f,
    simp, split,
    { existsi N, intros b hb, existsi b, simp [hb] },
    { rintros ⟨a, b⟩ ⟨⟨a', ⟨ha'1, ha'2⟩⟩, ⟨b', ⟨hb'1, hb'2⟩⟩⟩,
      dsimp at ha'1 ha'2 hb'1 hb'2,
      rw [←ha'2, ←hb'2],
      apply hεs,
      rw dist_eq_norm,
      apply hN; assumption }},
end

/-- In a normed field, `cau_seq` coincides with the usual notion of Cauchy sequences. -/
lemma cau_seq_iff_cauchy_seq {α : Type u} [normed_field α] {u : ℕ → α} :
  is_cau_seq norm u ↔ cauchy_seq u :=
⟨λh, filter_cauchy_of_cauchy ⟨u, h⟩,
 λh, cauchy_of_filter_cauchy u h⟩

/-- A complete normed field is complete as a metric space, as Cauchy sequences converge by
assumption and this suffices to characterize completeness. -/
instance complete_space_of_cau_seq_complete [cau_seq.is_complete β norm] : complete_space β :=
begin
  apply complete_of_cauchy_seq_tendsto,
  assume u hu,
  have C : is_cau_seq norm u := cau_seq_iff_cauchy_seq.2 hu,
  existsi cau_seq.lim ⟨u, C⟩,
  rw metric.tendsto_at_top,
  assume ε εpos,
  cases (cau_seq.equiv_lim ⟨u, C⟩) _ εpos with N hN,
  existsi N,
  simpa [dist_eq_norm] using hN
end

end
