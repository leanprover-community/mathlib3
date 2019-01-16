/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Sébastien Gouëzel

Characterize completeness of metric spaces in terms of Cauchy sequences.
In particular, reconcile the filter notion of Cauchy-ness with the cau_seq notion on normed spaces.
-/

import analysis.topology.uniform_space analysis.normed_space data.real.cau_seq analysis.limits
import tactic.linarith

universes u v
open set filter classical metric

variable {β : Type v}

/-We show that a metric space in which all Cauchy sequences converge is complete, i.e., all
Cauchy filters converge. For this, we approximate any Cauchy filter by a Cauchy sequence,
taking advantage of the fact that there is a sequence tending to `0` in ℝ.-/
namespace sequentially_complete

section
variables [metric_space β] {f : filter β} (hf : cauchy f)

private lemma one_div_succ (n : ℕ) : 1 / ((n : ℝ) + 1) > 0 :=
one_div_pos_of_pos (by linarith using [show (↑n : ℝ) ≥ 0, from nat.cast_nonneg _])

def set_seq_of_cau_filter : ℕ → set β
| 0 := some ((metric.cauchy_iff.1 hf).2 _ (one_div_succ 0))
| (n+1) := (set_seq_of_cau_filter n) ∩ some ((metric.cauchy_iff.1 hf).2 _ (one_div_succ (n + 1)))

lemma set_seq_of_cau_filter_mem_sets : ∀ n, set_seq_of_cau_filter hf n ∈ f.sets
| 0 := some (some_spec ((metric.cauchy_iff.1 hf).2 _ (one_div_succ 0)))
| (n+1) := inter_mem_sets (set_seq_of_cau_filter_mem_sets n)
             (some (some_spec ((metric.cauchy_iff.1 hf).2 _ (one_div_succ (n + 1)))))

lemma set_seq_of_cau_filter_inhabited (n : ℕ) : ∃ x, x ∈ set_seq_of_cau_filter hf n :=
inhabited_of_mem_sets (metric.cauchy_iff.1 hf).1 (set_seq_of_cau_filter_mem_sets hf n)

lemma set_seq_of_cau_filter_spec : ∀ n, ∀ {x y},
  x ∈ set_seq_of_cau_filter hf n → y ∈ set_seq_of_cau_filter hf n → dist x y < 1/((n : ℝ) + 1)
| 0 := some_spec (some_spec ((metric.cauchy_iff.1 hf).2 _ (one_div_succ 0)))
| (n+1) := λ x y hx hy,
  some_spec (some_spec ((metric.cauchy_iff.1 hf).2 _ (one_div_succ (n+1)))) x y
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
  set_seq_of_cau_filter hf (n+1) ⊆ set_seq_of_cau_filter hf n :=
inter_subset_left _ _

lemma set_seq_of_cau_filter_monotone {n k : ℕ} (hle : n ≤ k) :
  set_seq_of_cau_filter hf k ⊆ set_seq_of_cau_filter hf n :=
mono_of_mono_succ (set_seq_of_cau_filter hf) (set_seq_of_cau_filter_monotone' hf) hle

/--The approximating Cauchy sequence for the Cauchy filter `f`-/
noncomputable def seq_of_cau_filter (n : ℕ) : β :=
some (set_seq_of_cau_filter_inhabited hf n)

lemma seq_of_cau_filter_mem_set_seq (n : ℕ) : seq_of_cau_filter hf n ∈ set_seq_of_cau_filter hf n :=
some_spec (set_seq_of_cau_filter_inhabited hf n)

lemma seq_of_cau_filter_is_cauchy' {n k : ℕ} (hle : n ≤ k) :
  dist (seq_of_cau_filter hf n) (seq_of_cau_filter hf k) < 1 / ((n : ℝ) + 1) :=
set_seq_of_cau_filter_spec hf _
  (seq_of_cau_filter_mem_set_seq hf n)
  (set_seq_of_cau_filter_monotone hf hle (seq_of_cau_filter_mem_set_seq hf k))

lemma cauchy_seq_of_dist_tendsto_0 {s : ℕ → β} {b : ℕ → ℝ} (h : ∀ {n k : ℕ}, n ≤ k → dist (s n) (s k) < b n)
  (hb : tendsto b at_top (nhds 0)) : cauchy_seq s :=
begin
  rw metric.cauchy_seq_iff',
  assume ε hε,
  have hb : ∀ (i : set ℝ), (0:ℝ) ∈ i → is_open i → (∃ (a : ℕ), ∀ (c : ℕ), c ≥ a → b c ∈ i),
  { simpa [tendsto, nhds] using hb },
  cases hb (ball 0 ε) (mem_ball_self hε) (is_open_ball) with N hN,
  existsi N,
  intros k hk,
  rw [dist_comm],
  apply lt.trans,
  apply h hk,
  have := hN _ (le_refl _),
  have bnn : ∀ n, b n ≥ 0, from λ n, le_of_lt (lt_of_le_of_lt dist_nonneg (h (le_refl n))),
  simpa [real.norm_eq_abs, abs_of_nonneg (bnn _)] using this
end

lemma tendsto_div : tendsto (λ n : ℕ, 1 / ((n : ℝ) + 1)) at_top (nhds 0) :=
suffices tendsto (λ n : ℕ, 1 / (↑(n + 1) : ℝ)) at_top (nhds 0), by simpa,
tendsto_comp_succ_at_top_iff.2 tendsto_one_div_at_top_nhds_0_nat

/--The approximating sequence is indeed Cauchy-/
lemma seq_of_cau_filter_is_cauchy :
  cauchy_seq (seq_of_cau_filter hf) :=
cauchy_seq_of_dist_tendsto_0 (@seq_of_cau_filter_is_cauchy' _ _ _ hf) tendsto_div

/--
If the approximating Cauchy sequence is converging, to a limit `y`, then the
original Cauchy filter `f` is also converging, to the same limit.

Given `t1` in the filter `f` and `t2` a neighborhood of `y`, it suffices to show that `t1 ∩ t2` is nonempty.
Pick `ε` so that the ε-ball around `y` is contained in `t2`.
Pick `n` with `1/n < ε/2`, and `n2` such that `dist(seq n2, y) < ε/2`. Let `N = max(n, n2)`.
We defined `seq` by looking at a decreasing sequence of sets of `f` with shrinking radius.
The Nth one has radius `< 1/N < ε/2`. This set is in `f`, so we can find an element `x` that's
also in `t1`.
`dist(x, seq N) < ε/2` since `seq N` is in this set, and `dist (seq N, y) < ε/2`,
so `x` is in the ε-ball around `y`, and thus in `t2`.
-/
lemma le_nhds_cau_filter_lim {y : β} (H : tendsto (seq_of_cau_filter hf) at_top (nhds y)) :
  f ≤ nhds y :=
begin
  apply (le_nhds_iff_adhp_of_cauchy hf).2,
  apply forall_sets_neq_empty_iff_neq_bot.1,
  intros s hs,
  simp at hs,
  rcases hs with ⟨t1, ht1, t2, ht2, ht1t2⟩,
  apply ne_empty_iff_exists_mem.2,
  rcases metric.mem_nhds_iff.1 ht2 with ⟨ε, hε, ht2'⟩,
  cases metric.cauchy_iff.1 hf with hfb _,
  have : ε / 2 > 0, from div_pos hε (by norm_num),
  have : ∃ n : ℕ, 1 / (↑n + 1) < ε / 2, from exists_nat_one_div_lt this,
  cases this with n hnε,
  cases metric.tendsto_at_top.1 H _ this with n2 hn2,
  let N := max n n2,
  have hNε : 1 / (↑N+1) < ε / 2,
  { apply lt_of_le_of_lt _ hnε,
    apply one_div_le_one_div_of_le,
    { exact add_pos_of_nonneg_of_pos (nat.cast_nonneg _) zero_lt_one },
    { apply add_le_add_right, simp [le_max_left] }},
  have ht1sn : t1 ∩ set_seq_of_cau_filter hf N ∈ f.sets,
    from inter_mem_sets ht1 (set_seq_of_cau_filter_mem_sets hf _),
  have hts1n_ne : t1 ∩ set_seq_of_cau_filter hf N ≠ ∅,
    from forall_sets_neq_empty_iff_neq_bot.2 hfb _ ht1sn,
  cases exists_mem_of_ne_empty hts1n_ne with x hx,
  have hdist1 := set_seq_of_cau_filter_spec hf _ hx.2 (seq_of_cau_filter_mem_set_seq hf N),
  have hdist2 := hn2 N (le_max_right _ _),
  replace hdist1 := lt_trans hdist1 hNε,
  rw [dist_comm] at hdist2,
  have hdist : dist x y < ε, from calc
    dist x y ≤ dist x (seq_of_cau_filter hf N) + dist y (seq_of_cau_filter hf N) : dist_triangle_right _ _ _
         ... < ε/2 + ε/2 : add_lt_add hdist1 hdist2
         ... = ε : add_halves _,
  have hxt2 : x ∈ t2, from ht2' hdist,
  existsi x,
  apply ht1t2,
  exact mem_inter hx.left hxt2
end

end
end sequentially_complete

/--A metric space in which every Cauchy sequence converges is complete-/
theorem complete_of_cauchy_seq_tendsto {α : Type u} [metric_space α]
  (H : ∀(u : ℕ → α), cauchy_seq u → ∃x, tendsto u at_top (nhds x)) :
  complete_space α :=
⟨begin
  /-Consider a Cauchy filter `f`-/
  intros f hf,
  /-Introduce a sequence `u` approximating the filter `f`-/
  let u := sequentially_complete.seq_of_cau_filter hf,
  /-It is Cauchy-/
  have : cauchy_seq u := sequentially_complete.seq_of_cau_filter_is_cauchy hf,
  /-Therefore, it converges by assumption. Let `x` be its limit-/
  rcases H u this with ⟨x, hx⟩,
  /-The original filter also converges to `x`-/
  exact ⟨x, sequentially_complete.le_nhds_cau_filter_lim hf hx⟩
end⟩


section

/-Now, we will apply these results to `cau_seq`, i.e., "Cauchy sequences" defined by a multiplicative
absolute value on normed fields-/

lemma tendsto_limit [normed_ring β] [hn : is_absolute_value (norm : β → ℝ)]
  (f : cau_seq β norm) [cau_seq.is_complete β norm] :
  tendsto f at_top (nhds f.lim) :=
tendsto_nhds
begin
  intros s lfs os,
  suffices : ∃ (a : ℕ), ∀ (b : ℕ), b ≥ a → f b ∈ s, by simpa using this,
  rcases metric.is_open_iff.1 os _ lfs with ⟨ε, ⟨hε, hεs⟩⟩,
  cases setoid.symm (cau_seq.equiv_lim f) _ hε with N hN,
  existsi N,
  intros b hb,
  apply hεs,
  dsimp [ball], rw [dist_comm, dist_eq_norm],
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
  { apply_instance }
end

/--In a normed field, `cau_seq` coincides with the usual notion of Cauchy sequences-/
lemma cau_seq_iff_cauchy_seq {α : Type u} [normed_field α] {u : ℕ → α} :
  is_cau_seq norm u ↔ cauchy_seq u :=
⟨λh, filter_cauchy_of_cauchy ⟨u, h⟩,
 λh, cauchy_of_filter_cauchy u h⟩

/--A complete normed field is complete as a metric space, as Cauchy sequences converge by
assumption and this suffices to characterize completeness.-/
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
