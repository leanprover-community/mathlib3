import topology.metric_space.basic

open filter
open_locale topological_space

lemma tendsto_zero_max_iff_of_nonneg {ι} {fi : _root_.filter ι} (f g : ι → ℝ)
  (hf : 0 ≤ f) (hg : 0 ≤ g) :
  tendsto (λ n, max (f n) (g n)) fi (𝓝 0)
    ↔ tendsto (λ n, f n) fi (𝓝 0) ∧ tendsto (λ n, g n) fi (𝓝 0) :=
begin
  split; intro h,
  { split; refine squeeze_zero _ _ h,
    exacts [hf, λ _, le_max_left _ _ , hg, λ _, le_max_right _ _], },
  { have h_add : tendsto (λ (n : ι), f n + g n) fi (𝓝 0),
      by { convert h.1.add h.2, rw zero_add, },
    exact squeeze_zero (λ n, le_max_of_le_left (hf n))
      (λ n, max_le_add_of_nonneg (hf n) (hg n)) h_add, },
end

lemma prod.tendsto_iff {ι G G'} [pseudo_metric_space G] [pseudo_metric_space G']
  (seq : ι → G × G') {f : filter ι} (x : G × G') :
  tendsto seq f (𝓝 x)
    ↔ tendsto (λ n, (seq n).fst) f (𝓝 x.fst) ∧ tendsto (λ n, (seq n).snd) f (𝓝 x.snd) :=
begin
  rw [tendsto_iff_dist_tendsto_zero, @tendsto_iff_dist_tendsto_zero _ _ _ (λ (n : ι), (seq n).fst),
    @tendsto_iff_dist_tendsto_zero _ _ _ (λ (n : ι), (seq n).snd)],
  simp_rw [prod.dist_eq],
  rw tendsto_zero_max_iff_of_nonneg,
  exacts [λ _, dist_nonneg, λ _, dist_nonneg],
end
