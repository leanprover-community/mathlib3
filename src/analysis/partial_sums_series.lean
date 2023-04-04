import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import analysis.specific_limits.normed
import topology.metric_space.cau_seq_filter
import tactic

open_locale big_operators topology

universe u

/--
`partial_sum f n` is the sum `f 0 + f 1 + f 2 + ... + f (n - 1)`. Note that this does not include
the term `f n`.
-/
def partial_sum {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :=
∑ i in finset.range n, f i

lemma partial_sum_zero (R : Type u) [add_comm_monoid R] (n : ℕ) : partial_sum (λ _ : ℕ, 0) n = 0 :=
finset.sum_eq_zero (λ _ _, rfl)

lemma partial_sum_next {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :
  partial_sum f (n + 1) = f n + partial_sum f n :=
begin
  unfold partial_sum,
  rw finset.range_succ,
  apply finset.sum_insert,
  exact finset.not_mem_range_self
end

def series_sums_to {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) (a : R) :=
filter.tendsto (partial_sum f) filter.at_top (𝓝 a)

def series_converges {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) :=
∃ a : R, series_sums_to f a

def series_converges_absolutely {R : Type u} [add_comm_monoid R] [topological_space R] [has_abs R] (f : ℕ → R) :=
series_converges (λ x, |f x|)

lemma tail_limit {R : Type u} [topological_space R] (f : ℕ → R) (T : R) (h : filter.tendsto f filter.at_top (𝓝 T)) :
  filter.tendsto (λ k, f (k + 1)) filter.at_top (𝓝 T) :=
begin
  rw filter.tendsto_def at h ⊢,
  intros s hs,
  specialize h s hs,
  rw filter.mem_at_top_sets at h ⊢,
  cases h with a h,
  use a,
  intros b hb,
  exact h (b + 1) (nat.le_succ_of_le hb)
end

lemma terms_tendsto_zero (R : Type u) [add_comm_group R] [topological_space R] [topological_add_group R] (a : ℕ → R)
  (h : series_converges a) : filter.tendsto a filter.at_top (𝓝 0) :=
begin
  letI φ : uniform_space R := topological_add_group.to_uniform_space R,
  haveI hφ : uniform_add_group R := topological_add_comm_group_is_uniform,

  -- It suffices to show that for all neighborhoods of zero Z, There exists a N such that for all
  -- n ≥ N, a n ∈ Z.
  rw filter.tendsto_def,
  intros Z hZ,
  rw filter.mem_at_top_sets,

  -- Because `Z ∈ 𝓝 0`, there exists an entourage `V` such that `V[0] ⊆ Z`
  rcases uniform_space.mem_nhds_iff.mp hZ with ⟨V, hV₁, hV₂⟩,

  have h_unif := uniformity_eq_comap_nhds_zero R,
  rw h_unif at hV₁,
  rcases filter.mem_comap.mp hV₁ with ⟨t, ht₁, ht₂⟩,

  set m := λ (x : R × R), x.snd - x.fst,
  have hm : m ⁻¹' t ∈ uniformity R := begin
    rw h_unif,
    rw filter.mem_comap,
    use t,
    use ht₁,
  end,

  obtain ⟨X, hX₁, hX₂⟩ := comp_mem_uniformity_sets hm,
  let W := symmetrize_rel X,
  have hW₁ : W ∈ uniformity R := symmetrize_mem_uniformity hX₁,
  have hW₂ : symmetric_rel W := symmetric_symmetrize_rel X,
  have hW₃ : W ⊆ X := symmetrize_rel_subset_self X,

  cases h with T h,
  unfold series_sums_to at h,
  rw filter.tendsto_def at h,
  specialize h (uniform_space.ball T W) (uniform_space.ball_mem_nhds T hW₁),
  obtain ⟨N, hN⟩ := filter.mem_at_top_sets.mp h,

  use N,
  intros n hn,
  rw set.mem_preimage,

  apply hV₂,
  unfold uniform_space.ball,
  rw set.mem_preimage,
  apply ht₂,
  rw set.mem_preimage,
  change a n - 0 ∈ t,
  rw sub_zero,
  rw (show a n = partial_sum a (n + 1) - partial_sum a n, by simp [partial_sum_next a n]),

  change m (partial_sum a n, partial_sum a (n + 1)) ∈ t,
  rw ←set.mem_preimage,

  have hn₁ := set.mem_preimage.mp (hN n (by linarith)),
  have hn₂ := set.mem_preimage.mp (hN (n + 1) (by linarith)),

  unfold uniform_space.ball at hn₁ hn₂,
  rw set.mem_preimage at hn₁ hn₂,
  rw symmetric_rel.mk_mem_comm hW₂ at hn₁,
  replace hn₁ := hW₃ hn₁,
  replace hn₂ := hW₃ hn₂,
  have : (partial_sum a n, partial_sum a (n + 1)) ∈ comp_rel X X := mem_comp_rel.mpr ⟨T, ⟨hn₁, hn₂⟩⟩,
  have : (partial_sum a n, partial_sum a (n + 1)) ∈ m ⁻¹' t := hX₂ this,
  exact this,
end

lemma seq_tendsto_zero (a : ℕ → ℝ) (h : series_converges a) : filter.tendsto a filter.at_top (𝓝 0) :=
begin
  rw filter.tendsto_def,
  intros s hs,
  rw filter.mem_at_top_sets,

  rw metric.mem_nhds_iff at hs,
  rcases hs with ⟨ε, H, hε⟩,

  cases h with x hx,
  have : is_cau_seq norm (partial_sum a) := (filter.tendsto.cauchy_seq hx).is_cau_seq,
  replace this := is_cau_seq.cauchy₂ this H,
  cases this with i hi,

  use i + 1,
  intros b hb,

  rw set.mem_preimage,
  apply hε,
  rw [metric.mem_ball, dist_eq_norm, sub_zero],
  simpa [partial_sum_next] using hi (b + 1) (by linarith) b (by linarith),
end

lemma partial_sums_le (a b : ℕ → ℝ) (h : ∀ n, a n ≤ b n) : ∀ n, partial_sum a n ≤ partial_sum b n :=
begin
  intro n,
  induction n with n hi,
  { unfold partial_sum,
    simp },
  calc partial_sum a (n + 1) = a n + partial_sum a n : partial_sum_next n
    ... ≤ b n + partial_sum b n : add_le_add (h n) (hi)
    ... = partial_sum b (n + 1) : (partial_sum_next n).symm
end

lemma cau_seq_of_le (a b : ℕ → ℝ) (h : ∀ n, 0 < a n ∧ a n < b n) (hb : series_converges b) : is_cau_seq abs a :=
begin
  cases hb with T hT,
  intros ε hε,
  sorry
end

theorem summable_of_series_absolute_convergence_real {f : ℕ → ℝ}
  (h : series_converges_absolutely f) : summable f :=
summable_of_absolute_convergence_real h
