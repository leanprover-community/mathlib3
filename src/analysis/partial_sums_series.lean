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

theorem terms_tendsto_zero {R : Type u} [add_comm_group R] [topological_space R] [topological_add_group R]
  (a : ℕ → R) (h : series_converges a) : filter.tendsto a filter.at_top (𝓝 0) :=
begin
  -- Since R is a topological group, it has a uniform space.
  -- Since R is abelian, it satisfies `uniform_add_group`
  letI : uniform_space R := topological_add_group.to_uniform_space R,
  haveI : uniform_add_group R := topological_add_comm_group_is_uniform,

  -- It suffices to show that for all neighborhoods `X` of 0, There exists an `N` such that for all
  -- `n ≥ N`, `a n ∈ X`.
  rw filter.tendsto_def,
  intros X hX,
  rw filter.mem_at_top_sets,

  -- Because `X ∈ 𝓝 0`, there exists an entourage `V` such that `V[0] ⊆ X`
  rcases uniform_space.mem_nhds_iff.mp hX with ⟨V, hV₁, hV₂⟩,

  let m := λ (x : R × R), x.snd - x.fst,

  -- By the definition of an entourage in a topological group, there exists a neighbourhood `t` of 0
  -- such that `m ⁻¹' t ⊆ V`
  rw uniformity_eq_comap_nhds_zero R at hV₁,
  rcases filter.mem_comap.mp hV₁ with ⟨t, ht₁, ht₂⟩,

  -- Note that `m ⁻¹' t` is itself an entourage.
  have hm : m ⁻¹' t ∈ uniformity R := begin
    rw uniformity_eq_comap_nhds_zero R,
    rw filter.mem_comap,
    use t,
    use ht₁,
  end,

  -- Let `U` by a "half-size" entourage of `m ⁻¹' t` (so that `comp_rel U U ⊆ m ⁻¹' t`)
  -- Let `W` by the largest symmetric relation which is a subset of `U`. `W` is an entourage.
  obtain ⟨U, hU₁, hU₂⟩ := comp_mem_uniformity_sets hm,
  let W := symmetrize_rel U,
  have hW₁ : W ∈ uniformity R := symmetrize_mem_uniformity hU₁,
  have hW₂ : symmetric_rel W := symmetric_symmetrize_rel U,
  have hW₃ : W ⊆ U := symmetrize_rel_subset_self U,

  -- By hypothesis, the partial sums of `a` tend to some `T`. This means that given any
  -- neighbourhood of T, there exists an `N : ℕ` such that for all `n ≥ N`, the nth partial sum lies
  -- within that neighbourhood. Because `W[T]` is a neighbourhood of `T`, we use this to find our
  -- desired `N`.
  cases h with T h,
  unfold series_sums_to at h,
  rw filter.tendsto_def at h,
  specialize h (uniform_space.ball T W) (uniform_space.ball_mem_nhds T hW₁),
  obtain ⟨N, hN⟩ := filter.mem_at_top_sets.mp h,

  -- Using the `N` we just found, we need to show that for all `n ≥ N`, `a n ∈ X`. Since `V[0] ⊆ X`,
  -- it suffices to show that `a n ∈ V[0]`, or that `(0, a n) ∈ V`.
  use N,
  intros n hn,
  rw set.mem_preimage,
  apply hV₂,
  unfold uniform_space.ball,
  rw set.mem_preimage,

  -- Since `m ⁻¹ t ⊆ V`, it suffices to show that `(0, a n) ∈ m ⁻¹ t`, which is the same as showing
  -- that `m (0, a n) ∈ t`. This is the same as showing that `a n - 0 ∈ t`.
  apply ht₂,
  rw set.mem_preimage,
  change a n - 0 ∈ t,

  -- Note that `a n - 0` is the same as the difference between the nth and (n+1)th partial sums
  -- (because of the way that partial sums are defined here).
  rw sub_zero,
  rw (show a n = partial_sum a (n + 1) - partial_sum a n, by simp [partial_sum_next a n]),

  -- Therefore, we need to show that `partial_sum a (n + 1) - partial_sum a n ∈ t`, which is the
  -- same as showing that `(partial_sum a n, partial_sum a (n + 1)) ∈ m ⁻¹ t`.
  change m (partial_sum a n, partial_sum a (n + 1)) ∈ t,
  rw ←set.mem_preimage,

  -- Using what we deduced earlier from the hypothesis, `(T, partial_sum a n) ∈ W` and
  -- `(T, partial_sum a (n + 1)) ∈ W` (since `n ≥ N` and `n + 1 ≥ N`)
  have hn₁ := set.mem_preimage.mp (hN n hn),
  have hn₂ := set.mem_preimage.mp (hN (n + 1) (by linarith)),
  unfold uniform_space.ball at hn₁ hn₂,
  rw set.mem_preimage at hn₁ hn₂,

  -- `W` is a symmetric relation so `(partial_sum a n, T) ∈ W`.
  rw symmetric_rel.mk_mem_comm hW₂ at hn₁,

  -- Since `W ⊆ U`, `(partial_sum a n, T) ∈ U` and `(T, partial_sum a (n + 1)) ∈ U`,
  replace hn₁ := hW₃ hn₁,
  replace hn₂ := hW₃ hn₂,

  -- Because `comp_rel U U ⊆ m ⁻¹' t`, `(partial_sum a n, partial_sum a (n + 1)) ∈ m ⁻¹ t`.
  show (partial_sum a n, partial_sum a (n + 1)) ∈ m ⁻¹' t, from hU₂ (mem_comp_rel.mpr ⟨T, ⟨hn₁, hn₂⟩⟩)
end

lemma partial_sums_le (a b : ℕ → ℝ) (h : ∀ n, a n ≤ b n) : ∀ n, partial_sum a n ≤ partial_sum b n :=
begin
  intro n,
  induction n with n hi,
  { unfold partial_sum,
    simp },
  calc partial_sum a (n + 1) = a n + partial_sum a n : partial_sum_next a n
    ... ≤ b n + partial_sum b n : add_le_add (h n) (hi)
    ... = partial_sum b (n + 1) : (partial_sum_next b n).symm
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
