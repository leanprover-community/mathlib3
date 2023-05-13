import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import analysis.specific_limits.normed
import topology.metric_space.cau_seq_filter
import tactic

open filter

open_locale big_operators topology

universe u
/--
`partial_sum f n` is the sum `f 0 + f 1 + f 2 + ... + f (n - 1)`. Note that this does not include
the term `f n`.
-/
def partial_sum {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :=
∑ i in finset.range n, f i

@[simp]
lemma partial_sum_zero {R : Type u} [add_comm_monoid R] (f : ℕ → R) : partial_sum f 0 = 0 :=
begin
  unfold partial_sum,
  simp,
end

lemma partial_sum_next {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :
  partial_sum f (n + 1) = f n + partial_sum f n :=
begin
  unfold partial_sum,
  rw finset.range_succ,
  apply finset.sum_insert,
  exact finset.not_mem_range_self
end

lemma partial_sum_neg {R : Type u} [add_comm_group R] (f : ℕ → R) (n : ℕ) :
  partial_sum (λ m, - (f m)) n = - (partial_sum f n) :=
begin
  induction n with n hi,
  { simp },
  { simp [partial_sum_next, hi, add_comm] }
end

lemma converges_absolutely_iff_converges_of_all_terms_nonneg (a : ℕ → ℝ) (h : ∀ n, 0 ≤ a n) :
  (∃ C, tendsto (partial_sum a) at_top (𝓝 C)) ↔
    (∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) :=
begin
  have : (λ n, ‖a n‖) = a := begin
    funext n,
    exact real.norm_of_nonneg (h n),
  end,
  rw this
end

lemma converges_absolutely_iff_converges_of_all_terms_nonpos (a : ℕ → ℝ) (h : ∀ n, a n ≤ 0) :
  (∃ C, tendsto (partial_sum a) at_top (𝓝 C)) ↔
    (∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) :=
begin
  rw show (λ n, ‖a n‖) = (λ n, - a n), from funext (λ (n : ℕ), real.norm_of_nonpos (h n)),
  rw show (partial_sum (λ n, - a n)) = λ n, - (partial_sum a n),
    from funext (λ n, partial_sum_neg a n),
  split; rintros ⟨C, hC⟩; use -C,
  { exact tendsto.neg hC },
  { simpa using tendsto.neg hC }
end

lemma diff_partial_sums_of_agrees' {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n) (n : ℕ)
  : partial_sum a (n + k) - partial_sum b (n + k) = partial_sum a k - partial_sum b k :=
begin
  induction n with n hi,
  { simp },
  have : a (n + k) + partial_sum a (n + k) - (b (n + k) + partial_sum b (n + k)) =
    (a (n + k) - b (n + k)) + (partial_sum a (n + k) - partial_sum b (n + k)) := by ring,
  simp [this, (show n + 1 + k = n + k + 1, by ring), partial_sum_next, hi, h (n + k) (le_add_self)]
end

lemma diff_partial_sums_of_agrees {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n) {n : ℕ}
  (hn : k ≤ n) : partial_sum a n - partial_sum b n = partial_sum a k - partial_sum b k :=
begin
  have := diff_partial_sums_of_agrees' h (n - k),
  rw nat.sub_add_cancel hn at this,
  exact this,
end

-- Shifts a neighborhood of a topological abelian group up d units
lemma shift_neighborhood {R : Type*} [add_comm_group R] [topological_space R]
  [topological_add_group R] {c : R} {S : set R} (hS : S ∈ 𝓝 c) (d : R)
  : {x : R | x + d ∈ S} ∈ 𝓝 (c - d) :=
begin
  letI : uniform_space R := topological_add_group.to_uniform_space R,
  haveI : uniform_add_group R := topological_add_comm_group_is_uniform,

  rw uniform_space.mem_nhds_iff at ⊢ hS,
  rcases hS with ⟨V, hV, hS⟩,

  have := uniformity_translate_add d,
  rw ←this at hV,
  rw filter.mem_map at hV,

  let W : set (R × R) := (λ (x : R × R), (x.fst + d, x.snd + d)) ⁻¹' V,
  use W,
  have h₁ : ∀ x : R, (x ∈ uniform_space.ball (c - d) W) → (x + d ∈ S) := begin
    intros x hx,
    unfold uniform_space.ball at hx hS,
    apply hS,
    simpa using hx,
  end,
  exact ⟨hV, h₁⟩,
end

lemma converges_of_agrees_converges {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C)) : ∃ C, tendsto (partial_sum b) at_top (𝓝 C) :=
begin
  cases h₁ with C ha,
  let D := partial_sum b k - partial_sum a k,
  use C + D,
  rw tendsto_def at ⊢ ha,
  intros S hS,

  -- U is the neighborhood that results from shifting S by D units
  let U := {x : ℝ | x + D ∈ S},
  have hU : U ∈ 𝓝 C := by simpa using shift_neighborhood hS D,

  -- By hypothesis, there exists an N such that for all n ≥ N, partial_sum a n ∈ U.
  specialize ha U hU,
  rw mem_at_top_sets at ha,
  cases ha with N ha,

  -- We will show that for all m ≥ max N k, partial_sum b m ∈ S.
  rw mem_at_top_sets,
  use max N k,
  intros m hm,

  -- Since m ≥ N, partial_sum a m ∈ U.
  specialize ha m (le_of_max_le_left hm),
  rw set.mem_preimage at ha,

  -- Since partial_sum b m - partial_sum a m = D, we know b m ∈ S.
  change partial_sum a m + (partial_sum b k - partial_sum a k) ∈ S at ha,
  rw ←diff_partial_sums_of_agrees (λ n hn, (h n hn).symm) (le_of_max_le_right hm) at ha,
  rw set.mem_preimage,
  simpa using ha
end

lemma agrees_converges {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n) :
  (∃ C, tendsto (partial_sum a) at_top (𝓝 C)) ↔ (∃ C, tendsto (partial_sum b) at_top (𝓝 C)) :=
begin
  split; intro h₁,
  { exact converges_of_agrees_converges h h₁ },
  { exact converges_of_agrees_converges (λ n hn, (h n hn).symm) h₁ }
end

lemma frequently_exists_nonneg_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : ∃ᶠ (n : ℕ) in at_top, 0 ≤ a n :=
begin
  rw filter.frequently_at_top,
  intro k,
  by_contra h,
  push_neg at h,

  let b := λ n, if k ≤ n then a n else 0,
  have hb : ∀ n, k ≤ n → a n = b n := begin
    intros n hn,
    change a n = if k ≤ n then a n else 0,
    rw if_pos hn,
  end,

  have hb' : ∀ n, k ≤ n → ‖a n‖ = ‖b n‖ := begin
    intros n hn,
    rw hb n hn
  end,

  have hb_nonpos : ∀ n, b n ≤ 0 := begin
    intro n,
    by_cases hn : k ≤ n,
    { specialize h n hn,
      rw (hb n hn) at h,
      exact h.le },
    { change (if k ≤ n then a n else 0) ≤ 0,
      rw if_neg hn }
  end,

  have := converges_absolutely_iff_converges_of_all_terms_nonpos b hb_nonpos,
  rw agrees_converges hb at h₁,
  rw agrees_converges hb' at h₂,
  exact absurd (this.mp h₁) h₂
end

lemma frequently_exists_neg_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : ∃ᶠ (n : ℕ) in at_top, a n < 0 :=
begin
  rw filter.frequently_at_top,
  intro k,
  by_contra h,
  push_neg at h,

  let b := λ n, if k ≤ n then a n else 0,
  have hb : ∀ n, k ≤ n → a n = b n := begin
    intros n hn,
    change a n = if k ≤ n then a n else 0,
    rw if_pos hn,
  end,

  have hb' : ∀ n, k ≤ n → ‖a n‖ = ‖b n‖ := begin
    intros n hn,
    rw hb n hn
  end,

  have hb_nonneg : ∀ n, 0 ≤ b n := begin
    intro n,
    by_cases hn : k ≤ n,
    { specialize h n hn,
      rw (hb n hn) at h,
      exact h },
    { change 0 ≤ (if k ≤ n then a n else 0),
      rw if_neg hn }
  end,

  have := converges_absolutely_iff_converges_of_all_terms_nonneg b hb_nonneg,
  rw agrees_converges hb at h₁,
  rw agrees_converges hb' at h₂,
  exact absurd (this.mp h₁) h₂
end

noncomputable def rearrangement (a : ℕ → ℝ) (M : ℝ) : ℕ → ℕ
| 0 := 0
| (n+1) :=
  if ∑ (x : fin (n + 1)) in finset.univ, a (rearrangement ↑x) ≤ M then
    have h : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ 0 ≤ a k := sorry,
    nat.find h
  else
    have h : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ a k ≤ 0 := sorry,
    nat.find h

theorem riemann_series_theorem {a : ℕ → ℝ} (h₁ : ∃ C : ℝ, tendsto (partial_sum a) at_top (nhds C))
  (h₂ : ¬∃ C : ℝ, tendsto (partial_sum (λ k, ‖a k‖)) at_top (nhds C)) (M : ℝ) : ∃ (p : equiv.perm ℕ),
    filter.tendsto (partial_sum (λ n, a (p n))) filter.at_top (𝓝 M) := sorry
