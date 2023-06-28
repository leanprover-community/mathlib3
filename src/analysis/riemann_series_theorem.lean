import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import analysis.specific_limits.normed
import topology.metric_space.cau_seq_filter
import probability.kernel.cond_cdf
import data.nat.nth
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

lemma partial_sum_add {R : Type u} [add_comm_monoid R] (f : ℕ → R) (g : ℕ → R) (n : ℕ)
: partial_sum f n + partial_sum g n = partial_sum (λ k, f k + g k) n :=
begin
  induction n with n ih,
  { simp },
  { repeat { rw partial_sum_next },
    rw ←ih,
    abel }
end

lemma partial_sum_sub {R : Type u} [add_comm_group R] (f : ℕ → R) (g : ℕ → R) (n : ℕ)
  : partial_sum f n - partial_sum g n = partial_sum (λ k, f k - g k) n :=
begin
  induction n with n ih,
  { simp },
  { repeat { rw partial_sum_next },
    rw ←ih,
    abel }
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

lemma tail_limit' {R : Type u} [topological_space R] (f : ℕ → R) (T : R) (h : filter.tendsto f filter.at_top (𝓝 T)) :
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

lemma tail_limit {R : Type u} [topological_space R] (f : ℕ → R) (C : R) (j : ℕ)
  (h : filter.tendsto f filter.at_top (𝓝 C))
  : filter.tendsto (λ k, f (j + k)) filter.at_top (𝓝 C) :=
begin
  induction j with j ih,
  { simp [h] },
  { have : (λ k : ℕ, f (j.succ + k)) = λ k, f (j + k + 1),
    { funext k,
      change f (j + 1 + k) = _,
      apply congr_arg,
      ring },
    rw this,
    exact tail_limit' _ C ih }
end

lemma converges_of_shift_converges {a : ℕ → ℝ} {k : ℕ}
  (h : ∃ C, tendsto (partial_sum (λ i, a (k + i))) at_top (𝓝 C))
  : ∃ C, tendsto (partial_sum a) at_top (𝓝 C) :=
begin
  cases h with C hC,
  let D := partial_sum a k,
  use C + D,
  have h₁ : (λ i, partial_sum (λ (i : ℕ), a (k + i)) i + D) = (λ i, partial_sum a (k + i)) := begin
    ext i,
    induction i with i ih,
    { simp  },
    { rw (show k + i.succ = k + i + 1, by ring),
      rw partial_sum_next,
      rw partial_sum_next,
      rw ←ih,
      ring }
  end,
  /-
  have := tail_limit (partial_sum a) _ k hC,
  rw ←h₁ at this,
  exact filter.tendsto.add hC tendsto_const_nhds
  -/
  sorry
end

lemma shift_converges_of_converges {a : ℕ → ℝ} (k : ℕ)
  (h : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  : ∃ C, tendsto (partial_sum (λ i, a (k + i))) at_top (𝓝 C) :=
begin
  sorry
end

lemma shift_agrees_converges {a b : ℕ → ℝ} (k j l : ℕ) (h : ∀ n : ℕ, k ≤ n → a (j + n) = b (l + n))
  : (∃ C, tendsto (partial_sum a) at_top (𝓝 C)) ↔ (∃ C, tendsto (partial_sum b) at_top (𝓝 C)) :=
begin
  wlog hw : (∃ C, tendsto (partial_sum a) at_top (𝓝 C)),
  { specialize this k l j (λ n hn, (h n hn).symm),
    split,
    { exact λ h, absurd h hw },
    { exact λ h, (this h).mp h } },
  split,
  { intro _,
    have := shift_converges_of_converges j hw,
    exact converges_of_shift_converges ((agrees_converges h).mp this) },
  { exact λ _, hw }
end

def nonneg_terms {R : Type u} [linear_ordered_add_comm_monoid R]
  (a : ℕ → R) : ℕ → R :=
λ n, if 0 ≤ a n then a n else 0

def nonpos_terms {R : Type u} [linear_ordered_add_comm_monoid R]
  (a : ℕ → R) : ℕ → R :=
λ n, if 0 ≤ a n then 0 else a n

/--
  Similar to `nonneg_terms` but the negative terms are deleted rather than replaced with `0`.
-/
noncomputable def nonneg_terms_d {R : Type u} [linear_ordered_add_comm_monoid R]
  (a : ℕ → R) : ℕ → R :=
λ n, a (nat.nth (λ k, 0 ≤ a k) n)

lemma nonneg_terms_nonneg {R : Type u} [linear_ordered_add_comm_monoid R] (a : ℕ → R) (n : ℕ)
  : 0 ≤ nonneg_terms a n :=
begin
  unfold nonneg_terms,
  by_cases h : 0 ≤ a n; simp [h]
end

lemma nonpos_terms_nonpos {R : Type u} [linear_ordered_add_comm_monoid R] (a : ℕ → R) (n : ℕ)
  : nonpos_terms a n ≤ 0 :=
begin
  unfold nonpos_terms,
  by_cases h : 0 ≤ a n,
  { simp [h] },
  { simp [h, (not_le.mp h).le] }
end

lemma nonneg_terms_add_nonpos_terms {R : Type u} [linear_ordered_add_comm_monoid R]
  (a : ℕ → R) (n : ℕ) : nonneg_terms a n + nonpos_terms a n = a n :=
begin
  unfold nonneg_terms,
  unfold nonpos_terms,
  by_cases h : 0 ≤ a n; simp [h]
end

lemma partial_sum_nonneg_terms_add_partial_sum_nonpos_terms {R : Type u}
  [linear_ordered_add_comm_monoid R] (a : ℕ → R) (n : ℕ)
: partial_sum (nonneg_terms a) n + partial_sum (nonpos_terms a) n = partial_sum a n :=
begin
  rw partial_sum_add,
  conv {
    congr,
    congr,
    funext,
    rw nonneg_terms_add_nonpos_terms
  }
end

lemma nonneg_terms_sub_nonpos_terms (a : ℕ → ℝ) (n : ℕ)
  : nonneg_terms a n - nonpos_terms a n = ‖a n‖ :=
begin
  unfold nonneg_terms,
  unfold nonpos_terms,
  by_cases h : 0 ≤ a n,
  { simp [h, real.norm_of_nonneg h] },
  { simp [h, real.norm_of_nonpos (not_le.mp h).le] }
end

lemma partial_sum_nonneg_terms_sub_partial_sum_nonpos_terms (a : ℕ → ℝ) (n : ℕ)
: partial_sum (nonneg_terms a) n - partial_sum (nonpos_terms a) n = partial_sum (λ k, ‖a k‖) n :=
begin
  rw partial_sum_sub,
  conv {
    congr,
    congr,
    funext,
    rw nonneg_terms_sub_nonpos_terms
  }
end

lemma monotone_partial_sum_nonneg_terms (a : ℕ → ℝ) : monotone (partial_sum (nonneg_terms a)) :=
begin
  intros n m hnm,
  induction m with m ih,
  { rw nat.eq_zero_of_le_zero hnm },
  { by_cases h : n = m.succ,
    { rw h },
    { have h₁ : n ≤ m := nat.le_of_lt_succ (lt_of_le_of_ne hnm h),
      have pt_nonneg : 0 ≤ nonneg_terms a m := nonneg_terms_nonneg a m,
      calc partial_sum (nonneg_terms a) n ≤ partial_sum (nonneg_terms a) m : ih h₁
                                  ... ≤ nonneg_terms a m + partial_sum (nonneg_terms a) m : by linarith
                                  ... = partial_sum (nonneg_terms a) (m + 1) : by rw partial_sum_next } }
end

lemma antitone_partial_sum_nonpos_terms (a : ℕ → ℝ) : antitone (partial_sum (nonpos_terms a)) :=
begin
  unfold antitone,
  intros n m hnm,
  induction m with m ih,
  { rw nat.eq_zero_of_le_zero hnm },
  { by_cases h : n = m.succ,
    { rw h },
    { have h₁ : n ≤ m := nat.le_of_lt_succ (lt_of_le_of_ne hnm h),
      have : nonpos_terms a m ≤ 0 := nonpos_terms_nonpos a m,
      calc partial_sum (nonpos_terms a) (m + 1)
            = nonpos_terms a m + partial_sum (nonpos_terms a) m : partial_sum_next _ _
        ... ≤ partial_sum (nonpos_terms a) m : by linarith
        ... ≤ partial_sum (nonpos_terms a) n : ih h₁ } }
end

lemma nonneg_terms_tendsto_at_top_at_top_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : tendsto (partial_sum (nonneg_terms a)) at_top at_top :=
begin
  cases tendsto_of_monotone (monotone_partial_sum_nonneg_terms a) with h,
  { exact h },
  { exfalso,
    apply h₂,
    cases h with C hC,
    cases h₁ with D hD,
    have hsum : ∀ k, partial_sum (nonneg_terms a) k - (partial_sum a k - partial_sum (nonneg_terms a) k)
      = partial_sum (λ i, ‖a i‖) k,
    { intro k,
      have : partial_sum a k - partial_sum (nonneg_terms a) k = partial_sum (nonpos_terms a) k,
      { rw ←partial_sum_nonneg_terms_add_partial_sum_nonpos_terms a k,
        simp },
      rw this,
      exact partial_sum_nonneg_terms_sub_partial_sum_nonpos_terms a k },
    have := filter.tendsto.sub hC (filter.tendsto.sub hD hC),
    conv at this {
      congr,
      funext,
      rw hsum
    },
    use C - (D - C),
    exact this }
end

lemma nonpos_terms_tendsto_at_top_at_bot_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : tendsto (partial_sum (nonpos_terms a)) at_top at_bot :=
begin
  cases tendsto_of_antitone (antitone_partial_sum_nonpos_terms a) with h,
  { exact h },
  { exfalso,
    apply h₂,
    cases h with C hC,
    cases h₁ with D hD,
    have hsum : ∀ k, (partial_sum a k - partial_sum (nonpos_terms a) k) - partial_sum (nonpos_terms a) k
      = partial_sum (λ i, ‖a i‖) k,
    { intro k,
      have : partial_sum a k - partial_sum (nonpos_terms a) k = partial_sum (nonneg_terms a) k,
      { rw ←partial_sum_nonneg_terms_add_partial_sum_nonpos_terms a k,
        simp },
      rw this,
      exact partial_sum_nonneg_terms_sub_partial_sum_nonpos_terms a k },
    have := filter.tendsto.sub (filter.tendsto.sub hD hC) hC,
    conv at this {
      congr,
      funext,
      rw hsum
    },
    use D - C - C,
    exact this }
end

lemma frequently_exists_pos_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : ∃ᶠ (n : ℕ) in at_top, 0 < a n :=
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
      exact h },
    { change (if k ≤ n then a n else 0) ≤ 0,
      rw if_neg hn }
  end,

  have := converges_absolutely_iff_converges_of_all_terms_nonpos b hb_nonpos,
  rw agrees_converges hb at h₁,
  rw agrees_converges hb' at h₂,
  exact absurd (this.mp h₁) h₂
end

/--
  Weaker version of `frequently_exists_pos_of_conditionally_converging`
-/
lemma frequently_exists_nonneg_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : ∃ᶠ (n : ℕ) in at_top, 0 ≤ a n :=
begin
  have := frequently_exists_pos_of_conditionally_converging h₁ h₂,
  rw filter.frequently_at_top at ⊢ this,
  intro n,
  obtain ⟨m, hm₁, hm₂⟩ := this n,
  exact ⟨m, hm₁, hm₂.le⟩,
end

lemma nonneg_infinite_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : {n : ℕ | 0 ≤ a n}.infinite :=
begin
  rw set.infinite_iff_frequently_cofinite,
  rw nat.cofinite_eq_at_top,
  exact frequently_exists_nonneg_of_conditionally_converging h₁ h₂
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

lemma exists_pos_not_in_finset_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (s : finset ℕ)
  : ∃ n, n ∉ s ∧ 0 < a n :=
begin
  have := frequently_exists_pos_of_conditionally_converging h₁ h₂,
  obtain ⟨n, hn₁, hn₂⟩ := frequently_at_top.mp this (if h : s.nonempty then s.max' h + 1 else 0),
  use n,
  split,
  { by_cases hs : s.nonempty,
    { rw dif_pos hs at hn₁,
      intro h,
      exact absurd (finset.le_max' s n h) (not_le_of_lt (nat.lt_of_succ_le hn₁)) },
    { unfold finset.nonempty at hs,
      push_neg at hs,
      exact hs n } },
  { exact hn₂ }
end

lemma exists_neg_not_in_finset_of_conditionally_converging {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (s : finset ℕ)
  : ∃ n, n ∉ s ∧ a n < 0 :=
begin
  have := frequently_exists_neg_of_conditionally_converging h₁ h₂,
  obtain ⟨n, hn₁, hn₂⟩ := frequently_at_top.mp this (if h : s.nonempty then s.max' h + 1 else 0),
  use n,
  split,
  { by_cases hs : s.nonempty,
    { rw dif_pos hs at hn₁,
      intro h,
      exact absurd (finset.le_max' s n h) (not_le_of_lt (nat.lt_of_succ_le hn₁)) },
    { unfold finset.nonempty at hs,
      push_neg at hs,
      exact hs n } },
  { exact hn₂ }
end

noncomputable def rearrangement (a : ℕ → ℝ) (M : ℝ) : ℕ → ℕ
| 0 := 0
| (n+1) :=
  if ∑ (x : fin (n + 1)) in finset.univ, a (rearrangement ↑x) ≤ M then
    -- We could demonstrate that there exists a positive `a k` rather than a nonnegative one but then
    -- this function wouldn't be surjective
    Inf {k : ℕ | k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ 0 ≤ a k}
  else
    Inf {k : ℕ | k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ a k < 0}

lemma exists_nonneg_terms_not_in_range_fin_rearrangement {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ) (n : ℕ)
  : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧ 0 ≤ a k :=
begin
  obtain ⟨n, hn₁, hn₂⟩ := exists_pos_not_in_finset_of_conditionally_converging h₁ h₂
        ((set.range (λ x : fin (n + 1), rearrangement a M ↑x)).to_finset),
  use n,
  rw ←set.mem_to_finset,
  exact ⟨hn₁, hn₂.le⟩
end

lemma exists_neg_terms_not_in_range_fin_rearrangement {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ) (n : ℕ)
  : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧ a k < 0 :=
begin
  obtain ⟨n, hn₁, hn₂⟩ := exists_neg_not_in_finset_of_conditionally_converging h₁ h₂
        ((set.range (λ x : fin (n + 1), rearrangement a M ↑x)).to_finset),
  use n,
  rw ←set.mem_to_finset,
  exact ⟨hn₁, hn₂⟩
end

lemma rearrangement_fin_sum_def (a : ℕ → ℝ) (M : ℝ) (n : ℕ)
  : ∑ (x : fin n) in finset.univ, a (rearrangement a M ↑x) =
    partial_sum (λ k, a (rearrangement a M k)) n :=
fin.sum_univ_eq_sum_range (λ k, a (rearrangement a M k)) n

lemma rearrangement_def {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ) (n : ℕ)
  : rearrangement a M (n + 1) =
    if partial_sum (λ k, a (rearrangement a M k)) (n + 1) ≤ M then
      Inf {k : ℕ | k ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧ 0 ≤ a k}
    else
      Inf {k : ℕ | k ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧ a k < 0} :=
begin
  unfold rearrangement,
  simp [rearrangement_fin_sum_def]
end

lemma rearrangement_nonneg {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) {M : ℝ} {n : ℕ}
  (h : partial_sum (λ k, a (rearrangement a M k)) (n + 1) ≤ M)
  : rearrangement a M (n + 1) =
    Inf {k : ℕ | k ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧ 0 ≤ a k} :=
begin
  rw rearrangement_def h₁ h₂,
  exact if_pos h
end

lemma rearrangement_nonneg' {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) {M : ℝ} {n : ℕ}
  (h : partial_sum (λ k, a (rearrangement a M k)) n ≤ M) (hn : n ≠ 0)
  : rearrangement a M n =
    Inf {k : ℕ | k ∉ set.range (λ x : fin n, rearrangement a M ↑x) ∧ 0 ≤ a k} :=
begin
  cases n,
  { contradiction },
  { exact rearrangement_nonneg h₁ h₂ h }
end

lemma rearrangement_neg {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) {M : ℝ} {n : ℕ}
  (h : M < partial_sum (λ k, a (rearrangement a M k)) (n + 1))
  : rearrangement a M (n + 1) =
    Inf {k : ℕ | k ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧ a k < 0} :=
begin
  rw rearrangement_def h₁ h₂,
  exact if_neg (by { push_neg, exact h })
end

lemma rearrangement_zero (a : ℕ → ℝ) (M : ℝ) : rearrangement a M 0 = 0 :=
by unfold rearrangement

lemma rearrangement_nonneg_spec {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) {M : ℝ} {n : ℕ}
  (h : partial_sum (λ k, a (rearrangement a M k)) (n + 1) ≤ M)
  : rearrangement a M (n + 1) ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧
    0 ≤ a (rearrangement a M (n + 1)) :=
begin
  rw rearrangement_nonneg h₁ h₂ h,
  exact nat.Inf_mem (exists_nonneg_terms_not_in_range_fin_rearrangement h₁ h₂ M n),
end

lemma rearrangement_nonneg_spec' {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) {M : ℝ} {n : ℕ}
  (h : partial_sum (λ k, a (rearrangement a M k)) n ≤ M) (hn : n ≠ 0)
  : rearrangement a M n ∉ set.range (λ x : fin n, rearrangement a M ↑x) ∧
    0 ≤ a (rearrangement a M n) :=
begin
  cases n,
  { contradiction },
  { exact rearrangement_nonneg_spec h₁ h₂ h }
end

lemma rearrangement_neg_spec {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) {M : ℝ} {n : ℕ}
  (h : M < partial_sum (λ k, a (rearrangement a M k)) (n + 1))
  : rearrangement a M (n + 1) ∉ set.range (λ x : fin (n + 1), rearrangement a M ↑x) ∧
    a (rearrangement a M (n + 1)) < 0 :=
begin
  rw rearrangement_neg h₁ h₂ h,
  exact nat.Inf_mem (exists_neg_terms_not_in_range_fin_rearrangement h₁ h₂ M n),
end

lemma rearrangement_neg_spec' {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) {M : ℝ} {n : ℕ}
  (h : M < partial_sum (λ k, a (rearrangement a M k)) n) (hn : n ≠ 0)
  : rearrangement a M n ∉ set.range (λ x : fin n, rearrangement a M ↑x) ∧
    a (rearrangement a M n) < 0 :=
begin
  cases n,
  { contradiction },
  { exact rearrangement_neg_spec h₁ h₂ h }
end

lemma rearrangement_not_mem {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ) (n : ℕ)
  : rearrangement a M n ∉ set.range (λ x : fin n, rearrangement a M ↑x) :=
begin
  cases n,
  { simp },
  { by_cases h : partial_sum (λ k, a (rearrangement a M k)) (n + 1) ≤ M,
    { exact (rearrangement_nonneg_spec h₁ h₂ h).left },
    { push_neg at h,
      exact (rearrangement_neg_spec h₁ h₂ h).left } }
end

lemma rearrangement_injective {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ)
  : function.injective (rearrangement a M) :=
begin
  unfold function.injective,
  intros n m,
  contrapose,
  intro hnm,
  wlog h : n < m,
  { push_neg at h,
    specialize this h₁ h₂ M (ne.symm hnm) (lt_of_le_of_ne h (ne.symm hnm)),
    exact ne.symm this },
  clear hnm,
  intro hr,
  apply rearrangement_not_mem h₁ h₂ M m,
  rw ←hr,
  use n,
  { exact h },
  { refl }
end

lemma rearrangement_surjective {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ)
  : function.surjective (rearrangement a M) :=
begin
  sorry
end

lemma rearrangement_bijective {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ)
  : function.bijective (rearrangement a M) :=
⟨rearrangement_injective h₁ h₂ M, rearrangement_surjective h₁ h₂ M⟩

@[reducible]
noncomputable def sumto (a : ℕ → ℝ) (M : ℝ) : ℕ → ℝ :=
partial_sum (λ i, a (rearrangement a M i))

/--
  An index is a "switchpoint" when the previous parital sum in the series is on the "opposite side"
  of M. (This is not standard terminology.)
  Remember that `sumto a M (n + 1)` means the sum of the permuted terms up to `n` rather than
  `n + 1`. So `sumto a M (n + 1)` is on the opposite side of `sumto a M n` if and only if
  the `n_th` term was what caused the switch, not the `(n + 1)_th` term.
-/
inductive rearrangement_switchpoint (a : ℕ → ℝ) (M : ℝ) (n : ℕ) : Prop
| start : n = 0 → rearrangement_switchpoint
| under_to_over : sumto a M n ≤ M ∧ M < sumto a M (n + 1) → rearrangement_switchpoint
| over_to_under : M < sumto a M n ∧ sumto a M (n + 1) ≤ M → rearrangement_switchpoint

/--
  Helper instance to make it easier to use rearrangement_switchpoint in nat.find_greatest
-/
noncomputable instance decidable_rearrangement_switchpoint (a : ℕ → ℝ) (M : ℝ) (n : ℕ)
  : decidable (rearrangement_switchpoint a M n) :=
begin
  classical,
  apply_instance
end

lemma diff_M_le_switchpoint (a : ℕ → ℝ) (M : ℝ) {d : ℕ} (hd : rearrangement_switchpoint a M d)
  (hd₁ : d ≠ 0)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : ‖sumto a M (d + 1) - M‖ ≤ ‖a (rearrangement a M d)‖ :=
begin
  have h : sumto a M (d + 1) - sumto a M d = a (rearrangement a M d),
  { unfold sumto,
    rw ←(nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr hd₁)),
    simp [partial_sum_next] },
  cases hd,
  { contradiction },
  { have : sumto a M (d + 1) - M ≤ sumto a M (d + 1) - sumto a M d := by simp [hd.left],
    rw h at this,
    rw real.norm_of_nonneg (show 0 < sumto a M (d + 1) - M, by simp [hd.right]).le,
    rw real.norm_of_nonneg (show 0 ≤ a (rearrangement a M d), by linarith),
    exact this },
  { have h₃ : -(sumto a M (d + 1) - M) < -(sumto a M (d + 1) - sumto a M d) := by simp [hd.left],
    rw h at h₃,
    rw real.norm_of_nonpos (show sumto a M (d + 1) - M ≤ 0, by simp [hd.right]),
    have : a (rearrangement a M d) ≤ 0 := by linarith,
    rw real.norm_of_nonpos this,
    exact h₃.le }
end

@[reducible]
noncomputable def nearest_switchpoint (a : ℕ → ℝ) (M : ℝ) (n : ℕ) : ℕ :=
nat.find_greatest (rearrangement_switchpoint a M) n

lemma nearest_switchpoint_switchpoint (a : ℕ → ℝ) (M : ℝ) (n : ℕ)
: rearrangement_switchpoint a M (nearest_switchpoint a M n) :=
nat.find_greatest_spec (zero_le n) (rearrangement_switchpoint.start rfl)

lemma nearest_switchpoint_le (a : ℕ → ℝ) (M : ℝ) (n : ℕ) : nearest_switchpoint a M n ≤ n :=
nat.find_greatest_le n

lemma rearrangement_preserves_order_of_terms_nonneg (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  (n m : ℕ) (hnm : n < m) (hn₁ : sumto a M n ≤ M) (hn₂ : sumto a M m ≤ M)
  (hn₃ : n ≠ 0)
  : rearrangement a M n < rearrangement a M m :=
begin
  have hm₀ : m ≠ 0 := ne_zero_of_lt hnm,
  have hs : set.range (λ x : fin n, rearrangement a M ↑x) ⊆ set.range (λ x : fin m, rearrangement a M ↑x),
  { rw set.subset_def,
    intros k hk,
    rw set.mem_range at ⊢ hk,
    rcases hk with ⟨⟨a, ha₁⟩, ha₂⟩,
    use ⟨a, lt_trans ha₁ hnm⟩,
    exact ha₂ },
  have hm₁ : rearrangement a M m ∉ set.range (λ x : fin n, rearrangement a M ↑x),
  { intro hmem,
    apply (rearrangement_nonneg_spec' h₁ h₂ hn₂ hm₀).left,
    apply hs,
    exact hmem },
  have hm₂ : 0 ≤ a (rearrangement a M m) := (rearrangement_nonneg_spec' h₁ h₂ hn₂ hm₀).right,
  have : rearrangement a M m ∈ {k : ℕ | k ∉ set.range (λ (x : fin n), rearrangement a M ↑x) ∧ 0 ≤ a k},
  { split; assumption },
  have := nat.Inf_le this,
  rw ←(rearrangement_nonneg' h₁ h₂ hn₁ hn₃) at this,
  apply lt_of_le_of_ne this,
  intro h,
  apply (rearrangement_nonneg_spec' h₁ h₂ hn₂ hm₀).left,
  rw ←h,
  rw set.mem_range,
  use ⟨n, hnm⟩,
  refl
end

lemma rearrangement_preserves_order_of_terms_nonneg' (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  (n m : ℕ) (hnm : n ≤ m) (hn₁ : sumto a M n ≤ M) (hn₂ : sumto a M m ≤ M)
  (hn₃ : n ≠ 0)
  : rearrangement a M n ≤ rearrangement a M m :=
begin
  by_cases h : n = m,
  { rw h },
  { have : n < m := lt_of_le_of_ne hnm h,
    have := rearrangement_preserves_order_of_terms_nonneg a M h₁ h₂ n m this hn₁ hn₂ hn₃,
    exact this.le }
end

/--
  Alternate version of `nat.nth_eq_Inf` which uses the fact that the statements
  `∀ (k : ℕ), k < n + 1 → nat.nth p k < x` and `nat.nth p n < x` are the same since `nat.nth` is
  monotone.
-/
lemma nat.nth_eq_Inf' (p : ℕ → Prop) (n : ℕ) (hf : (set_of p).infinite):
  nat.nth p (n + 1) = Inf {x : ℕ | p x ∧ nat.nth p n < x} :=
begin
  rw nat.nth_eq_Inf,
  apply congr_arg,
  ext x,
  change p x ∧ _ ↔ p x ∧ _,
  split,
  { rintro ⟨h₁, h₂⟩,
    exact ⟨h₁, h₂ n (nat.lt_succ_self n)⟩ },
  { rintro ⟨h₁, h₂⟩,
    apply and.intro h₁,
    intros k hk,
    refine lt_of_le_of_lt _ h₂,
    exact nat.nth_monotone hf (nat.lt_succ_iff.mp hk) }
end

lemma nat.Inf_eq_iff {m : ℕ} {p : ℕ → Prop} (h : ∃ (n : ℕ), p n) :
  Inf {n | p n} = m ↔ p m ∧ ∀ (n : ℕ), n < m → ¬p n :=
begin
  have : {n | p n}.nonempty := h,
  rw nat.Inf_def this,
  exact nat.find_eq_iff h
end

lemma rearrangement_succ_eq_succ_nonneg_d (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  (n : ℕ) (hn₁ : sumto a M n ≤ M) (hn₂ : sumto a M (n + 1) ≤ M) (hn₃ : n ≠ 0)
  (k : ℕ) (hk : rearrangement a M n = nat.nth (λ j : ℕ, 0 ≤ a j) k)
  : rearrangement a M (n + 1) = nat.nth (λ j : ℕ, 0 ≤ a j) (k + 1) :=
begin
  rw nat.nth_eq_Inf' _ k (nonneg_infinite_of_conditionally_converging h₁ h₂),
  have : ∃ n, n ∈ {x : ℕ | 0 ≤ a x ∧ nat.nth (λ (n : ℕ), 0 ≤ a n) k < x},
  { have := frequently_exists_nonneg_of_conditionally_converging h₁ h₂,
    rw filter.frequently_at_top at this,
    obtain ⟨b, hb₁, hb₂⟩ := this (nat.nth (λ (n : ℕ), 0 ≤ a n) k + 1),
    exact ⟨b, hb₂, hb₁⟩ },
  symmetry,
  apply (nat.Inf_eq_iff this).mpr,
  --rw nat.Inf_def this,
  --symmetry,
  --apply (nat.find_eq_iff sorry).mpr,
  set r := rearrangement a M (n + 1),
  split,
  { change 0 ≤ a r ∧ _,
    obtain ⟨hr₁, hr₂⟩ := rearrangement_nonneg_spec h₁ h₂ hn₂,
    apply and.intro hr₂,
    rw ←hk,
    exact rearrangement_preserves_order_of_terms_nonneg a M h₁ h₂ n (n + 1) (nat.lt_succ_self n)
      hn₁ hn₂ hn₃ },
  {
    rintros j hj ⟨hj_contra₁, hj_contra₂⟩,
    rw ←not_le at hj,
    apply hj,
    clear hj,
    have : j ∈ {k : ℕ | k ∉ set.range (λ (x : fin (n + 1)), rearrangement a M ↑x) ∧ 0 ≤ a k},
    {
      refine ⟨_, hj_contra₁⟩,
      rw set.mem_range,
      push_neg,
      rintro ⟨y, hy⟩,
      change rearrangement a M y ≠ j,
      cases y,
      {
        rw rearrangement_zero,
        intro h_contra,
        rw ←h_contra at hj_contra₂,
        exact absurd hj_contra₂ (nat.not_lt_zero _)
      },
      {
        set m := y.succ,
        by_cases hc₂ : sumto a M m ≤ M,
        {
          have := rearrangement_preserves_order_of_terms_nonneg' a M h₁ h₂ m n (nat.lt_succ_iff.mp hy)
            hc₂ hn₁ (show y + 1 ≠ 0, by positivity),
          rw ←hk at hj_contra₂,
          have : rearrangement a M m < j := lt_of_le_of_lt this hj_contra₂,
          exact ne_of_lt this
        },
        {
          push_neg at hc₂,
          -- TODO: can use `rearrangement_neg_spec` without the `'`
          have := (rearrangement_neg_spec' h₁ h₂ hc₂ (show y + 1 ≠ 0, by positivity)).right,
          intro h_contra,
          rw h_contra at this,
          rw ←not_le at this,
          contradiction
        }
      }
    },
    change rearrangement a M (n + 1) ≤ j,
    rw rearrangement_nonneg h₁ h₂ hn₂,
    exact nat.Inf_le this
  }
end

lemma rearrangement_add_eq_add_nonneg_d (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  (n : ℕ) (d : ℕ) (hn₁ : ∀ i, i ≤ d → sumto a M (n + i) ≤ M) (hn₂ : n ≠ 0)
  (k : ℕ) (hk : rearrangement a M n = nat.nth (λ j : ℕ, 0 ≤ a j) k)
  : rearrangement a M (n + d) = nat.nth (λ j : ℕ, 0 ≤ a j) (k + d) :=
begin
  induction d with d ih,
  { simp [hk] },
  { change rearrangement a M (n + d + 1) = nat.nth (λ (j : ℕ), 0 ≤ a j) (k + d + 1),
    refine rearrangement_succ_eq_succ_nonneg_d a M h₁ h₂ (n + d) (hn₁ d (nat.le_succ d))
      (hn₁ (d + 1) le_rfl) (by positivity) (k + d) (ih _),
    intros i hi,
    exact hn₁ i (le_trans hi (nat.le_succ d)) }
end

lemma abs_sumto_sub_M_le_abs_sumto_nearest_switchpoint (a : ℕ → ℝ) (M : ℝ) (n : ℕ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  (hn₁ : nearest_switchpoint a M n ≠ 0)
: ‖sumto a M (n + 1) - M‖ ≤ ‖sumto a M (nearest_switchpoint a M n + 1) - M‖ :=
begin
  induction n with n ih,
  { unfold nearest_switchpoint at hn₁,
    rw nat.find_greatest_zero at hn₁,
    contradiction },
  {
    by_cases h : rearrangement_switchpoint a M (n + 1),
    { unfold nearest_switchpoint at hn₁,
      have : nearest_switchpoint a M (n + 1) = n + 1 := nat.find_greatest_eq h,
      rw this },
    {
      have hsp : nearest_switchpoint a M (n + 1) = nearest_switchpoint a M n := begin
        change nat.find_greatest (rearrangement_switchpoint a M) (n + 1) = _,
        exact nat.find_greatest_of_not h
      end,
      rw hsp at hn₁,
      specialize ih hn₁,
      rw hsp,
      refine le_trans _ ih,
      change ‖partial_sum _ _ - M‖ ≤ _,
      rw partial_sum_next,
      change ‖a (rearrangement a M (n + 1)) + sumto a M (n + 1) - M‖ ≤ ‖sumto a M (n + 1) - M‖,
      by_cases hsum : M < sumto a M (n + 1),
      {
        have ha₁ : a (rearrangement a M (n + 1)) < 0 := (rearrangement_neg_spec h₁ h₂ hsum).right,
        have ha₂ : -a (rearrangement a M (n + 1)) ≤ sumto a M (n + 1) - M := begin
          by_contra ha₂,
          push_neg at ha₂,
          have : a (rearrangement a M (n + 1)) + sumto a M (n + 1) - M < 0 := by linarith,
          unfold sumto at this,
          rw ←partial_sum_next (λ i, a (rearrangement a M i)) at this,
          have := rearrangement_switchpoint.over_to_under ⟨hsum, by linarith⟩,
          exact absurd this h
        end,
        rw real.norm_of_nonneg (show 0 ≤ sumto a M (n + 1) - M, by linarith),
        rw real.norm_of_nonneg (show 0 ≤ a (rearrangement a M (n + 1)) + sumto a M (n + 1) - M, by linarith),
        linarith
      },
      {
        push_neg at hsum,
        have ha₁ : 0 ≤ a (rearrangement a M (n + 1)) := (rearrangement_nonneg_spec h₁ h₂ hsum).right,
        have ha₂ : a (rearrangement a M (n + 1)) ≤ M - sumto a M (n + 1) := begin
          by_contra ha₂,
          push_neg at ha₂,
          have : 0 < a (rearrangement a M (n + 1)) + sumto a M (n + 1) - M := by linarith,
          unfold sumto at this,
          rw ←partial_sum_next (λ i, a (rearrangement a M i)) at this,
          change 0 < sumto a M (n + 2) - M at this,
          have := rearrangement_switchpoint.under_to_over ⟨hsum, by linarith⟩,
          exact absurd this h,
        end,
        rw real.norm_of_nonpos (show sumto a M (n + 1) - M ≤ 0, by linarith),
        rw real.norm_of_nonpos (show a (rearrangement a M (n + 1)) + sumto a M (n + 1) - M ≤ 0, by linarith),
        linarith
      }
    }
  }
end

lemma abs_sumto_sub_M_le_val_nearest_switchpoint (a : ℕ → ℝ) (M : ℝ) (n : ℕ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  (hn : nearest_switchpoint a M n ≠ 0)
: ‖sumto a M (n + 1) - M‖ ≤ ‖a (rearrangement a M (nearest_switchpoint a M n))‖ :=
begin
  have q₁ := abs_sumto_sub_M_le_abs_sumto_nearest_switchpoint a M n h₁ h₂ hn,
  have q₂ := diff_M_le_switchpoint a M (nearest_switchpoint_switchpoint a M n) hn h₁ h₂,
  exact le_trans q₁ q₂
end

lemma frequently_exists_switchpoint (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : ∃ᶠ (n : ℕ) in at_top, rearrangement_switchpoint a M n :=
begin
  by_contra h,
  rw filter.not_frequently at h,
  rw filter.eventually_at_top at h,
  cases h with N h,
  by_cases hN : sumto a M N ≤ M,
  {
    have : ∀ c, sumto a M (N + c + 1) ≤ M,
    { intro c,
      induction c with c ih,
      { by_contra hc,
        push_neg at hc,
        exact h N le_rfl (rearrangement_switchpoint.under_to_over ⟨hN, hc⟩) },
      { rw (show N + c.succ + 1 = N + c + 1 + 1, by ring),
        by_contra hc,
        push_neg at hc,
        exact h (N + c + 1) (by linarith) (rearrangement_switchpoint.under_to_over ⟨ih, hc⟩) } },
    have : ∀ c, 0 ≤ a (rearrangement a M (N + c + 1)),
    { intro c,
      exact (rearrangement_nonneg_spec h₁ h₂ (this c)).right },
    have := frequently_exists_neg_of_conditionally_converging h₁ h₂,
    sorry
  },
  {
    sorry
  }
end

lemma exists_le_nearest_switchpoint (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  (n : ℕ)
  : ∃ m, n ≤ nearest_switchpoint a M m :=
begin
  have := frequently_exists_switchpoint a M h₁ h₂,
  rw filter.frequently_at_top at this,
  obtain ⟨m, hm₁, hm₂⟩ := this n,
  use m,
  apply le_trans hm₁,
  apply le_of_eq,
  exact (nat.find_greatest_eq hm₂).symm
end

lemma tendsto_zero_nearest_switchpoint (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : tendsto (λ n, ‖a (rearrangement a M (nearest_switchpoint a M n))‖) at_top (𝓝 0) :=
begin
  sorry
end

lemma tendsto_zero_abs_sumto_sub_M (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : tendsto (λ n, ‖sumto a M (n + 1) - M‖) at_top (𝓝 0) :=
begin
  have h := tendsto_zero_nearest_switchpoint a M h₁ h₂,
  rw tendsto_def at h ⊢,
  intros s hs,
  obtain ⟨l, u, hlu₁, hlu₂⟩ := mem_nhds_iff_exists_Ioo_subset.mp hs,
  specialize h (set.Ioo l u) (Ioo_mem_nhds (set.mem_Ioo.mp hlu₁).left (set.mem_Ioo.mp hlu₁).right),
  rw mem_at_top_sets at h ⊢,
  cases h with N h,
  -- `c` is an arbitrary natural number which occurs at or after the first switchpoint
  obtain ⟨c, hc⟩  := exists_le_nearest_switchpoint a M h₁ h₂ 1,
  use max N c,
  intros b hb,
  specialize h b (le_of_max_le_left hb),
  rw set.mem_preimage at h ⊢,
  have : 1 ≤ nearest_switchpoint a M b := begin
    apply le_trans hc,
    apply nat.le_find_greatest,
    { exact le_trans (nearest_switchpoint_le a M c) (le_of_max_le_right hb) },
    { exact nearest_switchpoint_switchpoint a M c }
  end,
  apply hlu₂,
  split,
  { have : l < 0 := (set.mem_Ioo.mp hlu₁).left,
    apply lt_of_lt_of_le this,
    positivity },
  { have := abs_sumto_sub_M_le_val_nearest_switchpoint a M b h₁ h₂ (nat.one_le_iff_ne_zero.mp this),
    apply lt_of_le_of_lt this,
    exact (set.mem_Ioo.mp h).right }
end

lemma tendsto_zero_sumto_sub_M (a : ℕ → ℝ) (M : ℝ)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C))
  : tendsto (λ n, sumto a M (n + 1) - M) at_top (𝓝 0) :=
begin
  have h := tendsto_zero_abs_sumto_sub_M a M h₁ h₂,
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h
end

lemma rearrangement_tendsto_M {a : ℕ → ℝ}
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C, tendsto (partial_sum (λ n, ‖a n‖)) at_top (𝓝 C)) (M : ℝ)
  : tendsto (partial_sum (λ n, a (rearrangement a M n))) at_top (𝓝 M) :=
begin
  rw tendsto_def,
  intros s hs,
  rw filter.mem_at_top_sets,
  use 0, -- TODO: Change to a value that works
  intros b hb,
  rw set.mem_preimage,
  sorry
end

theorem riemann_series_theorem {a : ℕ → ℝ} (h₁ : ∃ C : ℝ, tendsto (partial_sum a) at_top (𝓝 C))
  (h₂ : ¬∃ C : ℝ, tendsto (partial_sum (λ k, ‖a k‖)) at_top (𝓝 C)) (M : ℝ) : ∃ (p : equiv.perm ℕ),
    tendsto (partial_sum (λ n, a (p n))) filter.at_top (𝓝 M) :=
⟨equiv.of_bijective _ (rearrangement_bijective h₁ h₂ M), rearrangement_tendsto_M h₁ h₂ M⟩
