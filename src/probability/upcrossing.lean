/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α E ι : Type*} [preorder ι] [measurable_space E]
  {m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E] [borel_space E]
  [second_countable_topology E]
  {f g : ι → α → E} {ℱ : filtration ι m0} [sigma_finite_filtration μ ℱ]

section upcrossing

/-
Upcrossing.

The main idea we need from the definition of upcrossing is:
{x | lim f_n(x) DNE} = {x | lim inf f_n(x) < lim sup f_n(x)} =
⋃ (a < b : ℝ) {x | lim U_n([a, b])(x) = ∞} =
⋃ (a < b : ℚ) {x | lim U_n([a, b])(x) = ∞}

To define upcrossing, we consider the following stopping times.
-/

-- **Update doc string**
/-- The upper crossing of a random process on the interval `[a, b]` before time `n + 1` is the
ℕ-valued random variable corresponding to the first time the process is above `b` after the
`n + 1`-th lower crossing. -/
noncomputable
def upper_crossing (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) : ℕ → α → ℕ
| 0 x := 0
| (n + 1) x := if h : ∃ s, s ≤ N ∧
  (if h : ∃ t, t ≤ N ∧ upper_crossing n x < t ∧ f t x ≤ a then nat.find h else N) < s ∧ b ≤ f s x
  then nat.find h else N

lemma upper_crossing_zero {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} :
  upper_crossing f a b N 0 = 0 :=
rfl

lemma upper_crossing_succ {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} (n : ℕ) :
  upper_crossing f a b N (n + 1) =
  λ x, if h : ∃ s, s ≤ N ∧
      (if h : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a then nat.find h else N) < s ∧
        b ≤ f s x
    then nat.find h else N :=
by { ext x, dsimp [upper_crossing], refl } -- `refl` without `dsimp` only does not work

/-- The lower crossing of a random process on the interval `[a, b]` before time `n + 1` is the
ℕ-valued random variable corresponding to the first time the process is below `a` after the
`n`-th upper crossing. -/
noncomputable
def lower_crossing (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) : ℕ → α → ℕ
| 0 x := 0
| (n + 1) x := if h : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a
  then nat.find h else N

lemma upper_crossing_succ_eq_dite_lower_crossing {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} (n : ℕ) :
  upper_crossing f a b N (n + 1) =
  λ x, if h : ∃ s, s ≤ N ∧ lower_crossing f a b N (n + 1) x < s ∧ b ≤ f s x
    then nat.find h else N :=
begin
  ext x,
  rw upper_crossing_succ,
  refl,
end

lemma lower_crossing_zero {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} :
  lower_crossing f a b N 0 = 0 :=
rfl

lemma lower_crossing_succ {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} (n : ℕ) :
  lower_crossing f a b N (n + 1) =
  λ x, if h : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a then nat.find h else N :=
rfl

-- lemma upper_crossing_is_stopping_time {f : ℕ → α → ℝ} (hf : adapted 𝒢 f) {a b : ℝ} {N : ℕ} {n : ℕ} :
--   is_stopping_time 𝒢 (upper_crossing f a b N n) :=
-- begin
--   intro i,
--   induction n with k ih,
--   { simp [upper_crossing_zero] },
--   { rw upper_crossing_succ,
--     sorry,
--   }
-- end

-- lemma lower_crossing_is_stopping_time {f : ℕ → α → ℝ} (hf : adapted 𝒢 f) {a b : ℝ} {N : ℕ} {n : ℕ} :
--   is_stopping_time 𝒢 (lower_crossing f a b N n) :=
-- sorry

lemma stopped_value_upper_crossing_ge (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) (n : ℕ) (x : α) :
  upper_crossing f a b N (n + 1) x = N ∨
  b ≤ stopped_value f (upper_crossing f a b N (n + 1)) x :=
begin
  rw or_iff_not_imp_left,
  intro h,
  have : ∃ s, s ≤ N ∧ lower_crossing f a b N (n + 1) x < s ∧ b ≤ f s x,
  { by_contra h',
    refine h _,
    rw upper_crossing_succ_eq_dite_lower_crossing,
    exact dif_neg h' },
  convert (nat.find_spec this).2.2,
  rw [stopped_value, upper_crossing_succ_eq_dite_lower_crossing],
  dsimp,
  rw dif_pos this,
end

lemma stopped_value_lower_crossing_le (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) (n : ℕ) (x : α) :
  lower_crossing f a b N (n + 1) x = N ∨
  stopped_value f (lower_crossing f a b N (n + 1)) x ≤ a :=
begin
  rw or_iff_not_imp_left,
  intro h,
  have : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a,
  { by_contra h',
    exact h (dif_neg h') },
  convert (nat.find_spec this).2.2,
  rw [stopped_value, lower_crossing_succ],
  dsimp,
  rw dif_pos this,
end

lemma upper_crossing_stabilize {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n m : ℕ} (hnm : n ≤ m) {x : α}
  (h : upper_crossing f a b N n x = N) : upper_crossing f a b N m x = N :=
begin
  induction hnm with k _ ih,
  { assumption },
  { rw upper_crossing_succ,
    dsimp,
    rw dif_neg,
    push_neg,
    intros t ht hlt,
    rw [ih, dif_neg] at hlt,
    { exact (hlt.not_le ht).elim },
    { push_neg,
      intros s hs hls,
      exact (hls.not_le hs).elim } }
end

lemma upper_crossing_stabilize_of_lower_crossing
  {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n m : ℕ} (hnm : n ≤ m) {x : α}
  (h : lower_crossing f a b N n x = N) : upper_crossing f a b N m x = N :=
begin
  induction hnm with k _ ih,
  { induction n with k ih,
    { rw lower_crossing_zero at h,
      rwa upper_crossing_zero },
    { rw upper_crossing_succ_eq_dite_lower_crossing,
      dsimp,
      rw [h, dif_neg],
      push_neg,
      intros t ht hlt,
      exact (hlt.not_le ht).elim } },
  { exact upper_crossing_stabilize (nat.le_succ _) ih }
end

lemma lower_crossing_stabilize {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n m : ℕ} (hnm : n ≤ m) {x : α}
  (h : lower_crossing f a b N n x = N) : lower_crossing f a b N m x = N :=
begin
  induction hnm with k _ ih,
  { assumption },
  { rw lower_crossing_succ,
    dsimp,
    rw dif_neg,
    { rw upper_crossing_stabilize_of_lower_crossing le_rfl ih,
      push_neg,
      intros t ht hlt,
      exact (hlt.not_le ht).elim } }
end

lemma upper_crossing_sub_lower_crossing {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n : ℕ} {x : α}
  (h : upper_crossing f a b N (n + 1) x ≠ N) :
  b - a ≤ stopped_value f (upper_crossing f a b N (n + 1)) x -
    stopped_value f (lower_crossing f a b N (n + 1)) x :=
begin
  cases stopped_value_lower_crossing_le f a b N n x with heq hle,
  { cases stopped_value_upper_crossing_ge f a b N n x with _ hle',
    { contradiction },
    { exact (h $ upper_crossing_stabilize_of_lower_crossing le_rfl heq).elim } },
  { cases stopped_value_upper_crossing_ge f a b N n x with _ hle',
    { contradiction },
    { linarith } }
end

/-- The `t`-th upcrossing of a random process on the interval `[a, b]` is the ℕ-valued random
variable corresponding to the maximum number of times the random process crossed from below `a` to
above `b` before (not including) time `t`.

**Upcrossing is actually 1 more than what the doc-string suggests here in the non-zero case**
In particular, `upcrossing f a b n` provides the first time the `upper_crossing` reaches `N`
(hence indicating the last time the process performs an upcrossing) if such a time exists and
0 otherwise. -/
noncomputable
def upcrossing (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) : α → ℕ :=
λ x, if h : ∃ n, n < N ∧ upper_crossing f a b N n x = N then nat.find h else 0

lemma upper_crossing_upcrossing_zero {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n : ℕ}
  {x : α} (hn : upcrossing f a b N x ≠ 0) :
  upper_crossing f a b N n x = N :=
begin
  rw [upcrossing, dite_ne_right_iff] at hn,
  sorry
end

lemma upcrossing_le {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {x : α} :
  ↑(upcrossing f a b N x) * (b - a) ≤
  stopped_value f (lower_crossing f a b N 1) x - a +
  ∑ i in finset.range N,
  (stopped_value f (upper_crossing f a b N i) x -
   stopped_value f (lower_crossing f a b N i) x) :=
begin
  set k := if h : ∃ n, n < N ∧ upper_crossing f a b N n x = N then nat.find h else 0 with hk,
  split_ifs at hk,
  { rw ← finset.sum_range_add_sum_Ico _ (nat.find_spec h).1.le,
    have : ∑ k in finset.Ico k N, (stopped_value f (upper_crossing f a b N k) x -
      stopped_value f (lower_crossing f a b N k) x) = 0,
    { sorry },
    rw [← hk, this, add_zero],
    have h' : ∑ i in finset.range k,
      (stopped_value f (upper_crossing f a b N i) x - stopped_value f (lower_crossing f a b N i) x)
    = stopped_value f (upper_crossing f a b N 1) x - stopped_value f (lower_crossing f a b N 1) x +
      ∑ i in finset.Ico 2 k,
      (stopped_value f (upper_crossing f a b N i) x - stopped_value f (lower_crossing f a b N i) x),
    { sorry },
    rw h',
    clear h',
    have h'' : ∑ i in finset.Ico 2 k, (b - a) ≤ ∑ i in finset.Ico 2 k,
      (stopped_value f (upper_crossing f a b N i) x - stopped_value f (lower_crossing f a b N i) x),
    { refine finset.sum_le_sum (λ i hi, _),
      rw finset.mem_Ico at hi,
      cases hi with hi₁ hi₂,
      have hnonneg : i ≠ 0,
      { linarith },
      rcases nat.exists_eq_succ_of_ne_zero hnonneg with ⟨j, rfl⟩,
      refine upper_crossing_sub_lower_crossing (λ hu, _),
      rw hk at hi₂,
      exact nat.find_min h hi₂ ⟨lt_trans hi₂ (nat.find_spec h).1, hu⟩ },
    ring_nf,
    rw ← add_assoc,
    refine le_trans _ (add_le_add le_rfl h''),
    rw finset.sum_const,
    sorry
  },
  { simp only [upcrossing],
    rw [dif_neg h, nat.cast_zero, zero_mul],
    sorry }
end

end upcrossing

end submartingale

end nat

end measure_theory
