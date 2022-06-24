/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.hitting_time
import probability.martingale

/-!

# Doob's upcrossing estimate

Given a discrete real-valued submartingale $(f_n)_{n \in \mathbb{N}}$, denoting $U_N(a, b)$ the
number of times $f_n$ crossed from below $a$ to above $b$ before time $N$, Doob's upcrossing
estimate (also known as Doob's inequality) states that
$$(b - a) \mathbb{E}[U_N(a, b)] \le \mathbb{E}[(f_N - a)^+].$$
Doob's upcrossing estimate is an important inequality and is central in proving the martingale
convergence theorems.

## Main definitions

* `measure_theory.upper_crossing a b f N n`: is the stopping time corresponding to `f` crossing
  above `b` the `n`-th time.
* `measure_theory.lower_crossing a b f N n`: is the stopping time corresponding to `f` crossing
  below `a` the `n`-th time.
* `measure_theory.upcrossing_strat a b f N`: is the predicatable process which is 1 if `n` is
  between a consecutive pair of lower and upper crossing and is 0 otherwise. Intuitively
  one might think of the `upcrossing_strat` as the strategy of buying 1 share whenever the process
  crosses below `a` for the first time after selling and selling 1 share whenever the process
  crosses above `b` for the first time after buying.
* `measure_theory.upcrossing a b f N`: is the number of times `f` crosses from below `a` to above
  `b` before time `N`.

## Main results

* `measure_theory.adapted.is_stopping_time_upper_crossing`: `upper_crossing` is a stopping time
  whenever the process it is associated to is adapted.
* `measure_theory.adapted.is_stopping_time_lower_crossing`: `lower_crossing` is a stopping time
  whenever the process it is associated to is adapted.
* `measure_theory.submartingale.integral_mul_upcrossing_le_integral_pos_part`: Doob's upcrossing
  estimate.

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α : Type*} {m0 : measurable_space α} {μ : measure α}

/-- `lower_crossing_aux a f c N` is the first time `f` reached below `a` after time `c` before
time `N`. -/
noncomputable
def lower_crossing_aux (a : ℝ) (f : ℕ → α → ℝ) (c N : ℕ) : α → ℕ :=
hitting f (set.Iic a) c N

/-- `upper_crossing a b f N n` is the first time before time `N`, `f` reaches
above `b` after `f` reached below `a` for the `n - 1`-th time. -/
noncomputable
def upper_crossing (a b : ℝ) (f : ℕ → α → ℝ) (N : ℕ) : ℕ → α → ℕ
| 0 := 0
| (n + 1) := λ x, hitting f (set.Ici b) (lower_crossing_aux a f (upper_crossing n x) N x) N x

/-- `lower_crossing a b f N n` is the first time before time `N`, `f` reaches
below `a` after `f` reached above `b` for the `n`-th time. -/
noncomputable
def lower_crossing (a b : ℝ) (f : ℕ → α → ℝ) (N n : ℕ) : α → ℕ :=
λ x, hitting f (set.Iic a) (upper_crossing a b f N n x) N x

variables {a b : ℝ} {f : ℕ → α → ℝ} {N : ℕ} {n m : ℕ} {x : α}

@[simp]
lemma upper_crossing_zero : upper_crossing a b f N 0 = 0 := rfl

@[simp]
lemma lower_crossing_zero : lower_crossing a b f N 0 = hitting f (set.Iic a) 0 N := rfl

lemma upper_crossing_succ :
  upper_crossing a b f N (n + 1) x =
  hitting f (set.Ici b) (lower_crossing_aux a f (upper_crossing a b f N n x) N x) N x :=
by rw upper_crossing

lemma upper_crossing_succ_eq (x : α) :
  upper_crossing a b f N (n + 1) x =
  hitting f (set.Ici b) (lower_crossing a b f N n x) N x :=
begin
  simp only [upper_crossing_succ],
  refl,
end

lemma upper_crossing_le : upper_crossing a b f N n x ≤ N :=
begin
  cases n,
  { simp only [upper_crossing_zero, zero_le, pi.zero_apply] },
  { simp only [hitting_le x, upper_crossing_succ] },
end

@[simp]
lemma upper_crossing_zero' : upper_crossing a b f 0 n x = 0 :=
nat.eq_zero_of_le_zero upper_crossing_le

lemma lower_crossing_le : lower_crossing a b f N n x ≤ N :=
by simp only [lower_crossing, hitting_le x]

lemma upper_crossing_le_lower_crossing :
  upper_crossing a b f N n x ≤ lower_crossing a b f N n x :=
by simp only [lower_crossing, le_hitting upper_crossing_le x]

lemma lower_crossing_le_upper_crossing_succ :
  lower_crossing a b f N n x ≤ upper_crossing a b f N (n + 1) x :=
begin
  rw upper_crossing_succ,
  exact le_hitting lower_crossing_le x,
end

lemma lower_crossing_mono (hnm : n ≤ m) :
  lower_crossing a b f N n x ≤ lower_crossing a b f N m x :=
begin
  suffices : monotone (λ n, lower_crossing a b f N n x),
  { exact this hnm },
  exact monotone_nat_of_le_succ
    (λ n, le_trans lower_crossing_le_upper_crossing_succ upper_crossing_le_lower_crossing)
end

lemma upper_crossing_mono (hnm : n ≤ m) :
  upper_crossing a b f N n x ≤ upper_crossing a b f N m x :=
begin
  suffices : monotone (λ n, upper_crossing a b f N n x),
  { exact this hnm },
  exact monotone_nat_of_le_succ
    (λ n, le_trans upper_crossing_le_lower_crossing lower_crossing_le_upper_crossing_succ),
end

lemma stopped_value_lower_crossing (h : lower_crossing a b f N n x ≠ N) :
  stopped_value f (lower_crossing a b f N n) x ≤ a :=
begin
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hitting_le_iff_of_lt _ (lt_of_le_of_ne lower_crossing_le h)).1 le_rfl,
  exact stopped_value_hitting_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 lower_crossing_le⟩, hj₂⟩,
end

lemma stopped_value_upper_crossing (h : upper_crossing a b f N (n + 1) x ≠ N) :
  b ≤ stopped_value f (upper_crossing a b f N (n + 1)) x :=
begin
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hitting_le_iff_of_lt _ (lt_of_le_of_ne upper_crossing_le h)).1 le_rfl,
  exact stopped_value_hitting_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 (hitting_le _)⟩, hj₂⟩,
end

lemma upper_crossing_lt_lower_crossing (hab : a < b) (hn : lower_crossing a b f N (n + 1) x ≠ N) :
  upper_crossing a b f N (n + 1) x < lower_crossing a b f N (n + 1) x :=
begin
  refine lt_of_le_of_ne upper_crossing_le_lower_crossing
    (λ h, not_le.2 hab $ le_trans _ (stopped_value_lower_crossing hn)),
  simp only [stopped_value],
  rw ← h,
  exact stopped_value_upper_crossing (h.symm ▸ hn),
end

lemma lower_crossing_lt_upper_crossing (hab : a < b) (hn : upper_crossing a b f N (n + 1) x ≠ N) :
  lower_crossing a b f N n x < upper_crossing a b f N (n + 1) x :=
begin
  refine lt_of_le_of_ne lower_crossing_le_upper_crossing_succ
    (λ h, not_le.2 hab $ le_trans (stopped_value_upper_crossing hn) _),
  simp only [stopped_value],
  rw ← h,
  exact stopped_value_lower_crossing (h.symm ▸ hn),
end

lemma upper_crossing_lt_succ (hab : a < b) (hn : upper_crossing a b f N (n + 1) x ≠ N) :
  upper_crossing a b f N n x < upper_crossing a b f N (n + 1) x :=
lt_of_le_of_lt upper_crossing_le_lower_crossing (lower_crossing_lt_upper_crossing hab hn)

lemma lower_crossing_stabilize (hnm : n ≤ m) (hn : lower_crossing a b f N n x = N) :
  lower_crossing a b f N m x = N :=
le_antisymm lower_crossing_le (le_trans (le_of_eq hn.symm) (lower_crossing_mono hnm))

lemma upper_crossing_stabilize (hnm : n ≤ m) (hn : upper_crossing a b f N n x = N) :
  upper_crossing a b f N m x = N :=
le_antisymm upper_crossing_le (le_trans (le_of_eq hn.symm) (upper_crossing_mono hnm))

lemma lower_crossing_stabilize' (hnm : n ≤ m) (hn : N ≤ lower_crossing a b f N n x) :
  lower_crossing a b f N m x = N :=
lower_crossing_stabilize hnm (le_antisymm lower_crossing_le hn)

lemma upper_crossing_stabilize' (hnm : n ≤ m) (hn : N ≤ upper_crossing a b f N n x) :
  upper_crossing a b f N m x = N :=
upper_crossing_stabilize hnm (le_antisymm upper_crossing_le hn)

section move

-- from #12509 **DELETE**
lemma strict_mono.not_bdd_above_range {α β} [preorder α] [no_max_order α] [nonempty α] [preorder β]
  [succ_order β] [is_succ_archimedean β] {f : α → β} (hf : strict_mono f) :
  ¬ bdd_above (set.range f) :=
begin
  sorry
end

-- PRed: #14896
lemma strict_mono_on.Icc_id_le {n : ℕ} {φ : ℕ → ℕ} (hφ : strict_mono_on φ (set.Icc 0 n)) :
  ∀ m ≤ n, m ≤ φ m :=
begin
  induction n with k ih,
  { simp },
  { rintro m (hm : _ ≤ order.succ k),
    have := strict_mono_on.mono hφ (set.Icc_subset_Icc_right (nat.le_succ _)),
    obtain (rfl | h) := order.le_succ_iff_eq_or_le.1 hm,
    { specialize ih this k le_rfl,
      exact le_trans (order.succ_mono ih) (nat.succ_le_of_lt
        (hφ ⟨zero_le _, nat.le_succ _⟩ ⟨zero_le _, le_refl k.succ⟩ (nat.lt_succ_self _))) },
    { exact ih this _ h } }
end

-- PRed: #14896
@[simp]
lemma strict_mono_on_singleton {α β : Type*} [preorder α] [preorder β] (f : α → β) (a : α) :
  strict_mono_on f {a} :=
λ i (hi : i = a) j (hj : j = a) hij, false.elim (hij.ne $ hj.symm ▸ hi)

-- PRed: #14896
lemma strict_mono_on_nat_Icc_of_lt_succ {n : ℕ} {φ : ℕ → ℕ}
  (hφ : ∀ m, m + 1 ≤ n → φ m < φ (m + 1)) :
  strict_mono_on φ (set.Icc 0 n) :=
begin
  induction n with k ih,
  { simp },
  { rintro i ⟨-, hi⟩ j ⟨-, hj⟩ hij,
    specialize ih (λ m hm, hφ _ (le_trans hm (nat.le_succ _))),
    by_cases hj' : j = k.succ,
    { subst hj',
      rw nat.lt_succ_iff at hij,
      exact lt_of_le_of_lt
        (ih.monotone_on ⟨zero_le _, hij⟩ ⟨zero_le _, le_rfl⟩ hij) (hφ _ le_rfl) },
    { have hj'' : j ≤ k,
      { rw ← nat.lt_succ_iff,
        exact lt_of_le_of_ne hj hj' },
      exact ih ⟨zero_le _, le_trans hij.le hj''⟩ ⟨zero_le _, hj''⟩ hij } }
end

end move

-- `upper_crossing_bound_eq` provides an explicit bound
lemma exists_upper_crossing_eq (f : ℕ → α → ℝ) (N : ℕ) (x : α) (hab : a < b) :
  ∃ n, upper_crossing a b f N n x = N :=
begin
  by_contra h, push_neg at h,
  have : strict_mono (λ n, upper_crossing a b f N n x) :=
    strict_mono_nat_of_lt_succ (λ n, upper_crossing_lt_succ hab (h _)),
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := not_bdd_above_iff.1 (strict_mono.not_bdd_above_range this) N,
  exact not_le.2 hk upper_crossing_le
end

lemma upper_crossing_lt_bdd_above (hab : a < b) : bdd_above {n | upper_crossing a b f N n x < N} :=
begin
  obtain ⟨k, hk⟩ := exists_upper_crossing_eq f N x hab,
  refine ⟨k, λ n (hn : upper_crossing a b f N n x < N), _⟩,
  by_contra hn',
  exact hn.ne (upper_crossing_stabilize (not_le.1 hn').le hk)
end

lemma upper_crossing_lt_nonempty (hN : 0 < N) : {n | upper_crossing a b f N n x < N}.nonempty :=
⟨0, hN⟩

lemma upper_crossing_bound_eq (f : ℕ → α → ℝ) (N : ℕ) (x : α) (hab : a < b) (hN : 0 < N) :
  upper_crossing a b f N N x = N :=
begin
  by_cases hN' : N < nat.find (exists_upper_crossing_eq f N x hab),
  { refine le_antisymm upper_crossing_le _,
    have hmono : strict_mono_on (λ n, upper_crossing a b f N n x)
      (set.Icc 0 (nat.find (exists_upper_crossing_eq f N x hab)).pred),
    { refine strict_mono_on_nat_Icc_of_lt_succ (λ m (hm : _ ≤ order.pred _), _),
      refine upper_crossing_lt_succ hab _,
      rw order.le_pred_iff_of_not_is_min at hm,
      { convert nat.find_min _ hm },
      { simp [hN.ne] } },
    convert strict_mono_on.Icc_id_le hmono N (nat.le_pred_of_lt hN') },
  { rw not_lt at hN',
    exact upper_crossing_stabilize hN' (nat.find_spec (exists_upper_crossing_eq f N x hab)) }
end

lemma upper_crossing_eq_of_bound_le (hab : a < b) (hN : 0 < N) (hn : N ≤ n) :
  upper_crossing a b f N n x = N :=
le_antisymm upper_crossing_le
  ((le_trans (upper_crossing_bound_eq f N x hab hN).symm.le (upper_crossing_mono hn)))

variables {ℱ : filtration ℕ m0}

lemma adapted.is_stopping_time_crossing (hf : adapted ℱ f) :
  is_stopping_time ℱ (upper_crossing a b f N n) ∧ is_stopping_time ℱ (lower_crossing a b f N n) :=
begin
  induction n with k ih,
  { refine ⟨is_stopping_time_const _ 0, _⟩,
    simp [hitting_is_stopping_time hf measurable_set_Iic] },
  { obtain ⟨ih₁, ih₂⟩ := ih,
    have : is_stopping_time ℱ (upper_crossing a b f N (k + 1)),
    { intro n,
      simp_rw upper_crossing_succ_eq,
      exact is_stopping_time_hitting_is_stopping_time ih₂ (λ _, lower_crossing_le)
        measurable_set_Ici hf _ },
    refine ⟨this, _⟩,
    { intro n,
      exact is_stopping_time_hitting_is_stopping_time this (λ _, upper_crossing_le)
        measurable_set_Iic hf _ } }
end

lemma adapted.is_stopping_time_upper_crossing (hf : adapted ℱ f) :
  is_stopping_time ℱ (upper_crossing a b f N n) :=
hf.is_stopping_time_crossing.1

lemma adapted.is_stopping_time_lower_crossing (hf : adapted ℱ f) :
  is_stopping_time ℱ (lower_crossing a b f N n) :=
hf.is_stopping_time_crossing.2

/-- `upcrossing_strat a b f N n` is 1 if `n` is between a consecutive pair of lower and upper
crossing and is 0 otherwise. `upcrossing_strat` is shifted by one index so that it is adapted
rather than predictable. -/
noncomputable
def upcrossing_strat (a b : ℝ) (f : ℕ → α → ℝ) (N n : ℕ) (x : α) : ℝ :=
∑ k in finset.range N,
  (set.Ico (lower_crossing a b f N k x) (upper_crossing a b f N (k + 1) x)).indicator 1 n

lemma upcrossing_strat_nonneg : 0 ≤ upcrossing_strat a b f N n x :=
finset.sum_nonneg (λ i hi, set.indicator_nonneg (λ x hx, zero_le_one) _)

-- move
@[to_additive] lemma set.mul_indicator_finset_bUnion_apply {ι M} [comm_monoid M] (I : finset ι)
  (s : ι → set α) {f : α → M} (h : ∀ (i ∈ I) (j ∈ I), i ≠ j → disjoint (s i) (s j)) (x : α) :
  (⋃ i ∈ I, s i).mul_indicator f x = ∏ i in I, (s i).mul_indicator f x :=
by rw set.mul_indicator_finset_bUnion I s h

lemma upcrossing_strat_le_one : upcrossing_strat a b f N n x ≤ 1 :=
begin
  rw [upcrossing_strat, ← set.indicator_finset_bUnion_apply],
  { exact set.indicator_le_self' (λ _ _, zero_le_one) _ },
  { intros i hi j hj hij,
    rw set.Ico_disjoint_Ico,
    obtain (hij' | hij') := lt_or_gt_of_ne hij,
    { rw [min_eq_left (upper_crossing_mono (nat.succ_le_succ hij'.le)),
        max_eq_right (lower_crossing_mono hij'.le)],
      refine le_trans upper_crossing_le_lower_crossing (lower_crossing_mono
        (nat.succ_le_of_lt hij')) },
    { rw gt_iff_lt at hij',
      rw [min_eq_right (upper_crossing_mono (nat.succ_le_succ hij'.le)),
        max_eq_left (lower_crossing_mono hij'.le)],
      refine le_trans upper_crossing_le_lower_crossing
        (lower_crossing_mono (nat.succ_le_of_lt hij')) } }
end

lemma adapted.upcrossing_strat_adapted (hf : adapted ℱ f) :
  adapted ℱ (upcrossing_strat a b f N) :=
begin
  intro n,
  change strongly_measurable[ℱ n] (λ x, ∑ k in finset.range N,
    ({n | lower_crossing a b f N k x ≤ n} ∩
     {n | n < upper_crossing a b f N (k + 1) x}).indicator 1 n),
  refine finset.strongly_measurable_sum _ (λ i hi,
    strongly_measurable_const.indicator ((hf.is_stopping_time_lower_crossing n).inter _)),
  simp_rw ← not_le,
  exact (hf.is_stopping_time_upper_crossing n).compl,
end

lemma submartingale.sum_upcrossing_strat_mul [is_finite_measure μ] (hf : submartingale f ℱ μ)
  (a b : ℝ) (N : ℕ) :
  submartingale
    (λ n : ℕ, ∑ k in finset.range n, upcrossing_strat a b f N k * (f (k + 1) - f k)) ℱ μ :=
hf.sum_mul_sub hf.adapted.upcrossing_strat_adapted
  ⟨1, λ _ _, upcrossing_strat_le_one⟩ (λ _ _, upcrossing_strat_nonneg)

lemma submartingale.sum_sub_upcrossing_strat_mul [is_finite_measure μ] (hf : submartingale f ℱ μ)
  (a b : ℝ) (N : ℕ) :
  submartingale
    (λ n : ℕ, ∑ k in finset.range n, (1 - upcrossing_strat a b f N k) * (f (k + 1) - f k)) ℱ μ :=
begin
  refine hf.sum_mul_sub ((adapted_const ℱ 1).sub hf.adapted.upcrossing_strat_adapted) _ _,
  { refine ⟨1, λ n x, sub_le.1 _⟩,
    simp [upcrossing_strat_nonneg] },
  { intros n x,
    simp [upcrossing_strat_le_one] }
end

lemma submartingale.sum_mul_upcrossing_strat_le [is_finite_measure μ] (hf : submartingale f ℱ μ) :
  μ[∑ k in finset.range n, upcrossing_strat a b f N k * (f (k + 1) - f k)] ≤
  μ[f n] - μ[f 0] :=
begin
  have h₁ : (0 : ℝ) ≤
    μ[∑ k in finset.range n, (1 - upcrossing_strat a b f N k) * (f (k + 1) - f k)],
  { have := (hf.sum_sub_upcrossing_strat_mul a b N).set_integral_le (zero_le n) measurable_set.univ,
    rw [integral_univ, integral_univ] at this,
    refine le_trans _ this,
    simp only [finset.range_zero, finset.sum_empty, integral_zero'] },
  have h₂ : μ[∑ k in finset.range n, (1 - upcrossing_strat a b f N k) * (f (k + 1) - f k)] =
    μ[∑ k in finset.range n, (f (k + 1) - f k)] -
    μ[∑ k in finset.range n, upcrossing_strat a b f N k * (f (k + 1) - f k)],
  { simp only [sub_mul, one_mul, finset.sum_sub_distrib, pi.sub_apply,
      finset.sum_apply, pi.mul_apply],
    refine integral_sub (integrable.sub (integrable_finset_sum _ (λ i hi, hf.integrable _))
      (integrable_finset_sum _ (λ i hi, hf.integrable _))) _,
    convert (hf.sum_upcrossing_strat_mul a b N).integrable n,
    ext, simp },
  rw [h₂, sub_nonneg] at h₁,
  refine le_trans h₁ _,
  simp_rw [finset.sum_range_sub, integral_sub' (hf.integrable _) (hf.integrable _)],
end

/-- The number of upcrossings (strictly) before time `N`. -/
noncomputable
def upcrossing (a b : ℝ) (f : ℕ → α → ℝ) (N : ℕ) (x : α) : ℕ :=
Sup {n | upper_crossing a b f N n x < N}

@[simp]
lemma upcrossing_zero : upcrossing a b f 0 x = 0 :=
by simp [upcrossing]

lemma upper_crossing_lt_of_le_upcrossing
  (hN : 0 < N) (hab : a < b) (hn : n ≤ upcrossing a b f N x) :
  upper_crossing a b f N n x < N :=
begin
  have : upper_crossing a b f N (upcrossing a b f N x) x < N :=
    (upper_crossing_lt_nonempty hN).cSup_mem
    ((order_bot.bdd_below _).finite_of_bdd_above (upper_crossing_lt_bdd_above hab)),
  exact lt_of_le_of_lt (upper_crossing_mono hn) this,
end

lemma upper_crossing_eq_of_upcrossing_lt
  (hab : a < b) (hn : upcrossing a b f N x < n) :
  upper_crossing a b f N n x = N :=
begin
  refine le_antisymm upper_crossing_le (not_lt.1 _),
  convert not_mem_of_cSup_lt hn (upper_crossing_lt_bdd_above hab),
end

lemma upcrossing_le (f : ℕ → α → ℝ) (x : α) (hN : 0 < N) (hab : a < b) :
  upcrossing a b f N x ≤ N :=
begin
  refine cSup_le ⟨0, hN⟩ (λ n (hn : _ < _), _),
  by_contra hnN,
  exact hn.ne (upper_crossing_eq_of_bound_le hab hN (not_le.1 hnN).le),
end

lemma lower_crossing_lt_of_lt_upcrossing
  (hN : 0 < N) (hab : a < b) (hn : n < upcrossing a b f N x) :
  lower_crossing a b f N n x < N :=
lt_of_le_of_lt lower_crossing_le_upper_crossing_succ (upper_crossing_lt_of_le_upcrossing hN hab hn)

lemma le_sub_of_le_upcrossing (hN : 0 < N) (hab : a < b) (hn : n < upcrossing a b f N x) :
  b - a ≤
  stopped_value f (upper_crossing a b f N (n + 1)) x -
  stopped_value f (lower_crossing a b f N n) x :=
sub_le_sub (stopped_value_upper_crossing (upper_crossing_lt_of_le_upcrossing hN hab hn).ne)
  (stopped_value_lower_crossing (lower_crossing_lt_of_lt_upcrossing hN hab hn).ne)

lemma sub_eq_zero_of_upcrossing_lt (hab : a < b) (hn : upcrossing a b f N x < n) :
  stopped_value f (upper_crossing a b f N (n + 1)) x -
  stopped_value f (lower_crossing a b f N n) x = 0 :=
begin
  have : N ≤ upper_crossing a b f N n x,
  { rw upcrossing at hn,
    rw ← not_lt,
    exact λ h, not_le.2 hn (le_cSup (upper_crossing_lt_bdd_above hab) h) },
  simp [stopped_value, upper_crossing_stabilize' (nat.le_succ n) this,
    lower_crossing_stabilize' le_rfl (le_trans this upper_crossing_le_lower_crossing)]
end

lemma mul_upcrossing_le (hf : a ≤ f N x) (hN : 0 < N) (hab : a < b) :
  (b - a) * upcrossing a b f N x ≤
  ∑ k in finset.range N, upcrossing_strat a b f N k x * (f (k + 1) - f k) x :=
begin
  classical,
  simp_rw [upcrossing_strat, finset.sum_mul, ← set.indicator_mul_left, pi.one_apply,
    pi.sub_apply, one_mul],
  rw finset.sum_comm,
  have h₁ : ∀ k, ∑ n in finset.range N,
    (set.Ico (lower_crossing a b f N k x) (upper_crossing a b f N (k + 1) x)).indicator
    (λ m, f (m + 1) x - f m x) n =
    stopped_value f (upper_crossing a b f N (k + 1)) x -
    stopped_value f (lower_crossing a b f N k) x,
  { intro k,
    rw [finset.sum_indicator_eq_sum_filter, (_ : (finset.filter
      (λ i, i ∈ set.Ico (lower_crossing a b f N k x) (upper_crossing a b f N (k + 1) x))
      (finset.range N)) =
      finset.Ico (lower_crossing a b f N k x) (upper_crossing a b f N (k + 1) x)),
      finset.sum_Ico_eq_add_neg _ lower_crossing_le_upper_crossing_succ,
      finset.sum_range_sub (λ n, f n x), finset.sum_range_sub (λ n, f n x), neg_sub,
      sub_add_sub_cancel],
    { refl },
    { ext i,
      simp only [set.mem_Ico, finset.mem_filter, finset.mem_range, finset.mem_Ico,
        and_iff_right_iff_imp, and_imp],
      exact λ _ h, lt_of_lt_of_le h upper_crossing_le } },
  simp_rw [h₁],
  have h₂ : ∑ k in finset.range (upcrossing a b f N x), (b - a) ≤
    ∑ k in finset.range N,
    (stopped_value f (upper_crossing a b f N (k + 1)) x -
    stopped_value f (lower_crossing a b f N k) x),
  { calc ∑ k in finset.range (upcrossing a b f N x), (b - a)
       ≤ ∑ k in finset.range (upcrossing a b f N x),
          (stopped_value f (upper_crossing a b f N (k + 1)) x -
           stopped_value f (lower_crossing a b f N k) x) :
    begin
      refine finset.sum_le_sum (λ i hi, le_sub_of_le_upcrossing hN hab _),
      rwa finset.mem_range at hi,
    end
    ...≤ ∑ k in finset.range N,
          (stopped_value f (upper_crossing a b f N (k + 1)) x -
           stopped_value f (lower_crossing a b f N k) x) :
    begin
      refine finset.sum_le_sum_of_subset_of_nonneg
        (finset.range_subset.2 (upcrossing_le f x hN hab)) (λ i _ hi, _),
      by_cases hi' : i = upcrossing a b f N x,
      { subst hi',
        simp only [stopped_value],
        rw upper_crossing_eq_of_upcrossing_lt hab (nat.lt_succ_self _),
        by_cases heq : lower_crossing a b f N (upcrossing a b f N x) x = N,
        { rw [heq, sub_self] },
        { rw sub_nonneg,
          exact le_trans (stopped_value_lower_crossing heq) hf } },
      { rw sub_eq_zero_of_upcrossing_lt hab,
        rw [finset.mem_range, not_lt] at hi,
        exact lt_of_le_of_ne hi (ne.symm hi') },
    end },
  refine le_trans _ h₂,
  rw [finset.sum_const, finset.card_range, nsmul_eq_mul, mul_comm],
end

lemma integral_mul_upcrossing_le_integral [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hfN : ∀ x, a ≤ f N x) (hfzero : 0 ≤ f 0) (hN : 0 < N) (hab : a < b) :
  (b - a) * μ[upcrossing a b f N] ≤ μ[f N] :=
calc (b - a) * μ[upcrossing a b f N]
     ≤ μ[∑ k in finset.range N, upcrossing_strat a b f N k * (f (k + 1) - f k)] :
begin
  rw ← integral_mul_left,
  refine integral_mono_of_nonneg _ ((hf.sum_upcrossing_strat_mul a b N).integrable N) _,
  { exact eventually_of_forall (λ x, mul_nonneg (sub_nonneg.2 hab.le) (nat.cast_nonneg _)) },
  { refine eventually_of_forall (λ x, _),
    simpa using mul_upcrossing_le (hfN x) hN hab },
end
  ...≤ μ[f N] - μ[f 0] : hf.sum_mul_upcrossing_strat_le
  ...≤ μ[f N] : (sub_le_self_iff _).2 (integral_nonneg hfzero)

lemma crossing_pos_eq (hab : a < b) :
  upper_crossing 0 (b - a) (λ n x, (f n x - a)⁺) N n = upper_crossing a b f N n ∧
  lower_crossing 0 (b - a) (λ n x, (f n x - a)⁺) N n = lower_crossing a b f N n :=
begin
  have hab' : 0 < b - a := sub_pos.2 hab,
  have hf : ∀ x i, b - a ≤ (f i x - a)⁺ ↔ b ≤ f i x,
  { intros i x,
    refine ⟨λ h, _, λ h, _⟩,
    { rwa [← sub_le_sub_iff_right a,
        ← lattice_ordered_comm_group.pos_of_pos_pos (lt_of_lt_of_le hab' h)] },
    { rw ← sub_le_sub_iff_right a at h,
      rwa lattice_ordered_comm_group.pos_of_nonneg _ (le_trans hab'.le h) } },
  have hf' : ∀ x i, (f i x - a)⁺ ≤ 0 ↔ f i x ≤ a,
  { intros x i,
    rw [lattice_ordered_comm_group.pos_nonpos_iff, sub_nonpos] },
  induction n with k ih,
  { refine ⟨rfl, _⟩,
    simp only [lower_crossing_zero, hitting, set.mem_Icc, set.mem_Iic],
    ext x,
    split_ifs with h₁ h₂ h₂,
    { simp_rw [hf'] },
    { simp_rw [set.mem_Iic, ← hf' _ _] at h₂,
      exact false.elim (h₂ h₁) },
    { simp_rw [set.mem_Iic, hf' _ _] at h₁,
      exact false.elim (h₁ h₂) },
    { refl } },
  { have : upper_crossing 0 (b - a) (λ n x, (f n x - a)⁺) N (k + 1) =
      upper_crossing a b f N (k + 1),
    { ext x,
      simp only [upper_crossing_succ_eq, ← ih.2, hitting, set.mem_Ici, tsub_le_iff_right],
      split_ifs with h₁ h₂ h₂,
      { simp_rw [← sub_le_iff_le_add, hf x] },
      { simp_rw [set.mem_Ici, ← hf _ _] at h₂,
        exact false.elim (h₂ h₁) },
      { simp_rw [set.mem_Ici, hf _ _] at h₁,
        exact false.elim (h₁ h₂) },
      { refl } },
    refine ⟨this, _⟩,
    ext x,
    simp only [lower_crossing, this, hitting, set.mem_Iic],
    split_ifs with h₁ h₂ h₂,
    { simp_rw [hf' x] },
    { simp_rw [set.mem_Iic, ← hf' _ _] at h₂,
      exact false.elim (h₂ h₁) },
    { simp_rw [set.mem_Iic, hf' _ _] at h₁,
      exact false.elim (h₁ h₂) },
    { refl } }
end

lemma upcrossing_pos_eq (hab : a < b) :
  upcrossing 0 (b - a) (λ n x, (f n x - a)⁺) N x = upcrossing a b f N x :=
by simp_rw [upcrossing, (crossing_pos_eq hab).1]

private lemma integral_mul_upcrossing_le_integral_pos_part'' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hN : 0 < N) (hab : a < b) :
  (b - a) * μ[upcrossing a b f N] ≤ μ[λ x, (f N x - a)⁺] :=
begin
  refine le_trans (le_of_eq _) (integral_mul_upcrossing_le_integral
    (hf.sub_martingale (martingale_const _ _ _)).pos
    (λ x, lattice_ordered_comm_group.pos_nonneg _)
    (λ x, lattice_ordered_comm_group.pos_nonneg _) hN (sub_pos.2 hab)),
  simp_rw [sub_zero, ← upcrossing_pos_eq hab],
  refl,
end

private lemma integral_mul_upcrossing_le_integral_pos_part' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hab : a < b) :
  (b - a) * μ[upcrossing a b f N] ≤ μ[λ x, (f N x - a)⁺] :=
begin
  by_cases hN : N = 0,
  { subst hN,
    simp only [upcrossing_zero, nat.cast_zero, integral_const, algebra.id.smul_eq_mul, mul_zero],
    exact integral_nonneg (λ x, lattice_ordered_comm_group.pos_nonneg _) },
  { exact integral_mul_upcrossing_le_integral_pos_part'' hf (zero_lt_iff.2 hN) hab }
end

/-- **Doob's upcrossing estimate**: given a real valued discrete submartingale `f` and real
values `a` and `b`, we have `(b - a) * 𝔼[upcrossing a b f N] ≤ 𝔼[(f N - a)⁺]` where
`upcrossing a b f N` is the number of times the process `f` crossed from below `a` to above
`b` before the time `N`. -/
lemma submartingale.integral_mul_upcrossing_le_integral_pos_part [is_finite_measure μ]
  (hf : submartingale f ℱ μ) :
  (b - a) * μ[upcrossing a b f N] ≤ μ[λ x, (f N x - a)⁺] :=
begin
  by_cases hab : a < b,
  { exact integral_mul_upcrossing_le_integral_pos_part' hf hab },
  { rw [not_lt, ← sub_nonpos] at hab,
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (integral_nonneg (λ x, nat.cast_nonneg _)))
      (integral_nonneg (λ x, lattice_ordered_comm_group.pos_nonneg _)) }
end

end measure_theory
