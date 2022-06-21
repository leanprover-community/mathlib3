import probability.hitting_time
import probability.martingale

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α}

section upcrossing

variables [preorder ι] [has_Inf ι]

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

@[simp]
lemma upper_crossing_succ :
  upper_crossing a b f N (n + 1) x =
  hitting f (set.Ici b) (lower_crossing_aux a f (upper_crossing a b f N n x) N x) N x :=
by rw upper_crossing

lemma upper_crossing_le : upper_crossing a b f N n x ≤ N :=
begin
  cases n,
  { simp only [upper_crossing_zero, zero_le, pi.zero_apply] },
  { simp only [hitting_le x, upper_crossing_succ] },
end

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

-- move to where `strict_mono_on.mono` is
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

@[simp]
lemma strict_mono_on_singleton {α β : Type*} [preorder α] [preorder β] (f : α → β) (a : α) :
  strict_mono_on f {a} :=
λ i (hi : i = a) j (hj : j = a) hij, false.elim (hij.ne $ hj.symm ▸ hi)

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

-- this lemma is redundent by `upper_crossing_bound_eq`
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

/-- The number of upcrossings (strictly) before time `N`. -/
noncomputable
def upcrossing (a b : ℝ) (f : ℕ → α → ℝ) (N : ℕ) (x : α) : ℕ :=
Sup {n | upper_crossing a b f N n x < N}

-- Remy's proof.
lemma nat.Sup_mem {s : set ℕ} (hs₁ : s.nonempty) (hs₂ : bdd_above s) : Sup s ∈ s :=
set.nonempty.cSup_mem hs₁ ((order_bot.bdd_below _).finite_of_bdd_above hs₂)

lemma upper_crossing_lt_of_le_upcrossing
  (hN : 0 < N) (hab : a < b) (hn : n ≤ upcrossing a b f N x) :
  upper_crossing a b f N n x < N :=
begin
  have : upper_crossing a b f N (upcrossing a b f N x) x < N :=
    nat.Sup_mem (upper_crossing_lt_nonempty hN) (upper_crossing_lt_bdd_above hab),
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

lemma lower_crossing_lt_of_le_upcrossing
  (hN : 0 < N) (hab : a < b) (hn : n < upcrossing a b f N x) :
  lower_crossing a b f N n x < N :=
lt_of_le_of_lt lower_crossing_le_upper_crossing_succ (upper_crossing_lt_of_le_upcrossing hN hab hn)

lemma le_sub_of_le_upcrossing (hN : 0 < N) (hab : a < b) (hn : n < upcrossing a b f N x) :
  b - a ≤
  stopped_value f (upper_crossing a b f N (n + 1)) x -
  stopped_value f (lower_crossing a b f N n) x :=
sub_le_sub (stopped_value_upper_crossing (upper_crossing_lt_of_le_upcrossing hN hab hn).ne)
  (stopped_value_lower_crossing (lower_crossing_lt_of_le_upcrossing hN hab hn).ne)

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

lemma le_sub_stopped_value_upcrossing (hab : a < b) :
  min (f N x - a) 0 ≤ stopped_value f (upper_crossing a b f N (upcrossing a b f N x + 1)) x -
  stopped_value f (lower_crossing a b f N (upcrossing a b f N x)) x :=
begin
  simp only [stopped_value, upper_crossing_eq_of_upcrossing_lt hab (nat.lt_succ_self _)],
  by_cases h : lower_crossing a b f N (upcrossing a b f N x) x = N,
  { simp [h] },
  { exact min_le_of_left_le ((sub_le_sub_iff_left _).2 (stopped_value_lower_crossing h)) },
end

lemma foo (hN : 0 < N) (hab : a < b) :
  (b - a) * upcrossing a b f N x - min (f N x - a) 0 ≤
  ∑ k in finset.range N, (stopped_value f (upper_crossing a b f N (k + 1)) x -
    stopped_value f (lower_crossing a b f N k) x) :=
begin
  rw ← finset.sum_range_add_sum_Ico _ (upcrossing_le f x hN hab),
  have : ∀ (m : ℕ), m ∈ finset.Ico (upcrossing a b f N x) N →
    stopped_value f (upper_crossing a b f N (m + 1)) x -
    stopped_value f (lower_crossing a b f N m) x = 0,
  { rintro m hm,
    rw [finset.mem_Ico, le_iff_eq_or_lt] at hm,
    obtain (hm | hm) := hm,
    { subst hm,
      sorry

    },
    { sorry }
  },
  sorry,
end

lemma foo' (hN : 0 < N) (hab : a < b) :
  (b - a) * upcrossing a b f N x ≤
  stopped_value f (upper_crossing a b f N 1) x - a +
  ∑ k in finset.Ico 1 N, (stopped_value f (upper_crossing a b f N (k + 1)) x -
    stopped_value f (lower_crossing a b f N k) x) :=
begin
  sorry,
end


end upcrossing

end measure_theory
