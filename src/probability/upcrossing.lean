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
  refine stopped_value_lower_crossing (h.symm ▸ hn),
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

-- from #12509
lemma strict_mono.not_bdd_above_range {α β} [preorder α] [no_max_order α] [nonempty α] [preorder β]
  [succ_order β] [is_succ_archimedean β] {f : α → β} (hf : strict_mono f) :
  ¬ bdd_above (set.range f) :=
begin
  sorry
end

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

/-- The number of upcrossings (strictly) before time `N`. -/
noncomputable
def upcrossing (a b : ℝ) (f : ℕ → α → ℝ) (N : ℕ) (x : α) : ℕ :=
Sup {n | upper_crossing a b f N n x < N}

lemma le_sub_of_le_upcrossing (hn : n ≤ upcrossing a b f N x) :
  b - a ≤
  stopped_value f (upper_crossing a b f N (n + 1)) x -
  stopped_value f (lower_crossing a b f N n) x :=
begin
  rw upcrossing at hn,
  sorry
end

end upcrossing

end measure_theory
