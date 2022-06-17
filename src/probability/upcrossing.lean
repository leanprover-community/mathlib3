import probability.martingale

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α}

section upcrossing

variables [preorder ι] [has_Inf ι]

noncomputable
def lower_crossing_aux (a : ℝ) (f : ℕ → α → ℝ) (c N : ℕ) : α → ℕ :=
hitting f (set.Iic a) c N

noncomputable
def upper_crossing (a b : ℝ) (f : ℕ → α → ℝ) (N : ℕ) : ℕ → α → ℕ
| 0 := 0
| (n + 1) := λ x, hitting f (set.Ici b) (lower_crossing_aux a f (upper_crossing n x) N x) N x

noncomputable
def lower_crossing (a b : ℝ) (f : ℕ → α → ℝ) (N n : ℕ) : α → ℕ :=
λ x, hitting f (set.Iic a) (upper_crossing a b f N n x) N x

variables {a b : ℝ} {f : ℕ → α → ℝ} {N : ℕ}

@[simp]
lemma upper_crossing_zero : upper_crossing a b f N 0 = 0 := rfl

@[simp]
lemma lower_crossing_zero : lower_crossing a b f N 0 = hitting f (set.Iic a) 0 N := rfl

@[simp]
lemma upper_crossing_succ (n : ℕ) (x : α) :
  upper_crossing a b f N (n + 1) x =
  hitting f (set.Ici b) (lower_crossing_aux a f (upper_crossing a b f N n x) N x) N x :=
by rw upper_crossing

lemma upper_crossing_le (n : ℕ) (x : α) : upper_crossing a b f N n x ≤ N :=
begin
  cases n,
  { simp only [upper_crossing_zero, zero_le, pi.zero_apply] },
  { simp only [hitting_le x, upper_crossing_succ] },
end

lemma lower_crossing_le (n : ℕ) (x : α) : lower_crossing a b f N n x ≤ N :=
by simp only [lower_crossing, hitting_le x]

lemma lower_crossing_le_upper_crossing (n : ℕ) (x : α) :
  upper_crossing a b f N n x ≤ lower_crossing a b f N n x :=
by simp only [lower_crossing, le_hitting (upper_crossing_le n x) x]

lemma upper_crossing_le_lower_crossing_succ (n : ℕ) (x : α) :
  lower_crossing a b f N n x ≤ upper_crossing a b f N (n + 1) x :=
begin
  rw upper_crossing_succ,
  exact le_hitting (lower_crossing_le n x) x,
end

-- lemma le_stopped_value_upper_crossing (n : ℕ) (x : α) :
--   stopped_value f (upper_crossing a b f N n) x = N ∨
--   a ≤ stopped_value f (upper_crossing a b f N n) x :=
-- begin
--   rw or_iff_not_imp_left,
--   intro h,
--   rw stopped_value,
--   simp,
--   rw stopped_value_hitting
-- end

end upcrossing

end measure_theory
