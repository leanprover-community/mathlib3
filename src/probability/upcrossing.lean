import probability.martingale

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α}

section upcrossing

variables [preorder ι] [has_Inf ι]

noncomputable
def upper_crossing_aux (a : ℝ) (f : ℕ → α → ℝ) (N : ℕ) (c : ℕ) : α → ℕ :=
hitting f (set.Iic a) c N

noncomputable
def lower_crossing (a b : ℝ) (f : ℕ → α → ℝ) (N : ℕ) : ℕ → α → ℕ
| 0 := 0
| (n + 1) := λ x, hitting f (set.Ici b) (upper_crossing_aux a f N (lower_crossing n x) x) N x

noncomputable
def upper_crossing (a b : ℝ) (f : ℕ → α → ℝ) (N : ℕ) (n : ℕ) : α → ℕ :=
λ x, hitting f (set.Iic a) (lower_crossing a b f N n x) N x

end upcrossing

end measure_theory
