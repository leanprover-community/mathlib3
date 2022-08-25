import tactic.interactive

lemma a {α} [nonempty α] : ∃ a : α, a = a :=
by inhabit α; use default; refl

noncomputable def b {α} [nonempty α] : α :=
by inhabit α; apply default

lemma c {α} [nonempty α] : ∀ n : ℕ, ∃ b : α, n = n :=
by inhabit α; intro; use default; refl

noncomputable def d {α} [nonempty α] : ∀ n : ℕ, α :=
by inhabit α; intro; apply default
