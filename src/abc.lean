import data.nat.prime

open nat

def radical (n : ℕ) : ℕ := (factors n).prod

def abc_triple (a b c : ℕ) : Prop :=
a > 0 ∧ b > 0 ∧ c > 0 ∧ coprime a b ∧ coprime b c ∧ coprime a c ∧ a + b = c

def statement_of_abc_conjecture : Prop :=
∀ n : ℕ, n > 0 → ∃ K : ℕ, ∀ a b c : ℕ, abc_triple a b c → c ^ n < K * (radical (a * b * c)) ^ (n + 1)

theorem abc_conjecture : statement_of_abc_conjecture :=
sorry
