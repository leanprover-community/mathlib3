import tactic.positivity

namespace tactic
variables {α : Type*}

open positivity

private lemma nat_cast_nonneg [ordered_semiring α] (n : ℕ) : 0 ≤ (n : α) := n.cast_nonneg

private lemma nat_cast_pos [ordered_semiring α] [nontrivial α] {n : ℕ} (hn : 0 < n) : 0 < (n : α) :=
nat.cast_pos.2 hn

private lemma int_cast_nonneg [ordered_ring α] {n : ℤ} (hn : 0 ≤ n) : 0 ≤ (n : α) :=
by { rw ←int.cast_zero, exact int.cast_mono hn }

private lemma int_cast_pos [ordered_ring α] [nontrivial α] {n : ℤ} : 0 < n → 0 < (n : α) :=
int.cast_pos.2

private lemma rat_cast_nonneg [linear_ordered_field α] {q : ℚ} : 0 ≤ q → 0 ≤ (q : α) :=
rat.cast_nonneg.2

private lemma rat_cast_pos [linear_ordered_field α] {q : ℚ} : 0 < q → 0 < (q : α) := rat.cast_pos.2

/-- Extension for the `positivity` tactic: cast of a natural is nonnegative. -/
@[positivity]
meta def positivity_coe : expr → tactic strictness
| `(coe %%a) := do
  typ_a ← infer_type a,
  strictness_a ← try_core (core a),
  match typ_a, strictness_a with
  | `(ℕ), some (positive p) := positive <$> mk_app ``nat_cast_pos [p]
  | `(ℕ), _ := nonnegative <$> mk_app ``nat_cast_nonneg [a]
  | `(ℤ), some (positive p) := positive <$> mk_app ``int_cast_pos [p]
  | `(ℤ), some (nonnegative p) := nonnegative <$> mk_app ``int_cast_nonneg [a]
  | `(ℚ), some (positive p) := positive <$> mk_app ``rat_cast_pos [p]
  | `(ℚ), some (nonnegative p) := nonnegative <$> mk_app ``rat_cast_nonneg [a]
  | _, _ := failed
  end
| _ := failed

end tactic
