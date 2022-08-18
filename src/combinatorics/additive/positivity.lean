import tactic.positivity

namespace tactic
variables {α : Type*}

open positivity

private lemma nonneg_of_canon {α : Type*} [canonically_ordered_add_monoid α] (a : α) : 0 ≤ a :=
zero_le _

/-- Extension for the `positivity` tactic: Any element of a canonically ordered additive monoid is
nonnegative. -/
@[positivity]
meta def positivity_canon : expr → tactic strictness
| `(%%a) := nonnegative <$> mk_app ``nonneg_of_canon [a]

private lemma nat_cast_nonneg [ordered_semiring α] (n : ℕ) : 0 ≤ (n : α) := n.cast_nonneg

private lemma nat_cast_pos [ordered_semiring α] [nontrivial α] {n : ℕ} (hn : 0 < n) : 0 < (n : α) :=
nat.cast_pos.2 hn

private lemma int_coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := n.cast_nonneg
private lemma int_coe_nat_pos {n : ℕ} : 0 < n → 0 < (n : ℤ) := nat.cast_pos.2

private lemma int_cast_nonneg [ordered_ring α] {n : ℤ} (hn : 0 ≤ n) : 0 ≤ (n : α) :=
by { rw ←int.cast_zero, exact int.cast_mono hn }

private lemma int_cast_pos [ordered_ring α] [nontrivial α] {n : ℤ} : 0 < n → 0 < (n : α) :=
int.cast_pos.2

private lemma rat_cast_nonneg [linear_ordered_field α] {q : ℚ} : 0 ≤ q → 0 ≤ (q : α) :=
rat.cast_nonneg.2

private lemma rat_cast_pos [linear_ordered_field α] {q : ℚ} : 0 < q → 0 < (q : α) := rat.cast_pos.2

/-- Extension for the `positivity` tactic: casts from `ℕ`, `ℤ`, `ℚ`. -/
@[positivity]
meta def positivity_coe : expr → tactic strictness
| `(@coe %%typ_a _ %%inst %%a) := do
  strictness_a ← core a,
  match inst with
  | `(@coe_to_lift _ _ %%inst) := match inst, strictness_a with
    | `(nat.cast_coe), positive p := positive <$> mk_app ``nat_cast_pos [p]
    | `(nat.cast_coe), nonnegative p := nonnegative <$> mk_app ``nat_cast_nonneg [a]
    | `(int.cast_coe), positive p := positive <$> mk_app ``int_cast_pos [p]
    | `(int.cast_coe), nonnegative p := nonnegative <$> mk_app ``int_cast_nonneg [p]
    | `(rat.cast_coe), positive p := positive <$> mk_app ``rat_cast_pos [p]
    | `(rat.cast_coe), nonnegative p := nonnegative <$> mk_app ``rat_cast_nonneg [p]
    | `(@coe_base _ _ int.has_coe), positive p := positive <$> mk_app ``int_coe_nat_pos [p]
    | `(@coe_base _ _ int.has_coe), nonnegative p := nonnegative <$> mk_app ``int_coe_nat_nonneg [a]
    | _, _ := failed -- TODO: Handle `coe : nnreal → real`
    end
  | _  := failed
  end
| _ := failed

end tactic
