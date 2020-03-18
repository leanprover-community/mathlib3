
import tactic.slim_check

namespace slim_check.examples

example : ∀ n : ℕ, n > n+1 :=
by success_if_fail { slim_check }; admit

example : ∀ n : ℕ, n < 20 :=
by success_if_fail { slim_check }; admit

open slim_check

run_cmd tactic.unsafe_run_io $ @testable.check (∀ n : ℕ, n > n+1) _ 100
run_cmd tactic.unsafe_run_io $ @testable.check (∀ n m : ℕ, n ≤ m)  _ 100
run_cmd tactic.unsafe_run_io $ @testable.check (∀ n m : ℕ, 2*m + n < 100)  _ 100
run_cmd tactic.unsafe_run_io $ @testable.check (∀ n m : ℕ, 0 ≤ m + n)  _ 100
run_cmd tactic.unsafe_run_io $ @testable.check
                     (∀ (n : ℤ) (xs : list ℤ) x,
                                 x ∈ xs → x < n)  _ 100

example : ∀ n : ℕ, n < n+1 :=
by slim_check

example : 1 < (2 : ℕ) :=
by slim_check

def even (n : ℕ) : bool :=
n % 2 = 0

section
variables (α : Type)

variables [has_add α] [has_one α] [decidable_eq α]

-- example (xs : list α) : 10 ∈ xs → ∃ (x ∈ xs), x = (10 : α) :=
-- by slim_check

example : (∀ (xs : list α), xs ≠ [] → ∃ (x ∈ xs), x = (10 : α)) :=
by success_if_fail { slim_check, }; admit

example : (∀ (xs : list α), ∃ (x ∈ xs), ∃ y ∈ xs, x ≠ y) :=
by success_if_fail { slim_check }; admit -- remaining meta variables

end

example : (∀ (x ∈ [1,2,3,4]), x ≠ 10) :=
by slim_check -- no error message or warning:
              -- slim_check actually proves the statement

example : (∃ (x ∈ [1,2,3,9]), x = 10) :=
by success_if_fail { slim_check }; admit

example : (∀ (α : Type) (xs : list α), xs.length < 10) :=
by success_if_fail { slim_check }; admit

example : (∀ n m : ℕ, 2*m + n < 100) :=
by success_if_fail { slim_check }; admit

-- example : (∀ n m : ℕ, 2*m + n < 10000000000) :=
-- by success_if_fail { slim_check }; admit

example : (∀ n m : ℕ, 2*m + n < 1000000000000) :=
by { slim_check }

example : (∀ (n : ℤ) (xs : list ℤ) x, x ∈ xs → x ≤ n) :=
by success_if_fail { slim_check }; admit

example : (∀ (xs : list ℤ), ∃ x ∈ xs, ∀ y ∈ xs, x ≤ y) :=
by success_if_fail { slim_check }; admit

example : (∀ (xs : list ℤ), xs = [] ∨ ∃ x ∈ xs, ∀ y ∈ xs, x ≤ y) :=
by slim_check

-- example : (∀ (xs : list ℤ), xs ≠ [] → ∃ x ∈ xs, ∀ y ∈ xs, x ≤ y) :=
-- by slim_check

example : (∀ n m : ℕ, even m → ¬ even n → ¬ even (m+n)) :=
by slim_check

variables n m : ℕ

example : (false → even m → ¬ even n → even (m+n)) :=
by success_if_fail { slim_check }; admit

example (xs : list ℕ) (n ∈ xs) : 5*(n+1) ≥ list.length xs :=
by slim_check

end slim_check.examples
