import tactic.assert_exists
import tactic.lint

/-! ### Test `assert_not_exists` -/

assert_not_exists foo

def foo : nat := 1

assert_not_exists bar

run_cmd do
  (_, s) ← lint tt lint_verbosity.medium [`assert_not_exists.linter] tt,
  guard $ "/- `bar` does not ever exist -/\n".is_suffix_of s.to_string

/-! ### Test `assert_no_instance` -/

class some_class (t : Type*).

assert_no_instance (some_class ℕ)

instance : some_class ℕ := {}

assert_no_instance (some_class ℤ)

run_cmd do
  (_, s) ← lint tt lint_verbosity.medium [`assert_no_instance.linter] tt,
  guard $ "/- No instance of `some_class ℤ` -/\n".is_suffix_of s.to_string
