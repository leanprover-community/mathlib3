import tactic.to_additive
import tactic.alias

/-- Test assertion helpers -/
meta def assert_ok (n : name) := do
  decl ← tactic.get_decl n,
  some msg ← linter.to_additive_doc.test decl | pure (),
  fail! "Linting {n} complained unexpectedly:\n{msg}"

meta def assert_complain (n : name) := do
  decl ← tactic.get_decl n,
  none ← linter.to_additive_doc.test decl | pure (),
  fail! "Linting {n} succeeded unexpectedly"

/-- Docstring -/
@[to_additive add_foo]
def foo (α : Type*) [has_one α] : α := 1

run_cmd assert_complain ``foo
run_cmd assert_ok ``add_foo

@[to_additive add_bar "docstring"]
def bar (α : Type*) [has_one α] : α := 1

run_cmd assert_complain ``bar
run_cmd assert_ok ``add_bar

/-- Docstring -/
@[to_additive add_baz "docstring"]
def baz (α : Type*) [has_one α] : α := 1

run_cmd assert_ok ``baz
run_cmd assert_ok ``add_baz

@[to_additive add_quux]
def quux (α : Type*) [has_one α] : α := 1

run_cmd assert_ok ``quux
run_cmd assert_ok ``add_quux

def without_to_additive (α : Type*) [has_one α] : α := 1

run_cmd assert_ok ``without_to_additive

-- Aliases always have docstrings, so we do not want to complain if their
-- additive version do not
alias quux <- quux_alias
attribute [to_additive add_quux_alias] quux_alias

run_cmd assert_ok ``quux_alias
run_cmd assert_ok ``add_quux_alias

-- Same for iff aliases
def a_one_iff_b_one (α : Type*) [has_one α] (a b : α) (h : a = b) : (a = 1) ↔ (b = 1) := by {subst h}
alias a_one_iff_b_one ↔ b_one_of_a_one a_one_of_b_one
attribute [to_additive] a_one_iff_b_one
attribute [to_additive] b_one_of_a_one
attribute [to_additive] a_one_of_b_one

run_cmd assert_ok ``a_one_iff_b_one
run_cmd assert_ok ``a_one_of_b_one
run_cmd assert_ok ``b_one_of_a_one
