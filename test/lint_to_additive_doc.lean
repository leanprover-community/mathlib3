import algebra.group.to_additive
import tactic.alias

/-- Docstring -/
@[to_additive add_foo]
def foo (α : Type*) [has_one α] : α := 1

@[to_additive add_bar "docstring"]
def bar (α : Type*) [has_one α] : α := 1

/-- Docstring -/
@[to_additive add_baz "docstring"]
def baz (α : Type*) [has_one α] : α := 1

@[to_additive add_quux]
def quux (α : Type*) [has_one α] : α := 1

def no_to_additive (α : Type*) [has_one α] : α := 1

open tactic
run_cmd do
  decl ← get_decl ``foo,
  res ← linter.to_additive_doc.test decl,
  -- linter complains
  guard $ res.is_some

run_cmd do
  decl ← get_decl ``bar,
  res ← linter.to_additive_doc.test decl,
  -- linter complains
  guard $ res.is_some

run_cmd do
  decl ← get_decl ``baz,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none

run_cmd do
  decl ← get_decl ``quux,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none

run_cmd do
  decl ← get_decl ``no_to_additive,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none

-- Aliases always have docstrings, so we do not want to complain if their
-- additive version do not
alias quux <- quux_alias
attribute [to_additive add_quux_alias] quux_alias

run_cmd do
  decl ← get_decl ``quux_alias,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none

-- Same for iff aliases
def a_one_iff_b_one (α : Type*) [has_one α] (a b : α) (h : a = b) : (a = 1) ↔ (b = 1) := by {subst h}
alias a_one_iff_b_one ↔ b_one_of_a_one a_one_of_b_one
attribute [to_additive] a_one_iff_b_one
attribute [to_additive] b_one_of_a_one
attribute [to_additive] a_one_of_b_one

run_cmd do
  decl ← get_decl ``a_one_iff_b_one,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none,

  decl ← get_decl ``b_one_of_a_one,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none,

  decl ← get_decl ``a_one_of_b_one,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none
