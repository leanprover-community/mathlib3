import algebra.group.to_additive

/-- Docstring -/
@[to_additive add_foo]
lemma foo (α : Type*) [has_one α] : α := 1

@[to_additive add_bar "docstring"]
lemma bar (α : Type*) [has_one α] : α := 1

/-- Docstring -/
@[to_additive add_baz "docstring"]
lemma baz (α : Type*) [has_one α] : α := 1

@[to_additive add_quuz]
lemma quux (α : Type*) [has_one α] : α := 1

open tactic
run_cmd do
  decl ← get_decl ``foo,
  res ← linter.to_additive_doc.test decl,
  -- linter complains
  guard $ res.is_some,

  decl ← get_decl ``bar,
  res ← linter.to_additive_doc.test decl,
  -- linter complains
  guard $ res.is_some,

  decl ← get_decl ``baz,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none,

  decl ← get_decl ``quux,
  res ← linter.to_additive_doc.test decl,
  -- linter is happy
  guard $ res.is_none
