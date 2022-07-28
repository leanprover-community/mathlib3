/-
Copyright (c) 2022 Ian Wood. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Wood
-/
import tactic.basic
import tactic.expand_exists

@[expand_exists nat_greater nat_greater_spec]
lemma nat_greater_exists (n : ℕ) : ∃ m : ℕ, n < m := ⟨n + 1, by fconstructor⟩

noncomputable example : ℕ → ℕ := nat_greater
example : ∀ (n : ℕ), n < nat_greater n := nat_greater_spec

@[expand_exists dependent_type dependent_type_val dependent_type_spec]
lemma dependent_type_exists {α : Type*} (a : α) : ∃ {β : Type} (b : β), (a, b) = (a, b) :=
⟨unit, (), rfl⟩

example {α : Type*} (a : α) : Type := dependent_type a
noncomputable example {α : Type*} (a : α) : dependent_type a := dependent_type_val a
example {α : Type*} (a : α) : (a, dependent_type_val a) = (a, dependent_type_val a) :=
dependent_type_spec a

@[expand_exists nat_greater_nosplit nat_greater_nosplit_spec,
  expand_exists nat_greater_split nat_greater_split_lt nat_greater_split_neq]
lemma nat_greater_exists₂ (n : ℕ) : ∃ m : ℕ, n < m ∧ m ≠ 0 := begin
  use n + 1,
  split,
  fconstructor,
  finish,
end

noncomputable example : ℕ → ℕ := nat_greater_nosplit
noncomputable example : ℕ → ℕ := nat_greater_split

example : ∀ (n : ℕ), n < nat_greater_nosplit n ∧ nat_greater_nosplit n ≠ 0 :=
nat_greater_nosplit_spec

example : ∀ (n : ℕ), n < nat_greater_nosplit n := nat_greater_split_lt
example : ∀ (n : ℕ), nat_greater_nosplit n ≠ 0 := nat_greater_split_neq

@[expand_exists a_doc_string="test" no_doc_string again_a_doc_string="test"]
lemma doc_string_test (n : ℕ) : ∃ (a b : ℕ), a = b := ⟨n, n, rfl⟩

noncomputable example : ℕ → ℕ := a_doc_string
noncomputable example : ℕ → ℕ := no_doc_string
example (n : ℕ) : a_doc_string n = no_doc_string n := again_a_doc_string n

namespace foo
namespace bar
inductive baz
| a : baz
| b : baz → baz

@[expand_exists in_bar _root_.foo.in_foo _root_.in_root]
lemma namespace_test (x : baz) : ∃ (y z : baz), x.b = y ∧ y = z := ⟨x.b, x.b, rfl, rfl⟩

end bar
end foo

noncomputable example : foo.bar.baz → foo.bar.baz := foo.bar.in_bar
noncomputable example : foo.bar.baz → foo.bar.baz := foo.in_foo
example (x : foo.bar.baz) : x.b = foo.bar.in_bar x ∧ foo.bar.in_bar x = foo.in_foo x := in_root x
