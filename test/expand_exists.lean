/-
Copyright (c) 2022 Ian Wood. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Wood
-/
import tactic.basic
import tactic.expand_exists

@[expand_exists nat_greater nat_greater_spec]
lemma nat_greater_exists (n : ℕ) : ∃ m : ℕ, n < m := ⟨n + 1, by fconstructor⟩

noncomputable def nat_greater_res : ℕ → ℕ := nat_greater
lemma nat_greater_spec_res : ∀ (n : ℕ), n < nat_greater n := nat_greater_spec

@[expand_exists dependent_type dependent_type_val dependent_type_spec]
lemma dependent_type_exists {α : Type*} (a : α) : ∃ {β : Type} (b : β), (a, b) = (a, b) :=
⟨unit, (), rfl⟩

def dependent_type_res {α : Type*} (a : α) : Type := dependent_type a
noncomputable def dependent_type_val_res {α : Type*} (a : α) : dependent_type a :=
dependent_type_val a
lemma dependent_type_spec_res
{α : Type*} (a : α) : (a, dependent_type_val a) = (a, dependent_type_val a) := dependent_type_spec a

@[expand_exists nat_greater_nosplit nat_greater_nosplit_spec,
  expand_exists nat_greater_split nat_greater_split_lt nat_greater_split_neq]
lemma nat_greater_exists₂ (n : ℕ) : ∃ m : ℕ, n < m ∧ m ≠ 0 := begin
  use n + 1,
  split,
  fconstructor,
  finish,
end

noncomputable def nat_greater_nosplit_res : ℕ → ℕ := nat_greater_nosplit
noncomputable def nat_greater_split_res : ℕ → ℕ := nat_greater_split

lemma nat_greater_nosplit_spec_res :
∀ (n : ℕ), n < nat_greater_nosplit n ∧ nat_greater_nosplit n ≠ 0 := nat_greater_nosplit_spec

lemma nat_greater_split_spec_lt_res : ∀ (n : ℕ), n < nat_greater_nosplit n := nat_greater_split_lt
lemma nat_greater_split_spec_neq_res : ∀ (n : ℕ), nat_greater_nosplit n ≠ 0 := nat_greater_split_neq
