/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import data.opposite
import data.set.basic

/-!
# The opposite of a set

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/

variables {α : Type*}

open opposite

namespace set

/-- The opposite of a set `s` is the set obtained by taking the opposite of each member of `s`. -/
protected def op (s : set α) : set αᵒᵖ :=
op '' s

@[simp] lemma mem_op (s : set α) (a : αᵒᵖ) : a ∈ s.op ↔ unop a ∈ s :=
by tidy

@[simp] lemma op_mem_op (s : set α) (a : α) : op a ∈ s.op ↔ a ∈ s :=
by rw [mem_op, unop_op]

/-- The unop of a set `s` is the set obtained by taking the unop of each member of `s`. -/
protected def unop (s : set αᵒᵖ) : set α :=
unop '' s

@[simp] lemma mem_unop (s : set αᵒᵖ) (a : α) : a ∈ s.unop ↔ op a ∈ s :=
by tidy

@[simp] lemma unop_mem_unop (s : set αᵒᵖ) (a : αᵒᵖ) : unop a ∈ s.unop ↔ a ∈ s :=
by rw [mem_unop, op_unop]

@[simp] lemma op_unop (s : set α) : s.op.unop = s :=
ext (by simp only [mem_unop, op_mem_op, iff_self, implies_true_iff])

@[simp] lemma unop_op (s : set αᵒᵖ) : s.unop.op = s :=
ext (by simp only [mem_op, unop_mem_unop, iff_self, implies_true_iff])

end set
