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

@[simp] lemma singleton_op (x : α) : ({x} : set α).op = {op x} :=
ext $ λ y, by simpa only [mem_op, mem_singleton_iff] using unop_eq_iff_eq_op

@[simp] lemma singleton_unop (x : αᵒᵖ) : ({x} : set αᵒᵖ).unop = {unop x} :=
ext $ λ y, by simpa only [mem_unop, mem_singleton_iff] using op_eq_iff_eq_unop

@[simp] lemma singleton_op_unop (x : α) : ({op x} : set αᵒᵖ).unop = {x} :=
by simp only [singleton_unop, opposite.unop_op]

@[simp] lemma singleton_unop_op (x : αᵒᵖ) : ({unop x} : set α).op = {x} :=
by simp only [singleton_op, opposite.op_unop]

end set
