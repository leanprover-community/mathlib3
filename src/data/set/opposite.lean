/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import data.opposite
import data.set.image

/-!
# The opposite of a set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/

variables {α : Type*}

open opposite

namespace set

/-- The opposite of a set `s` is the set obtained by taking the opposite of each member of `s`. -/
protected def op (s : set α) : set αᵒᵖ :=
unop ⁻¹' s

/-- The unop of a set `s` is the set obtained by taking the unop of each member of `s`. -/
protected def unop (s : set αᵒᵖ) : set α :=
op ⁻¹' s

@[simp] lemma mem_op {s : set α} {a : αᵒᵖ} : a ∈ s.op ↔ unop a ∈ s :=
iff.rfl

@[simp] lemma op_mem_op {s : set α} {a : α} : op a ∈ s.op ↔ a ∈ s :=
by rw [mem_op, unop_op]

@[simp] lemma mem_unop {s : set αᵒᵖ} {a : α} : a ∈ s.unop ↔ op a ∈ s :=
iff.rfl

@[simp] lemma unop_mem_unop {s : set αᵒᵖ} {a : αᵒᵖ} : unop a ∈ s.unop ↔ a ∈ s :=
by rw [mem_unop, op_unop]

@[simp] lemma op_unop (s : set α) : s.op.unop = s :=
ext (by simp only [mem_unop, op_mem_op, iff_self, implies_true_iff])

@[simp] lemma unop_op (s : set αᵒᵖ) : s.unop.op = s :=
ext (by simp only [mem_op, unop_mem_unop, iff_self, implies_true_iff])

/-- The members of the opposite of a set are in bijection with the members of the set itself. -/
@[simps] def op_equiv_self (s : set α) : s.op ≃ s :=
⟨λ x, ⟨unop x, x.2⟩, λ x, ⟨op x, x.2⟩, λ x, by simp, λ x, by simp⟩

/-- Taking opposites as an equivalence of powersets. -/
@[simps] def op_equiv : set α ≃ set αᵒᵖ :=
⟨set.op, set.unop, op_unop, unop_op⟩

@[simp] lemma singleton_op (x : α) : ({x} : set α).op = {op x} :=
ext $ λ y, by simpa only [mem_op, mem_singleton_iff] using unop_eq_iff_eq_op

@[simp] lemma singleton_unop (x : αᵒᵖ) : ({x} : set αᵒᵖ).unop = {unop x} :=
ext $ λ y, by simpa only [mem_unop, mem_singleton_iff] using op_eq_iff_eq_unop

@[simp] lemma singleton_op_unop (x : α) : ({op x} : set αᵒᵖ).unop = {x} :=
by simp only [singleton_unop, opposite.unop_op]

@[simp] lemma singleton_unop_op (x : αᵒᵖ) : ({unop x} : set α).op = {x} :=
by simp only [singleton_op, opposite.op_unop]

end set
