/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import group_theory.group_action.defs

/-!
# Sigma instances for additive and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for arbitrary sum of additive and multiplicative actions.

## See also

* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sum`
-/

variables {ι : Type*} {M N : Type*} {α : ι → Type*}

namespace sigma

section has_smul
variables [Π i, has_smul M (α i)] [Π i, has_smul N (α i)] (a : M) (i : ι) (b : α i)
  (x : Σ i, α i)

@[to_additive sigma.has_vadd] instance : has_smul M (Σ i, α i) := ⟨λ a, sigma.map id $ λ i, (•) a⟩

@[to_additive] lemma smul_def : a • x = x.map id (λ i, (•) a) := rfl
@[simp, to_additive] lemma smul_mk : a • mk i b = ⟨i, a • b⟩ := rfl

@[to_additive] instance [has_smul M N] [Π i, is_scalar_tower M N (α i)] :
  is_scalar_tower M N (Σ i, α i) :=
⟨λ a b x, by { cases x, rw [smul_mk, smul_mk, smul_mk, smul_assoc] }⟩

@[to_additive] instance [Π i, smul_comm_class M N (α i)] : smul_comm_class M N (Σ i, α i) :=
⟨λ a b x, by { cases x, rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm] }⟩

@[to_additive] instance [Π i, has_smul Mᵐᵒᵖ (α i)] [Π i, is_central_scalar M (α i)] :
  is_central_scalar M (Σ i, α i) :=
⟨λ a x, by { cases x, rw [smul_mk, smul_mk, op_smul_eq_smul] }⟩

/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive "This is not an instance because `i` becomes a metavariable."]
protected lemma has_faithful_smul' [has_faithful_smul M (α i)] : has_faithful_smul M (Σ i, α i) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ a : α i, heq_iff_eq.1 (ext_iff.1 $ h $ mk i a).2⟩

@[to_additive] instance [nonempty ι] [Π i, has_faithful_smul M (α i)] :
  has_faithful_smul M (Σ i, α i) :=
nonempty.elim ‹_› $ λ i, sigma.has_faithful_smul' i

end has_smul

@[to_additive] instance {m : monoid M} [Π i, mul_action M (α i)] : mul_action M (Σ i, α i) :=
{ mul_smul := λ a b x, by { cases x, rw [smul_mk, smul_mk, smul_mk, mul_smul] },
  one_smul := λ x, by { cases x, rw [smul_mk, one_smul] } }

end sigma
