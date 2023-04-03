/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.group_action.group
import group_theory.group_action.pi

/-!
# Group actions on embeddings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a `mul_action G (α ↪ β)` instance that agrees with the `mul_action G (α → β)`
instances defined by `pi.mul_action`.

Note that unlike the `pi` instance, this requires `G` to be a group.
-/

universes u v w
variables {G G' α β : Type*}

namespace function.embedding

@[to_additive function.embedding.has_vadd]
instance [group G] [mul_action G β] : has_smul G (α ↪ β) :=
⟨λ g f, f.trans (mul_action.to_perm g).to_embedding⟩

@[to_additive]
lemma smul_def [group G] [mul_action G β] (g : G) (f : α ↪ β) :
  g • f = f.trans (mul_action.to_perm g).to_embedding := rfl
@[simp, to_additive]
lemma smul_apply [group G] [mul_action G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
rfl
@[to_additive]
lemma coe_smul [group G] [mul_action G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • f := rfl

instance [group G] [group G'] [has_smul G G'] [mul_action G β] [mul_action G' β]
  [is_scalar_tower G G' β] : is_scalar_tower G G' (α ↪ β) :=
⟨λ x y z, function.embedding.ext $ λ i, smul_assoc x y (z i)⟩

@[to_additive]
instance [group G] [group G'] [mul_action G β] [mul_action G' β] [smul_comm_class G G' β] :
  smul_comm_class G G' (α ↪ β) :=
⟨λ x y z, function.embedding.ext $ λ i, smul_comm x y (z i)⟩

instance [group G] [mul_action G β] [mul_action Gᵐᵒᵖ β] [is_central_scalar G β] :
  is_central_scalar G (α ↪ β) :=
⟨λ r m, function.embedding.ext $ λ i, op_smul_eq_smul _ _⟩

@[to_additive]
instance [group G] [mul_action G β] : mul_action G (α ↪ β) :=
fun_like.coe_injective.mul_action _ coe_smul

end function.embedding
