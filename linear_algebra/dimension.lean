/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Dimension of modules and vector spaces.
-/
import linear_algebra.basic set_theory.cardinal
noncomputable theory

local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace vector_space
variables [field α] [vector_space α β]

variables (α β)
def dim : cardinal :=
cardinal.min
  (nonempty_subtype.2 (@exists_is_basis α β _ _))
  (λ b, cardinal.mk b.1)
variables {α β}

/-
theorem mk_basis {b : set β} (h : is_basis b) : cardinal.mk b = dim α β :=
begin
  cases (show ∃ b', dim α β = _, from cardinal.min_eq _ _) with b' e,
  refine quotient.sound
end
-/

end vector_space
