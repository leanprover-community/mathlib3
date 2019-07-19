/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Models and variable assignments.
-/

import logic.function tactic.basic tactic.interactive
import tactic.vampire.misc

universe u

variable {α : Type u}

namespace vampire

local notation f `₀↦` a := assign a f

def value (α : Type u) : Type u := list α → (α × Prop)

def value.default [inhabited α] : value α :=
λ as, (default α, false)

def value.eq [inhabited α] : value α
| [x, y] := (default α, x = y)
| _      := (default α, false)

def evaluate (a : α) : value α :=
λ _, (a, false)

def denote (v : value α) : α := (v []).fst

postfix  `ₑ` : 1000 := evaluate
postfix  `ᵈ` : 1000 := denote

lemma denote_evaluate (a : α) : (a ₑ)ᵈ = a := rfl

@[reducible] def value.app (v w : value α) : value α :=
λ as, v (wᵈ :: as)

local infix `⬝` := value.app

def model (α : Type u) : Type u := nat → value α

def model.default (α : Type u) [inhabited α] : model α := λ _, value.default

def model.eq (α : Type u) [inhabited α] : model α
| 0       := value.eq
| (k + 1) := value.default

@[reducible] def vas (α : Type u) : Type u := nat → α

def vas.default (α : Type u) [inhabited α] : vas α := λ _, default α

namespace model

def decr_idxs (M : model α) : model α :=
M ∘ nat.succ

end model

lemma assign_decr_idxs (M : model α) :
  (M.decr_idxs ₀↦ (M 0)) = M :=
begin
  rw function.funext_iff,
  rintro ⟨_⟩, { refl },
  simp only [model.decr_idxs, assign]
end

end vampire
