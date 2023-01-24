/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.pointwise.smul

/-!
# Support of an element under an action action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given an action of a group `G` on a type `α`, we say that a set `s : set α` supports an element
`a : α` if, for all `g` that fix `s` pointwise, `g` fixes `a`.

This is crucial in Fourier-Motzkin constructions.
-/

open_locale pointwise

variables {G H α β : Type*}

namespace mul_action
section has_smul
variables (G) [has_smul G α] [has_smul G β]

/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
@[to_additive "A set `s` supports `b` if `g +ᵥ b = b` whenever `g +ᵥ a = a` for all `a ∈ s`."]
def supports (s : set α) (b : β) := ∀ g : G, (∀ ⦃a⦄, a ∈ s → g • a = a) → g • b = b

variables {s t : set α} {a : α} {b : β}

@[to_additive] lemma supports_of_mem (ha : a ∈ s) : supports G s a := λ g h, h ha

variables {G}

@[to_additive] lemma supports.mono (h : s ⊆ t) (hs : supports G s b) : supports G t b :=
λ g hg, hs _ $ λ a ha, hg $ h ha

end has_smul

variables [group H] [has_smul G α] [has_smul G β] [mul_action H α] [has_smul H β]
  [smul_comm_class G H β] [smul_comm_class G H α] {s t : set α} {b : β}

-- TODO: This should work without `smul_comm_class`
@[to_additive] lemma supports.smul (g : H) (h : supports G s b) : supports G (g • s) (g • b) :=
begin
  rintro g' hg',
  rw [smul_comm, h],
  rintro a ha,
  have := set.ball_image_iff.1 hg' a ha,
  rwa [smul_comm, smul_left_cancel_iff] at this,
end

end mul_action
