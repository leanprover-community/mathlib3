/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.monotone.union
import algebra.order.group.instances

/-!
# Monotonicity of odd functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An odd function on a linear ordered additive commutative group `G` is monotone on the whole group
provided that is is monotone on `set.Ici 0`, see `monotone_of_odd_of_monotone_on_nonneg`. We also
prove versions of this lemma for `antitone`, `strict_mono`, and `strict_anti`.
-/

open set
variables {G H : Type*} [linear_ordered_add_comm_group G] [ordered_add_comm_group H]

/-- An odd function on a linear ordered additive commutative group is strictly monotone on the whole
group provided that it is strictly monotone on `set.Ici 0`. -/
lemma strict_mono_of_odd_strict_mono_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
  (h₂ : strict_mono_on f (Ici 0)) :
  strict_mono f :=
begin
  refine strict_mono_on.Iic_union_Ici (λ x hx y hy hxy, neg_lt_neg_iff.1 _) h₂,
  rw [← h₁, ← h₁],
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)
end

/-- An odd function on a linear ordered additive commutative group is strictly antitone on the whole
group provided that it is strictly antitone on `set.Ici 0`. -/
lemma strict_anti_of_odd_strict_anti_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
  (h₂ : strict_anti_on f (Ici 0)) :
  strict_anti f :=
@strict_mono_of_odd_strict_mono_on_nonneg G Hᵒᵈ _ _ _ h₁ h₂

/-- An odd function on a linear ordered additive commutative group is monotone on the whole group
provided that it is monotone on `set.Ici 0`. -/
lemma monotone_of_odd_of_monotone_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
  (h₂ : monotone_on f (Ici 0)) : monotone f :=
begin
  refine monotone_on.Iic_union_Ici (λ x hx y hy hxy, neg_le_neg_iff.1 _) h₂,
  rw [← h₁, ← h₁],
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)
end

/-- An odd function on a linear ordered additive commutative group is antitone on the whole group
provided that it is monotone on `set.Ici 0`. -/
lemma antitone_of_odd_of_monotone_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
  (h₂ : antitone_on f (Ici 0)) : antitone f :=
@monotone_of_odd_of_monotone_on_nonneg G Hᵒᵈ _ _ _ h₁ h₂
