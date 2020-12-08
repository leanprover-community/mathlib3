/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import tactic.split_ifs
import tactic.simpa
import algebra.group.to_additive
/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `pi.lean` files elsewhere.
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive] instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := ⟨λ _, 1⟩
@[simp, to_additive] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

@[to_additive]
instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := ⟨λ f g i, f i * g i⟩
@[simp, to_additive] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

@[to_additive] instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := ⟨λ f i, (f i)⁻¹⟩
@[simp, to_additive] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

instance has_div [Π i, has_div $ f i] : has_div (Π i : I, f i) := ⟨λ f g i, f i / g i⟩
@[simp] lemma div_apply [Π i, has_div $ f i] : (x / y) i = x i / y i := rfl

section

variables [decidable_eq I]
variables [Π i, has_zero (f i)]

/-- The function supported at `i`, with value `x` there. -/
def single (i : I) (x : f i) : Π i, f i :=
λ i', if h : i' = i then (by { subst h, exact x }) else 0

@[simp]
lemma single_eq_same (i : I) (x : f i) : single i x i = x :=
begin
  dsimp [single],
  split_ifs,
  { refl, },
  { exfalso, exact h rfl, }
end

@[simp]
lemma single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : single i x i' = 0 :=
begin
  dsimp [single],
  split_ifs with h',
  { exfalso, exact h h', },
  { refl, }
end

variables (f)

lemma single_injective (i : I) : function.injective (single i : f i → Π i, f i) :=
λ x y h, by simpa only [single, dif_pos] using congr_fun h i

end
end pi
