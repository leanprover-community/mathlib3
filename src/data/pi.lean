/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import tactic.split_ifs
import tactic.simpa
import tactic.congr
import algebra.group.to_additive
/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `pi.lean` files elsewhere.
-/

universes u v₁ v₂ v₃
variable {I : Type u}     -- The indexing type
-- The families of types already equipped with instances
variables {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}
variables (x y : Π i, f i) (i : I)

namespace pi

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive] instance has_one [∀ i, has_one $ f i] :
  has_one (Π i : I, f i) :=
⟨λ _, 1⟩
@[simp, to_additive] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

@[to_additive] lemma one_def [Π i, has_one $ f i] : (1 : Π i, f i) = λ i, 1 := rfl

@[to_additive]
instance has_mul [∀ i, has_mul $ f i] :
  has_mul (Π i : I, f i) :=
⟨λ f g i, f i * g i⟩
@[simp, to_additive] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

@[to_additive] instance has_inv [∀ i, has_inv $ f i] :
  has_inv (Π i : I, f i) :=
  ⟨λ f i, (f i)⁻¹⟩
@[simp, to_additive] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

@[to_additive] instance has_div [Π i, has_div $ f i] :
  has_div (Π i : I, f i) :=
⟨λ f g i, f i / g i⟩
@[simp, to_additive] lemma div_apply [Π i, has_div $ f i] : (x / y) i = x i / y i := rfl
@[to_additive] lemma div_def [Π i, has_div $ f i] : x / y = λ i, x i / y i := rfl

section

variables [decidable_eq I]
variables [Π i, has_zero (f i)] [Π i, has_zero (g i)] [Π i, has_zero (h i)]

/-- The function supported at `i`, with value `x` there. -/
def single (i : I) (x : f i) : Π i, f i :=
function.update 0 i x

@[simp]
lemma single_eq_same (i : I) (x : f i) : single i x i = x :=
function.update_same i x _

@[simp]
lemma single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : single i x i' = 0 :=
function.update_noteq h x _

lemma apply_single (f' : Π i, f i → g i) (hf' : ∀ i, f' i 0 = 0) (i : I) (x : f i) (j : I):
  f' j (single i x j) = single i (f' i x) j :=
by simpa only [pi.zero_apply, hf', single] using function.apply_update f' 0 i x j

lemma apply_single₂ (f' : Π i, f i → g i → h i) (hf' : ∀ i, f' i 0 0 = 0)
  (i : I) (x : f i) (y : g i) (j : I):
  f' j (single i x j) (single i y j) = single i (f' i x y) j :=
begin
  by_cases h : j = i,
  { subst h, simp only [single_eq_same], },
  { simp only [h, single_eq_of_ne, ne.def, not_false_iff, hf'], },
end

variables (f)

lemma single_injective (i : I) : function.injective (single i : f i → Π i, f i) :=
function.update_injective _ i

end
end pi

lemma subsingleton.pi_single_eq {α : Type*} [decidable_eq I] [subsingleton I] [has_zero α]
  (i : I) (x : α) :
  pi.single i x = λ _, x :=
funext $ λ j, by rw [subsingleton.elim j i, pi.single_eq_same]
