/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import tactic.split_ifs
import tactic.simpa
/-!
# Theorems on pi types

This file defines basic structures on Pi Types
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

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

end pi
