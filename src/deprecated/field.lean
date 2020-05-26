/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import deprecated.ring
import algebra.field

/-!
# Field properties of unbundled ring homomorphisms (deprecated)
-/

namespace is_ring_hom
open ring_hom (of)

section
variables {α : Type*} {β : Type*} [division_ring α] [division_ring β]
variables (f : α → β) [is_ring_hom f] {x y : α}

lemma map_ne_zero : f x ≠ 0 ↔ x ≠ 0 := (of f).map_ne_zero

lemma map_eq_zero : f x = 0 ↔ x = 0 := (of f).map_eq_zero

lemma map_inv : f x⁻¹ = (f x)⁻¹ := (of f).map_inv

lemma map_div : f (x / y) = f x / f y := (of f).map_div

lemma injective : function.injective f := (of f).injective

end

end is_ring_hom
