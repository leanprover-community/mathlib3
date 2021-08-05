/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.matrix.basic
import algebra.char_p.basic
/-!
# Matrices in prime characteristic
-/

open matrix
variables {n : Type*} [fintype n] {R : Type*} [ring R]

instance matrix.char_p [decidable_eq n] [nonempty n] (p : ℕ) [char_p R p] :
  char_p (matrix n n R) p :=
⟨begin
  intro k,
  let scalar := (diagonal_ring_hom n R).comp (pi.ring_hom $ λ _, ring_hom.id _),
  suffices : function.injective scalar,
  { rw [← scalar.map_nat_cast k, ← scalar.map_zero, this.eq_iff, ←char_p.cast_eq_zero_iff R p k], },
  refine diagonal_injective.comp _,
  intros x y h,
  obtain ⟨i⟩ := id ‹nonempty n›,
  exact function.funext_iff.mp h i,
 end⟩
