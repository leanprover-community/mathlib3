/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homotopy

/-!
# Null homotopic chain complex maps

-/

open category_theory
open category_theory.category

namespace chain_complex

variables {V : Type*} [category V] [preadditive V]

/-- Given a sequence h of morphisms `C_n ⟶ D_{n+1}`, this is the chain
complex morphism C ⟶ D given by the formula `dh+hd`. -/
@[simps]
def null_homotopic_map {C D : chain_complex V ℕ}
  (h : Π (n : ℕ), C.X n ⟶ D.X (n+1)) : C ⟶ D :=
{ f := (λ n, by
  { cases n,
    exact h 0 ≫ D.d 1 0,
    exact h (n+1) ≫ D.d (n+2) (n+1) + C.d (n+1) n ≫ h n, }),
  comm' := λ i j, by
  { rw complex_shape.down_rel,
    intro hij,
    cases j; rw ← hij,
    { simp only [limits.comp_zero, nat.rec_add_one,
      homological_complex.d_comp_d, preadditive.add_comp, zero_add, assoc], },
    { simp only [limits.comp_zero, nat.rec_add_one, add_zero, limits.zero_comp,
        homological_complex.d_comp_d, preadditive.add_comp,
        preadditive.comp_add, zero_add, homological_complex.d_comp_d_assoc,
        assoc], }, }, }

/-- Morphisms constructed by `null_homotopic_map` are homotopic to the zero map. -/
@[simps]
def null_homotopy {C D : chain_complex V ℕ}
  (h : Π (n : ℕ), C.X n ⟶ D.X (n+1)) :
  homotopy (null_homotopic_map h) 0 :=
{ hom := λ i j, dite (i+1=j)
    (λ hij, h i ≫ (eq_to_hom (by { congr, assumption, }) : D.X (i+1) ⟶ D.X j))
    (λ _, 0),
  zero' := λ i j hij, begin
    rw [dite_eq_right_iff],
    intro hij',
    exfalso,
    exact hij hij',
  end,
  comm := λ n, begin
    cases n,
    { tidy, },
    { tidy, apply add_comm, }
  end }

end chain_complex

