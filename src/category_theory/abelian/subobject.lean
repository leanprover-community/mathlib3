/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.opposite
import category_theory.subobject.limits

/-!
# Equivalence between subobjects and quotients in abelian categories

-/

open category_theory category_theory.limits opposite

universes v u

noncomputable theory

variables {C : Type u} [category.{v} C] [abelian C]

namespace category_theory.abelian

def order_iso (X : C) : subobject X ≃o (subobject (op X))ᵒᵈ :=
{ to_fun := subobject.lift (λ A f hf, subobject.mk (cokernel.π f).op)
  begin
    rintros A B f g hf hg i hi,
    refine subobject.mk_eq_mk_of_comm _ _ _ _,
    { sorry, },
    { sorry, }
  end
  ,
  inv_fun := subobject.lift (λ A f hf, subobject.mk (kernel.ι f.unop)) sorry,
  left_inv :=
  begin
    apply subobject.ind,
    introsI,
    dsimp,
    sorry,
  end,
  right_inv :=
  begin
    apply subobject.ind,
    introsI,
    dsimp,
    sorry,
  end,
  map_rel_iff' :=
  begin
    apply subobject.ind₂,
    dsimp,
    sorry,
  end }

end category_theory.abelian
