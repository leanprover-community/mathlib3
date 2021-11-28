/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.homotopy.basic

/-!

# Homotopy equivalences between topological spaces

In this file, we define homotopy equivalences between topological spaces `X` and `Y` as a pair of
functions `f : C(X, Y)` and `g : C(Y, X)` such that `f.comp g` and `g.comp f` are both homotopic
to `id`.

-/

universes u v w

structure homotopy_equiv (X : Type u) (Y : Type v) [topological_space X] [topological_space Y] :=
(to_fun : C(X, Y))
(inv_fun : C(Y, X))
(left_inv : (inv_fun.comp to_fun).homotopic continuous_map.id)
(right_inv : (to_fun.comp inv_fun).homotopic continuous_map.id)

variables {X : Type u} {Y : Type v} {Z : Type w}
variables [topological_space X] [topological_space Y] [topological_space Z]

namespace homotopy_equiv

def refl (X : Type u) [topological_space X] : homotopy_equiv X X :=
{ to_fun := continuous_map.id,
  inv_fun := continuous_map.id,
  left_inv := continuous_map.homotopic.refl _,
  right_inv := continuous_map.homotopic.refl _ }

def symm (h : homotopy_equiv X Y) : homotopy_equiv Y X :=
{ to_fun := h.inv_fun,
  inv_fun := h.to_fun,
  left_inv := h.right_inv,
  right_inv := h.left_inv }

def trans (h₁ : homotopy_equiv X Y) (h₂ : homotopy_equiv Y Z) : homotopy_equiv X Z :=
{ to_fun := h₂.to_fun.comp h₁.to_fun,
  inv_fun := h₁.inv_fun.comp h₂.inv_fun,
  left_inv := begin
    refine continuous_map.homotopic.trans _ h₁.left_inv,
    change ((h₁.inv_fun.comp h₂.inv_fun).comp (h₂.to_fun.comp h₁.to_fun)) with
      h₁.inv_fun.comp ((h₂.inv_fun.comp h₂.to_fun).comp h₁.to_fun),
    refine continuous_map.homotopic.hcomp _ (continuous_map.homotopic.refl _),
    refine continuous_map.homotopic.trans ((continuous_map.homotopic.refl _).hcomp h₂.left_inv) _,
    rw continuous_map.id_comp,
  end,
  right_inv := begin
    refine continuous_map.homotopic.trans _ h₂.right_inv,
    change ((h₂.to_fun.comp h₁.to_fun).comp (h₁.inv_fun.comp h₂.inv_fun)) with
      h₂.to_fun.comp ((h₁.to_fun.comp h₁.inv_fun).comp h₂.inv_fun),
    refine continuous_map.homotopic.hcomp _ (continuous_map.homotopic.refl _),
    refine continuous_map.homotopic.trans ((continuous_map.homotopic.refl _).hcomp h₁.right_inv) _,
    rw continuous_map.id_comp,
  end }

end homotopy_equiv

namespace homeomorph

def to_homotopy_equiv (h : X ≃ₜ Y) : homotopy_equiv X Y :=
{ to_fun := ⟨h⟩,
  inv_fun := ⟨h.symm⟩,
  left_inv := by { convert continuous_map.homotopic.refl _, ext, simp },
  right_inv := by { convert continuous_map.homotopic.refl _, ext, simp } }

end homeomorph
