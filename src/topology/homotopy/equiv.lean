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

variables {X : Type u} {Y : Type v} {Z : Type w}
variables [topological_space X] [topological_space Y] [topological_space Z]

namespace continuous_map

/--
A homotopy equivalence between topological spaces `X` and `Y` are a pair of functions
`to_fun : C(X, Y)` and `inv_fun : C(Y, X)` such that `to_fun.comp inv_fun` and `inv_fun.comp to_fun`
are both homotopic to `id`.
-/
@[ext]
structure homotopy_equiv (X : Type u) (Y : Type v) [topological_space X] [topological_space Y] :=
(to_fun : C(X, Y))
(inv_fun : C(Y, X))
(left_inv : (inv_fun.comp to_fun).homotopic id)
(right_inv : (to_fun.comp inv_fun).homotopic id)

namespace homotopy_equiv

instance : has_coe_to_fun (homotopy_equiv X Y) (λ _, X → Y) := ⟨λ h, h.to_fun⟩

@[simp]
lemma to_fun_eq_coe (h : homotopy_equiv X Y) : (h.to_fun : X → Y) = h := rfl

@[continuity]
lemma continuous (h : homotopy_equiv X Y) : continuous h := h.to_fun.continuous

/--
Any topological space is homotopy equivalent to itself.
-/
def refl (X : Type u) [topological_space X] : homotopy_equiv X X :=
{ to_fun := id,
  inv_fun := id,
  left_inv := homotopic.refl _,
  right_inv := homotopic.refl _ }

instance : inhabited (homotopy_equiv unit unit) := ⟨refl unit⟩

@[simp]
lemma coe_refl (X : Type u) [topological_space X] : ⇑(refl X) = id := rfl

/--
If `X` is homotopy equivalent to `Y`, then `Y` is homotopy equivalent to `X`.
-/
def symm (h : homotopy_equiv X Y) : homotopy_equiv Y X :=
{ to_fun := h.inv_fun,
  inv_fun := h.to_fun,
  left_inv := h.right_inv,
  right_inv := h.left_inv }

@[simp]
lemma coe_inv_fun (h : homotopy_equiv X Y) : (⇑h.inv_fun : Y → X) = ⇑h.symm := rfl

@[simp]
lemma refl_symm (X : Type u) [topological_space X] : (refl X).symm = refl X := rfl

/--
If `X` is homotopy equivalent to `Y`, and `Y` is homotopy equivalent to `Z`, then `X` is homotopy
equivalent to `Z`.
-/
def trans (h₁ : homotopy_equiv X Y) (h₂ : homotopy_equiv Y Z) : homotopy_equiv X Z :=
{ to_fun := h₂.to_fun.comp h₁.to_fun,
  inv_fun := h₁.inv_fun.comp h₂.inv_fun,
  left_inv := begin
    refine homotopic.trans _ h₁.left_inv,
    change ((h₁.inv_fun.comp h₂.inv_fun).comp (h₂.to_fun.comp h₁.to_fun)) with
      h₁.inv_fun.comp ((h₂.inv_fun.comp h₂.to_fun).comp h₁.to_fun),
    refine homotopic.hcomp _ (homotopic.refl _),
    refine homotopic.trans ((homotopic.refl _).hcomp h₂.left_inv) _,
    rw id_comp,
  end,
  right_inv := begin
    refine homotopic.trans _ h₂.right_inv,
    change ((h₂.to_fun.comp h₁.to_fun).comp (h₁.inv_fun.comp h₂.inv_fun)) with
      h₂.to_fun.comp ((h₁.to_fun.comp h₁.inv_fun).comp h₂.inv_fun),
    refine homotopic.hcomp _ (homotopic.refl _),
    refine homotopic.trans ((homotopic.refl _).hcomp h₁.right_inv) _,
    rw id_comp,
  end }

@[simp]
lemma coe_trans (h₁ : homotopy_equiv X Y) (h₂ : homotopy_equiv Y Z) :
  ⇑(h₁.trans h₂) = h₂ ∘ h₁ := rfl

lemma symm_trans (h₁ : homotopy_equiv X Y) (h₂ : homotopy_equiv Y Z) :
  (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := by ext; refl

end homotopy_equiv

end continuous_map

open continuous_map

namespace homeomorph

/--
Any homeomorphism is a homotopy equivalence.
-/
def to_homotopy_equiv (h : X ≃ₜ Y) : homotopy_equiv X Y :=
{ to_fun := ⟨h⟩,
  inv_fun := ⟨h.symm⟩,
  left_inv := by { convert homotopic.refl _, ext, simp },
  right_inv := by { convert homotopic.refl _, ext, simp } }

@[simp]
lemma coe_to_homotopy_equiv (h : X ≃ₜ Y) : ⇑(h.to_homotopy_equiv) = h := rfl

@[simp]
lemma refl_to_homotopy_equiv (X : Type u) [topological_space X] :
  (homeomorph.refl X).to_homotopy_equiv = homotopy_equiv.refl X := rfl

@[simp]
lemma symm_to_homotopy_equiv (h : X ≃ₜ Y) :
  h.symm.to_homotopy_equiv = h.to_homotopy_equiv.symm := rfl

@[simp]
lemma trans_to_homotopy_equiv (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z) :
  (h₀.trans h₁).to_homotopy_equiv = h₀.to_homotopy_equiv.trans h₁.to_homotopy_equiv := rfl

end homeomorph
