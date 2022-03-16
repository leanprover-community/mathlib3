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

## Main definitions

- `continuous_map.homotopy_equiv` is the type of homotopy equivalences between topological spaces.

## Notation

We introduce the notation `X ≃ₕ Y` for `continuous_map.homotopy_equiv X Y` in the `continuous_map`
locale.

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
(left_inv : (inv_fun.comp to_fun).homotopic (continuous_map.id X))
(right_inv : (to_fun.comp inv_fun).homotopic (continuous_map.id Y))

localized "infix ` ≃ₕ `:25 := continuous_map.homotopy_equiv" in continuous_map

namespace homotopy_equiv

instance : has_coe_to_fun (homotopy_equiv X Y) (λ _, X → Y) := ⟨λ h, h.to_fun⟩

@[simp]
lemma to_fun_eq_coe (h : homotopy_equiv X Y) : (h.to_fun : X → Y) = h := rfl

@[continuity]
lemma continuous (h : homotopy_equiv X Y) : continuous h := h.to_fun.continuous

end homotopy_equiv

end continuous_map

open_locale continuous_map

namespace homeomorph

/--
Any homeomorphism is a homotopy equivalence.
-/
def to_homotopy_equiv (h : X ≃ₜ Y) : X ≃ₕ Y :=
{ to_fun := ⟨h⟩,
  inv_fun := ⟨h.symm⟩,
  left_inv := by { convert continuous_map.homotopic.refl _, ext, simp },
  right_inv := by { convert continuous_map.homotopic.refl _, ext, simp } }

@[simp]
lemma coe_to_homotopy_equiv (h : X ≃ₜ Y) : ⇑(h.to_homotopy_equiv) = h := rfl

end homeomorph

namespace continuous_map

namespace homotopy_equiv

/--
If `X` is homotopy equivalent to `Y`, then `Y` is homotopy equivalent to `X`.
-/
def symm (h : X ≃ₕ Y) : Y ≃ₕ X :=
{ to_fun := h.inv_fun,
  inv_fun := h.to_fun,
  left_inv := h.right_inv,
  right_inv := h.left_inv }

@[simp]
lemma coe_inv_fun (h : homotopy_equiv X Y) : (⇑h.inv_fun : Y → X) = ⇑h.symm := rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (h : X ≃ₕ Y) : X → Y := h
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.symm_apply (h : X ≃ₕ Y) : Y → X := h.symm

initialize_simps_projections homotopy_equiv (to_fun_to_fun -> apply,
  inv_fun_to_fun -> symm_apply, -to_fun, -inv_fun)

/--
Any topological space is homotopy equivalent to itself.
-/
@[simps]
def refl (X : Type u) [topological_space X] : X ≃ₕ X :=
(homeomorph.refl X).to_homotopy_equiv

instance : inhabited (homotopy_equiv unit unit) := ⟨refl unit⟩

/--
If `X` is homotopy equivalent to `Y`, and `Y` is homotopy equivalent to `Z`, then `X` is homotopy
equivalent to `Z`.
-/
@[simps]
def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z :=
{ to_fun := h₂.to_fun.comp h₁.to_fun,
  inv_fun := h₁.inv_fun.comp h₂.inv_fun,
  left_inv := begin
    refine homotopic.trans _ h₁.left_inv,
    change ((h₁.inv_fun.comp h₂.inv_fun).comp (h₂.to_fun.comp h₁.to_fun)) with
      h₁.inv_fun.comp ((h₂.inv_fun.comp h₂.to_fun).comp h₁.to_fun),
    refine homotopic.hcomp _ (homotopic.refl _),
    refine homotopic.trans ((homotopic.refl _).hcomp h₂.left_inv) _,
    -- simp,
    rw continuous_map.id_comp,
  end,
  right_inv := begin
    refine homotopic.trans _ h₂.right_inv,
    change ((h₂.to_fun.comp h₁.to_fun).comp (h₁.inv_fun.comp h₂.inv_fun)) with
      h₂.to_fun.comp ((h₁.to_fun.comp h₁.inv_fun).comp h₂.inv_fun),
    refine homotopic.hcomp _ (homotopic.refl _),
    refine homotopic.trans ((homotopic.refl _).hcomp h₁.right_inv) _,
    rw id_comp,
  end }

lemma symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) :
  (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := by ext; refl

end homotopy_equiv

end continuous_map

open continuous_map

namespace homeomorph

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
