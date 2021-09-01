/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/

import category_theory.category.Cat
import category_theory.category.default
import order.category.Preorder

/-!

# Preorders as categories

We install a category instance on any preorder. This is not to be confused with the category _of_
preorders, defined in `order/category/Preorder`.

We show that monotone functions between preorders correspond to functors of the associated
categories. Furthermore, galois connections correspond to adjoint functors.

## Main definitions

* `hom_of_le` and `le_of_hom` provide translations between inequalities in the preorder, and
  morphisms in the associated category.
* `monotone.functor` is the functor associated to a monotone function.
* `galois_connection.adjunction` is the adjunction associated to a galois connection.
* `Preorder_to_Cat` is the functor embedding the category of preorders into `Cat`.

-/

universes u v

namespace preorder

open category_theory

/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ulift (plift (X ≤ Y))`.
See `category_theory.hom_of_le` and `category_theory.le_of_hom`.

See https://stacks.math.columbia.edu/tag/00D3.
-/
@[priority 100] -- see Note [lower instance priority]
instance small_category (α : Type u) [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans _ _ _ f.down.down g.down.down ⟩ ⟩ }

end preorder

namespace category_theory

variables {α : Type u} [preorder α]

/--
Express an inequality as a morphism in the corresponding preorder category.
-/
def hom_of_le {U V : α} (h : U ≤ V) : U ⟶ V := ulift.up (plift.up h)

alias hom_of_le ← has_le.le.hom

@[simp] lemma hom_of_le_refl {U : α} : (le_refl U).hom = 𝟙 U := rfl
@[simp] lemma hom_of_le_comp {U V W : α} (h : U ≤ V) (k : V ≤ W) :
  h.hom ≫ k.hom = (h.trans k).hom := rfl

/--
Extract the underlying inequality from a morphism in a preorder category.
-/
lemma le_of_hom {U V : α} (h : U ⟶ V) : U ≤ V := h.down.down

alias le_of_hom ← quiver.hom.le

@[simp] lemma le_of_hom_hom_of_le {a b : α} (h : a ≤ b) : h.hom.le = h := rfl
@[simp] lemma hom_of_le_le_of_hom {a b : α} (h : a ⟶ b) : h.le.hom = h :=
by { cases h, cases h, refl, }

lemma iso.to_eq {x y : X} (f : x ≅ y) : x = y := le_antisymm f.hom.le f.inv.le

/--
A categorical equivalence between partial orders is just an order isomorphism.
-/
def equivalence.to_order_iso (e : X ≌ Y) : X ≃o Y :=
{ to_fun := e.functor.obj,
  inv_fun := e.inverse.obj,
  left_inv := λ a, (e.unit_iso.app a).to_eq.symm,
  right_inv := λ b, (e.counit_iso.app b).to_eq,
  map_rel_iff' := λ a a',
    ⟨λ h, ((equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (equivalence.unit_inv e).app a').le,
     λ (h : a ≤ a'), (e.functor.map h.hom).le⟩, }

-- `@[simps]` on `equivalence.to_order_iso` produces lemmas that fail the `simp_nf` linter,
-- so we provide them by hand:
@[simp]
lemma equivalence.to_order_iso_apply (e : X ≌ Y) (a : α) :
  e.to_order_iso a = e.functor.obj a := rfl

@[simp]
lemma equivalence.to_order_iso_symm_apply (e : X ≌ Y) (b : β) :
  e.to_order_iso.symm b = e.inverse.obj b := rfl

end category_theory

variables {X : Type u} {Y : Type v} [preorder X] [preorder Y]

/--
A monotone function between preorders induces a functor between the associated categories.
-/
def monotone.functor {f : X → Y} (h : monotone f) : X ⥤ Y :=
{ obj := f,
  map := λ x₁ x₂ g, (h g.le).hom }

@[simp] lemma monotone.functor_obj {f : X → Y} (h : monotone f) : h.functor.obj = f := rfl

/--
A galois connection between preorders induces an adjunction between the associated categories.
-/
def galois_connection.adjunction {l : X → Y} {u : Y → X} (gc : galois_connection l u) :
  gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
category_theory.adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, ⟨λ f, (gc.le_u f.le).hom, λ f, (gc.l_le f.le).hom, by tidy, by tidy⟩ }

namespace category_theory

/--
A functor between preorder categories is monotone.
-/
@[mono] lemma functor.monotone (f : X ⥤ Y) : monotone f.obj :=
λ x y hxy, (f.map hxy.hom).le

/--
An adjunction between preorder categories induces a galois connection.
-/
lemma galois_connection_of_adjunction {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) :
  galois_connection L.obj R.obj :=
λ x y, ⟨λ h, ((adj.hom_equiv x y).to_fun h.hom).le, λ h, ((adj.hom_equiv x y).inv_fun h.hom).le⟩

/--
The embedding of `Preorder` into `Cat`.
-/
@[simps]
def Preorder_to_Cat : Preorder ⥤ Cat :=
{ obj := λ X, Cat.of X.1,
  map := λ X Y f, f.monotone.functor,
  map_id' := λ X, begin apply category_theory.functor.ext, tidy end,
  map_comp' := λ X Y Z f g, begin apply category_theory.functor.ext, tidy end }

instance : faithful Preorder_to_Cat :=
{ map_injective' := λ X Y f g h, begin ext x, exact functor.congr_obj h x end }

instance : full Preorder_to_Cat :=
{ preimage := λ X Y f, ⟨f.obj, monotone_of_functor f⟩,
  witness' := λ X Y f, begin apply category_theory.functor.ext, tidy end }

end category_theory
