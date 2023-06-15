/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import category_theory.equivalence
import order.hom.basic

/-!

# Preorders as categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We install a category instance on any preorder. This is not to be confused with the category _of_
preorders, defined in `order/category/Preorder`.

We show that monotone functions between preorders correspond to functors of the associated
categories.

## Main definitions

* `hom_of_le` and `le_of_hom` provide translations between inequalities in the preorder, and
  morphisms in the associated category.
* `monotone.functor` is the functor associated to a monotone function.

-/

universes u v

namespace preorder

open category_theory

/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ulift (plift (X ≤ Y))`.
See `category_theory.hom_of_le` and `category_theory.le_of_hom`.

See <https://stacks.math.columbia.edu/tag/00D3>.
-/
@[priority 100] -- see Note [lower instance priority]
instance small_category (α : Type u) [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans _ _ _ f.down.down g.down.down ⟩ ⟩ }

end preorder

namespace category_theory

open opposite

variables {X : Type u} [preorder X]

/--
Express an inequality as a morphism in the corresponding preorder category.
-/
def hom_of_le {x y : X} (h : x ≤ y) : x ⟶ y := ulift.up (plift.up h)

alias hom_of_le ← _root_.has_le.le.hom

@[simp] lemma hom_of_le_refl {x : X} : (le_refl x).hom = 𝟙 x := rfl
@[simp] lemma hom_of_le_comp {x y z : X} (h : x ≤ y) (k : y ≤ z) :
  h.hom ≫ k.hom = (h.trans k).hom := rfl

/--
Extract the underlying inequality from a morphism in a preorder category.
-/
lemma le_of_hom {x y : X} (h : x ⟶ y) : x ≤ y := h.down.down

alias le_of_hom ← _root_.quiver.hom.le

@[simp] lemma le_of_hom_hom_of_le {x y : X} (h : x ≤ y) : h.hom.le = h := rfl
@[simp] lemma hom_of_le_le_of_hom {x y : X} (h : x ⟶ y) : h.le.hom = h :=
by { cases h, cases h, refl, }

/-- Construct a morphism in the opposite of a preorder category from an inequality. -/
def op_hom_of_le {x y : Xᵒᵖ} (h : unop x ≤ unop y) : y ⟶ x := h.hom.op

lemma le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y ≤ unop x := h.unop.le

instance unique_to_top [order_top X] {x : X} : unique (x ⟶ ⊤) := by tidy
instance unique_from_bot [order_bot X] {x : X} : unique (⊥ ⟶ x) := by tidy

end category_theory

section

variables {X : Type u} {Y : Type v} [preorder X] [preorder Y]

/--
A monotone function between preorders induces a functor between the associated categories.
-/
def monotone.functor {f : X → Y} (h : monotone f) : X ⥤ Y :=
{ obj := f,
  map := λ x₁ x₂ g, (h g.le).hom }

@[simp] lemma monotone.functor_obj {f : X → Y} (h : monotone f) : h.functor.obj = f := rfl

end

namespace category_theory

section preorder

variables {X : Type u} {Y : Type v} [preorder X] [preorder Y]

/--
A functor between preorder categories is monotone.
-/
@[mono] lemma functor.monotone (f : X ⥤ Y) : monotone f.obj :=
λ x y hxy, (f.map hxy.hom).le

end preorder

section partial_order

variables {X : Type u} {Y : Type v} [partial_order X] [partial_order Y]

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
lemma equivalence.to_order_iso_apply (e : X ≌ Y) (x : X) :
  e.to_order_iso x = e.functor.obj x := rfl

@[simp]
lemma equivalence.to_order_iso_symm_apply (e : X ≌ Y) (y : Y) :
  e.to_order_iso.symm y = e.inverse.obj y := rfl

end partial_order

end category_theory
