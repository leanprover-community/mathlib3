/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.concrete_category.basic

/-!
# The category of pointed types

This defines `Pointed`, the category of pointed types.

## TODO

* Monoidal structure
* Upgrade `Type_to_Pointed` to an equivalence
-/

open category_theory

universes u
variables {α β : Type*}

/-- The category of pointed types. -/
structure Pointed : Type.{u + 1} :=
(X : Type.{u})
(point : X)

namespace Pointed

instance : has_coe_to_sort Pointed Type* := ⟨X⟩

attribute [protected] Pointed.X

/-- Turns a point into a pointed type. -/
def of {X : Type*} (point : X) : Pointed := ⟨X, point⟩

@[simp] lemma coe_of {X : Type*} (point : X) : ↥(of point) = X := rfl

alias of ← _root_.prod.Pointed

instance : inhabited Pointed := ⟨of ((), ())⟩

/-- Morphisms in `Pointed`. -/
@[ext] protected structure hom (X Y : Pointed.{u}) : Type u :=
(to_fun : X → Y)
(map_point : to_fun X.point = Y.point)

namespace hom

/-- The identity morphism of `X : Pointed`. -/
@[simps] def id (X : Pointed) : hom X X := ⟨id, rfl⟩

instance (X : Pointed) : inhabited (hom X X) := ⟨id X⟩

/-- Composition of morphisms of `Pointed`. -/
@[simps] def comp {X Y Z : Pointed.{u}} (f : hom X Y) (g : hom Y Z) : hom X Z :=
⟨g.to_fun ∘ f.to_fun, by rw [function.comp_apply, f.map_point, g.map_point]⟩

end hom

instance large_category : large_category Pointed :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp,
  id_comp' := λ _ _ _, hom.ext _ _ rfl,
  comp_id' := λ _ _ _, hom.ext _ _ rfl,
  assoc' := λ _ _ _ _ _ _ _, hom.ext _ _ rfl }

instance concrete_category : concrete_category Pointed :=
{ forget := { obj := Pointed.X, map := @hom.to_fun },
  forget_faithful := ⟨@hom.ext⟩ }

/-- Constructs a isomorphism between pointed types from an equivalence that preserves the point
between them. -/
@[simps] def iso.mk {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point) : α ≅ β :=
{ hom := ⟨e, he⟩,
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩,
  hom_inv_id' := Pointed.hom.ext _ _ e.symm_comp_self,
  inv_hom_id' := Pointed.hom.ext _ _ e.self_comp_symm }

end Pointed

/-- `option` as a functor from types to pointed types. This is the free functor. -/
@[simps] def Type_to_Pointed : Type.{u} ⥤ Pointed.{u} :=
{ obj := λ X, ⟨option X, none⟩,
  map := λ X Y f, ⟨option.map f, rfl⟩,
  map_id' := λ X, Pointed.hom.ext _ _ option.map_id,
  map_comp' := λ X Y Z f g, Pointed.hom.ext _ _ (option.map_comp_map _ _).symm }

/-- `Type_to_Pointed` is the free functor. -/
def Type_to_Pointed_forget_adjunction : Type_to_Pointed ⊣ forget Pointed :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, { to_fun := λ f, f.to_fun ∘ option.some,
                        inv_fun := λ f, ⟨λ o, o.elim Y.point f, rfl⟩,
                        left_inv := λ f, by { ext, cases x, exact f.map_point.symm, refl },
                        right_inv := λ f, funext $ λ _, rfl },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext, cases x; refl }, }
