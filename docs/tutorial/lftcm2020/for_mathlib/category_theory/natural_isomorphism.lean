import category_theory.natural_isomorphism

open category_theory

universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables (F G : C ⥤ D) (α : F ≅ G)

/-!
Unfortunately we need a separate set of cancellation lemmas for components of natural isomorphisms,
because the `simp` normal form is `α.hom.app X`, rather than `α.app.hom X`.

(With the later, the morphism would be visibly part of an isomorphism, so general lemmas about
isomorphisms would apply.)

In the future, we should consider a redesign that changes this simp norm form,
but for now it breaks too many proofs.
-/

namespace category_theory.iso

@[simp] lemma cancel_nat_iso_hom_left {X : C} {Z : D} (g g' : G.obj X ⟶ Z) :
  α.hom.app X ≫ g = α.hom.app X ≫ g' ↔ g = g' :=
by simp only [cancel_epi]

@[simp] lemma cancel_nat_iso_inv_left {X : C} {Z : D} (g g' : F.obj X ⟶ Z) :
  α.inv.app X ≫ g = α.inv.app X ≫ g' ↔ g = g' :=
by simp only [cancel_epi]

@[simp] lemma cancel_nat_iso_hom_right {X : D} {Y : C} (f f' : X ⟶ F.obj Y) :
  f ≫ α.hom.app Y = f' ≫ α.hom.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_nat_iso_inv_right {X : D} {Y : C} (f f' : X ⟶ G.obj Y) :
  f ≫ α.inv.app Y = f' ≫ α.inv.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_nat_iso_hom_right_assoc {W X X' : D} {Y : C}
  (f : W ⟶ X) (g : X ⟶ F.obj Y) (f' : W ⟶ X') (g' : X' ⟶ F.obj Y)  :
  f ≫ g ≫ α.hom.app Y = f' ≫ g' ≫ α.hom.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_nat_iso_inv_right_assoc {W X X' : D} {Y : C}
  (f : W ⟶ X) (g : X ⟶ G.obj Y) (f' : W ⟶ X') (g' : X' ⟶ G.obj Y)  :
  f ≫ g ≫ α.inv.app Y = f' ≫ g' ≫ α.inv.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

end category_theory.iso
