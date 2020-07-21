import category_theory.equivalence

open category_theory

universes v₁ v₂ u₁ u₂

namespace category_theory.equivalence

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables (e : C ≌ D)

-- We need special forms of `cancel_nat_iso_hom_right(_assoc)` and `cancel_nat_iso_inv_right(_assoc)`
-- for units and counits, because the simplifier can't see that `(𝟭 C).obj X` is the same as `X`.
-- We also provide the lemmas for length four compositions, since they're occasionally useful.
-- (e.g. in proving that equivalences take monos to monos)

@[simp] lemma cancel_unit_right {X Y : C}
  (f f' : X ⟶ Y) :
  f ≫ e.unit.app Y = f' ≫ e.unit.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_unit_inv_right {X Y : C}
  (f f' : X ⟶ e.inverse.obj (e.functor.obj Y))   :
  f ≫ e.unit_inv.app Y = f' ≫ e.unit_inv.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_counit_right {X Y : D}
  (f f' : X ⟶ e.functor.obj (e.inverse.obj Y))   :
  f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_counit_inv_right {X Y : D}
  (f f' : X ⟶ Y) :
  f ≫ e.counit_inv.app Y = f' ≫ e.counit_inv.app Y ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_unit_right_assoc {W X X' Y : C}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
  f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_counit_inv_right_assoc {W X X' Y : D}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
  f ≫ g ≫ e.counit_inv.app Y = f' ≫ g' ≫ e.counit_inv.app Y ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_unit_right_assoc' {W X X' Y Y' Z : C}
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
  f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_counit_inv_right_assoc' {W X X' Y Y' Z : D}
  (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
  f ≫ g ≫ h ≫ e.counit_inv.app Z = f' ≫ g' ≫ h' ≫ e.counit_inv.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' :=
by simp only [←category.assoc, cancel_mono]

end category_theory.equivalence
