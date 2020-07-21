import category_theory.isomorphism

open category_theory

universes v u

variables {C : Type u} [category.{v} C]

namespace category_theory.iso

/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/

@[simp] lemma cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) :
  f.hom ≫ g = f.hom ≫ g' ↔ g = g' :=
by simp only [cancel_epi]

@[simp] lemma cancel_iso_inv_left {X Y Z : C} (f : Y ≅ X) (g g' : Y ⟶ Z) :
  f.inv ≫ g = f.inv ≫ g' ↔ g = g' :=
by simp only [cancel_epi]

@[simp] lemma cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) :
  f ≫ g.hom = f' ≫ g.hom ↔ f = f' :=
by simp only [cancel_mono]

@[simp] lemma cancel_iso_inv_right {X Y Z : C} (f f' : X ⟶ Y) (g : Z ≅ Y) :
  f ≫ g.inv = f' ≫ g.inv ↔ f = f' :=
by simp only [cancel_mono]

/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/

@[simp] lemma cancel_iso_hom_right_assoc {W X X' Y Z : C}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y)
  (h : Y ≅ Z) :
  f ≫ g ≫ h.hom = f' ≫ g' ≫ h.hom ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

@[simp] lemma cancel_iso_inv_right_assoc {W X X' Y Z : C}
  (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y)
  (h : Z ≅ Y) :
  f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f' ≫ g' :=
by simp only [←category.assoc, cancel_mono]

end category_theory.iso
