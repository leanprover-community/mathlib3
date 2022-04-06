/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.structured_arrow
import category_theory.groupoid
import category_theory.punit

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type`, an object of `F.elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction, so this is mostly just a
more convenient API. We prove the equivalence in
`category_theory.category_of_elements.structured_arrow_equivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/

namespace category_theory

universes w v u
variables {C : Type u} [category.{v} C]

/--
The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
@[nolint has_inhabited_instance]
def functor.elements (F : C ⥤ Type w) := (Σ c : C, F.obj c)

/-- The category structure on `F.elements`, for `F : C ⥤ Type`.
    A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.
 -/
instance category_of_elements (F : C ⥤ Type w) : category.{v} F.elements :=
{ hom := λ p q, { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 },
  id := λ p, ⟨𝟙 p.1, by obviously⟩,
  comp := λ p q r f g, ⟨f.val ≫ g.val, by obviously⟩ }

namespace category_of_elements

@[ext]
lemma ext (F : C ⥤ Type w) {x y : F.elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
subtype.ext_val w

@[simp] lemma comp_val {F : C ⥤ Type w} {p q r : F.elements} {f : p ⟶ q} {g : q ⟶ r} :
  (f ≫ g).val = f.val ≫ g.val := rfl

@[simp] lemma id_val {F : C ⥤ Type w} {p : F.elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 := rfl

end category_of_elements

noncomputable
instance groupoid_of_elements {G : Type u} [groupoid.{v} G] (F : G ⥤ Type w) :
  groupoid F.elements :=
{ inv := λ p q f, ⟨inv f.val,
      calc F.map (inv f.val) q.2 = F.map (inv f.val) (F.map f.val p.2) : by rw f.2
                             ... = (F.map f.val ≫ F.map (inv f.val)) p.2 : by simp
                             ... = p.2 : by {rw ←functor.map_comp, simp}⟩, }

namespace category_of_elements
variable (F : C ⥤ Type w)

/-- The functor out of the category of elements which forgets the element. -/
@[simps]
def π : F.elements ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.val }

/--
A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.elements ⥤ F₂.elements :=
{ obj := λ t, ⟨t.1, α.app t.1 t.2⟩,
  map := λ t₁ t₂ k, ⟨k.1, by simpa [←k.2] using (functor_to_types.naturality _ _ α k.1 t₁.2).symm⟩ }

@[simp] lemma map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ := rfl

/-- The forward direction of the equivalence `F.elements ≅ (*, F)`. -/
def to_structured_arrow : F.elements ⥤ structured_arrow punit F :=
{ obj := λ X, structured_arrow.mk (λ _, X.2),
  map := λ X Y f, structured_arrow.hom_mk f.val (by tidy) }

@[simp] lemma to_structured_arrow_obj (X) :
  (to_structured_arrow F).obj X = { left := punit.star, right := X.1, hom := λ _, X.2 } := rfl
@[simp] lemma to_comma_map_right {X Y} (f : X ⟶ Y) :
  ((to_structured_arrow F).map f).right = f.val := rfl

/-- The reverse direction of the equivalence `F.elements ≅ (*, F)`. -/
def from_structured_arrow : structured_arrow punit F ⥤ F.elements :=
{ obj := λ X, ⟨X.right, X.hom (punit.star)⟩,
  map := λ X Y f, ⟨f.right, congr_fun f.w'.symm punit.star⟩ }

@[simp] lemma from_structured_arrow_obj (X) :
  (from_structured_arrow F).obj X = ⟨X.right, X.hom (punit.star)⟩ := rfl
@[simp] lemma from_structured_arrow_map {X Y} (f : X ⟶ Y) :
  (from_structured_arrow F).map f = ⟨f.right, congr_fun f.w'.symm punit.star⟩ := rfl

/-- The equivalence between the category of elements `F.elements`
    and the comma category `(*, F)`. -/
@[simps]
def structured_arrow_equivalence : F.elements ≌ structured_arrow punit F :=
equivalence.mk (to_structured_arrow F) (from_structured_arrow F)
  (nat_iso.of_components (λ X, eq_to_iso (by tidy)) (by tidy))
  (nat_iso.of_components
    (λ X, { hom := { right := 𝟙 _ }, inv := { right := 𝟙 _ } })
    (by tidy))

open opposite

/--
The forward direction of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)`,
given by `category_theory.yoneda_sections`.
-/
@[simps]
def to_costructured_arrow (F : Cᵒᵖ ⥤ Type v) : (F.elements)ᵒᵖ ⥤ costructured_arrow yoneda F :=
{ obj := λ X, costructured_arrow.mk
    ((yoneda_sections (unop (unop X).fst) F).inv (ulift.up (unop X).2)),
  map := λ X Y f,
  begin
    fapply costructured_arrow.hom_mk,
    exact f.unop.val.unop,
    ext y,
    simp only [costructured_arrow.mk_hom_eq_self, yoneda_map_app, functor_to_types.comp, op_comp,
      yoneda_sections_inv_app, functor_to_types.map_comp_apply, quiver.hom.op_unop,
      subtype.val_eq_coe],
    congr,
    exact f.unop.2,
  end }

/--
The reverse direction of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)`,
given by `category_theory.yoneda_equiv`.
-/
@[simps]
def from_costructured_arrow (F : Cᵒᵖ ⥤ Type v) : (costructured_arrow yoneda F)ᵒᵖ ⥤ F.elements :=
{ obj := λ X, ⟨op (unop X).1, yoneda_equiv.1 (unop X).3⟩,
  map := λ X Y f, ⟨f.unop.1.op,
  begin
    convert (congr_fun ((unop X).hom.naturality f.unop.left.op) (𝟙 _)).symm,
    simp only [equiv.to_fun_as_coe, quiver.hom.unop_op, yoneda_equiv_apply,
      types_comp_apply, category.comp_id, yoneda_obj_map],
    have : yoneda.map f.unop.left ≫ (unop X).hom = (unop Y).hom,
    { convert f.unop.3, erw category.comp_id },
    erw ← this,
    simp only [yoneda_map_app, functor_to_types.comp],
    erw category.id_comp
  end ⟩}

@[simp]
lemma from_costructured_arrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
  (from_costructured_arrow F).obj (op (costructured_arrow.mk f)) = ⟨op X, yoneda_equiv.1 f⟩ := rfl

/-- The unit of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
lemma from_to_costructured_arrow_eq (F : Cᵒᵖ ⥤ Type v) :
 (to_costructured_arrow F).right_op ⋙ from_costructured_arrow F = 𝟭 _ :=
begin
  apply functor.ext,
  intros X Y f,
  have : ∀ {a b : F.elements} (H : a = b),
    ↑(eq_to_hom H) = eq_to_hom (show a.fst = b.fst, by { cases H, refl }) :=
    λ _ _ H, by { cases H, refl },
  ext, simp[this],
  tidy
end

/-- The counit of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
lemma to_from_costructured_arrow_eq (F : Cᵒᵖ ⥤ Type v) :
  (from_costructured_arrow F).right_op ⋙ to_costructured_arrow F = 𝟭 _ :=
begin
  apply functor.hext,
  { intro X, cases X, cases X_right,
    simp only [functor.id_obj, functor.right_op_obj,
      to_costructured_arrow_obj, functor.comp_obj, costructured_arrow.mk],
    congr,
    ext x f,
    convert congr_fun (X_hom.naturality f.op).symm (𝟙 X_left),
    simp only [quiver.hom.unop_op, yoneda_obj_map],
    erw category.comp_id },
  intros X Y f,
  cases X, cases Y, cases f, cases X_right, cases Y_right,
  simp[costructured_arrow.hom_mk],
  delta costructured_arrow.mk,
  congr,
  { ext x f,
    convert congr_fun (X_hom.naturality f.op).symm (𝟙 X_left),
    simp only [quiver.hom.unop_op, category_theory.yoneda_obj_map],
    erw category.comp_id },
  { ext x f,
    convert congr_fun (Y_hom.naturality f.op).symm (𝟙 Y_left),
    simp only [quiver.hom.unop_op, category_theory.yoneda_obj_map],
    erw category.comp_id },
  simp,
  exact proof_irrel_heq _ _,
end


/-- The equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps] def costructured_arrow_yoneda_equivalence (F : Cᵒᵖ ⥤ Type v) :
  (F.elements)ᵒᵖ ≌ costructured_arrow yoneda F :=
equivalence.mk (to_costructured_arrow F) (from_costructured_arrow F).right_op
  (nat_iso.op (eq_to_iso (from_to_costructured_arrow_eq F)))
  (eq_to_iso $ to_from_costructured_arrow_eq F)

/--
The equivalence `(-.elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorphism of functors.
-/
lemma costructured_arrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v}
  (α : F₁ ⟶ F₂) : (map α).op ⋙ to_costructured_arrow F₂ =
    to_costructured_arrow F₁ ⋙ costructured_arrow.map α :=
begin
  fapply functor.ext,
  { intro X,
    simp only [costructured_arrow.map_mk, to_costructured_arrow_obj,
      functor.op_obj, functor.comp_obj],
    congr,
    ext x f,
    simpa using congr_fun (α.naturality f.op).symm (unop X).snd },
  { intros X Y f, ext,
    have : ∀ {F : Cᵒᵖ ⥤ Type v} {a b : costructured_arrow yoneda F} (H : a = b),
      comma_morphism.left (eq_to_hom H) = eq_to_hom (show a.left = b.left, by { cases H, refl }) :=
      λ _ _ _ H, by { cases H, refl },
    simp [this] }
end

end category_of_elements
end category_theory
