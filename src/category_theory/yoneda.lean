/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.hom_functor

/-!
# The Yoneda embedding

The Yoneda embedding as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
along with an instance that it is `fully_faithful`.

Also the Yoneda lemma, `yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/

namespace category_theory
open opposite

universes v₁ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C]

/--
The Yoneda embedding, as a functor from `C` into presheaves on `C`.

See https://stacks.math.columbia.edu/tag/001O.
-/
@[simps]
def yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁) :=
{ obj := λ X,
  { obj := λ Y, unop Y ⟶ X,
    map := λ Y Y' f g, f.unop ≫ g,
    map_comp' := λ _ _ _ f g, begin ext, dsimp, erw [category.assoc] end,
    map_id' := λ Y, begin ext, dsimp, erw [category.id_comp] end },
  map := λ X X' f, { app := λ Y g, g ≫ f } }

/--
The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
@[simps] def coyoneda : Cᵒᵖ ⥤ (C ⥤ Type v₁) :=
{ obj := λ X,
  { obj := λ Y, unop X ⟶ Y,
    map := λ Y Y' f g, g ≫ f,
    map_comp' := λ _ _ _ f g, begin ext1, dsimp, erw [category.assoc] end,
    map_id' := λ Y, begin ext1, dsimp, erw [category.comp_id] end },
  map := λ X X' f, { app := λ Y g, f.unop ≫ g },
  map_comp' := λ _ _ _ f g, begin ext, dsimp, erw [category.assoc] end,
  map_id' := λ X, begin ext, dsimp, erw [category.id_comp] end }

namespace yoneda

lemma obj_map_id {X Y : C} (f : op X ⟶ op Y) :
  ((@yoneda C _).obj X).map f (𝟙 X) = ((@yoneda C _).map f.unop).app (op Y) (𝟙 Y) :=
by obviously

@[simp] lemma naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y)
  {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : f ≫ α.app (op Z') h = α.app (op Z) (f ≫ h) :=
(functor_to_types.naturality _ _ α f.op h).symm

/--
The Yoneda embedding is full.

See https://stacks.math.columbia.edu/tag/001P.
-/
instance yoneda_full : full (@yoneda C _) :=
{ preimage := λ X Y f, (f.app (op X)) (𝟙 X) }

/--
The Yoneda embedding is faithful.

See https://stacks.math.columbia.edu/tag/001P.
-/
instance yoneda_faithful : faithful (@yoneda C _) :=
{ map_injective' := λ X Y f g p,
  begin
    injection p with h,
    convert (congr_fun (congr_fun h (op X)) (𝟙 X)); dsimp; simp,
  end }

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply yoneda.ext,
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C)
  (p : Π {Z : C}, (Z ⟶ X) → (Z ⟶ Y)) (q : Π {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
  (h₁ : Π {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : Π {Z : C} (f : Z ⟶ Y), p (q f) = f)
  (n : Π {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
@preimage_iso _ _ _ _ yoneda _ _ _ _
  (nat_iso.of_components (λ Z, { hom := p, inv := q, }) (by tidy))

/--
If `yoneda.map f` is an isomorphism, so was `f`.
-/
def is_iso {X Y : C} (f : X ⟶ Y) [is_iso (yoneda.map f)] : is_iso f :=
is_iso_of_fully_faithful yoneda f

end yoneda

namespace coyoneda

@[simp] lemma naturality {X Y : Cᵒᵖ} (α : coyoneda.obj X ⟶ coyoneda.obj Y)
  {Z Z' : C} (f : Z' ⟶ Z) (h : unop X ⟶ Z') : (α.app Z' h) ≫ f = α.app Z (h ≫ f) :=
begin erw [functor_to_types.naturality], refl end

instance coyoneda_full : full (@coyoneda C _) :=
{ preimage := λ X Y f, ((f.app (unop X)) (𝟙 _)).op }

instance coyoneda_faithful : faithful (@coyoneda C _) :=
{ map_injective' := λ X Y f g p,
  begin
    injection p with h,
    have t := (congr_fun (congr_fun h (unop X)) (𝟙 _)),
    simpa using congr_arg has_hom.hom.op t,
  end }

/--
If `coyoneda.map f` is an isomorphism, so was `f`.
-/
def is_iso {X Y : Cᵒᵖ} (f : X ⟶ Y) [is_iso (coyoneda.map f)] : is_iso f :=
is_iso_of_fully_faithful coyoneda f

-- No need to use Cᵒᵖ here, works with any category
/-- A Type-valued presheaf `P` is isomorphic to the composition of `P` with the
  coyoneda functor coming from `punit`. -/
@[simps] def iso_comp_punit (P : C ⥤ Type v₁) : (P ⋙ coyoneda.obj (op punit.{v₁+1})) ≅ P :=
{ hom := { app := λ X f, f punit.star},
  inv := { app := λ X a _, a } }

end coyoneda

/--
A presheaf `F` is representable if there is object `X` so `F ≅ yoneda.obj X`.

See https://stacks.math.columbia.edu/tag/001Q.
-/
-- TODO should we make this a Prop, merely asserting existence of such an object?
class representable (F : Cᵒᵖ ⥤ Type v₁) :=
(X : C)
(w : yoneda.obj X ≅ F)

end category_theory

namespace category_theory
-- For the rest of the file, we are using product categories,
-- so need to restrict to the case morphisms are in 'Type', not 'Sort'.

universes v₁ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

open opposite

variables (C : Type u₁) [category.{v₁} C]

-- We need to help typeclass inference with some awkward universe levels here.
instance prod_category_instance_1 : category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
category_theory.prod.{(max u₁ v₁) v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

instance prod_category_instance_2 : category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
category_theory.prod.{v₁ (max u₁ v₁)} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open yoneda

/--
The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yoneda_evaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
evaluation_uncurried Cᵒᵖ (Type v₁) ⋙ ulift_functor.{u₁}

@[simp] lemma yoneda_evaluation_map_down
  (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (x : (yoneda_evaluation C).obj P) :
  ((yoneda_evaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) := rfl

/--
The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yoneda_pairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ functor.hom (Cᵒᵖ ⥤ Type v₁)

@[simp] lemma yoneda_pairing_map
  (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yoneda_pairing C).obj P) :
  (yoneda_pairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 := rfl

/--
The Yoneda lemma asserts that that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See https://stacks.math.columbia.edu/tag/001P.
-/
def yoneda_lemma : yoneda_pairing C ≅ yoneda_evaluation C :=
{ hom :=
  { app := λ F x, ulift.up ((x.app F.1) (𝟙 (unop F.1))),
    naturality' :=
    begin
      intros X Y f, ext, dsimp,
      erw [category.id_comp, ←functor_to_types.naturality],
      simp only [category.comp_id, yoneda_obj_map],
    end },
  inv :=
  { app := λ F x,
    { app := λ X a, (F.2.map a.op) x.down,
      naturality' :=
      begin
        intros X Y f, ext, dsimp,
        rw [functor_to_types.map_comp_apply]
      end },
    naturality' :=
    begin
      intros X Y f, ext, dsimp,
      rw [←functor_to_types.naturality, functor_to_types.map_comp_apply]
    end },
  hom_inv_id' :=
  begin
    ext, dsimp,
    erw [←functor_to_types.naturality,
         obj_map_id],
    simp only [yoneda_map_app, has_hom.hom.unop_op],
    erw [category.id_comp],
  end,
  inv_hom_id' :=
  begin
    ext, dsimp,
    rw [functor_to_types.map_id_apply]
  end }.

variables {C}

/--
The isomorphism between `yoneda.obj X ⟶ F` and `F.obj (op X)`
(we need to insert a `ulift` to get the universes right!)
given by the Yoneda lemma.
-/
@[simp] def yoneda_sections (X : C) (F : Cᵒᵖ ⥤ Type v₁) :
  (yoneda.obj X ⟶ F) ≅ ulift.{u₁} (F.obj (op X)) :=
(yoneda_lemma C).app (op X, F)

/--
We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yoneda_equiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) :=
(yoneda_sections X F).to_equiv.trans equiv.ulift

lemma yoneda_equiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) :
  F.map g.op (yoneda_equiv f) = yoneda_equiv (yoneda.map g ≫ f) :=
begin
  change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g),
  rw ← f.naturality,
  dsimp,
  simp,
end

@[simp]
lemma yoneda_equiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
  yoneda_equiv f = f.app (op X) (𝟙 X) :=
rfl

@[simp]
lemma yoneda_equiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X))
  (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
  (yoneda_equiv.symm x).app Y f = F.map f.op x :=
rfl

/--
When `C` is a small category, we can restate the isomorphism from `yoneda_sections`
without having to change universes.
-/
def yoneda_sections_small {C : Type u₁} [small_category C] (X : C)
  (F : Cᵒᵖ ⥤ Type u₁) :
  (yoneda.obj X ⟶ F) ≅ F.obj (op X) :=
yoneda_sections X F ≪≫ ulift_trivial _

@[simp]
lemma yoneda_sections_small_hom {C : Type u₁} [small_category C] (X : C)
  (F : Cᵒᵖ ⥤ Type u₁) (f : yoneda.obj X ⟶ F) :
  (yoneda_sections_small X F).hom f = f.app _ (𝟙 _) :=
rfl

@[simp]
lemma yoneda_sections_small_inv_app_apply {C : Type u₁} [small_category C] (X : C)
  (F : Cᵒᵖ ⥤ Type u₁) (t : F.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
  ((yoneda_sections_small X F).inv t).app Y f = F.map f.op t :=
rfl

end category_theory
