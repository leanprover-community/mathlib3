/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.hom_functor
import category_theory.currying
import category_theory.products.basic

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

universes v₁ u₁ u₂-- morphism levels before object levels. See note [category_theory universes].

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
    map := λ Y Y' f g, g ≫ f },
  map := λ X X' f, { app := λ Y g, f.unop ≫ g } }

namespace yoneda

lemma obj_map_id {X Y : C} (f : op X ⟶ op Y) :
  (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) :=
by { dsimp, simp }

@[simp] lemma naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y)
  {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : f ≫ α.app (op Z') h = α.app (op Z) (f ≫ h) :=
(functor_to_types.naturality _ _ α f.op h).symm

/--
The Yoneda embedding is full.

See https://stacks.math.columbia.edu/tag/001P.
-/
instance yoneda_full : full (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁) :=
{ preimage := λ X Y f, f.app (op X) (𝟙 X) }

/--
The Yoneda embedding is faithful.

See https://stacks.math.columbia.edu/tag/001P.
-/
instance yoneda_faithful : faithful (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁) :=
{ map_injective' := λ X Y f g p, by convert (congr_fun (congr_app p (op X)) (𝟙 X)); dsimp; simp }

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
lemma is_iso {X Y : C} (f : X ⟶ Y) [is_iso (yoneda.map f)] : is_iso f :=
is_iso_of_fully_faithful yoneda f

end yoneda

namespace coyoneda

@[simp] lemma naturality {X Y : Cᵒᵖ} (α : coyoneda.obj X ⟶ coyoneda.obj Y)
  {Z Z' : C} (f : Z' ⟶ Z) (h : unop X ⟶ Z') : (α.app Z' h) ≫ f = α.app Z (h ≫ f) :=
(functor_to_types.naturality _ _ α f h).symm

instance coyoneda_full : full (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁) :=
{ preimage := λ X Y f, (f.app _ (𝟙 X.unop)).op }

instance coyoneda_faithful : faithful (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁) :=
{ map_injective' := λ X Y f g p,
  begin
    have t := congr_fun (congr_app p X.unop) (𝟙 _),
    simpa using congr_arg quiver.hom.op t,
  end }

/--
If `coyoneda.map f` is an isomorphism, so was `f`.
-/
lemma is_iso {X Y : Cᵒᵖ} (f : X ⟶ Y) [is_iso (coyoneda.map f)] : is_iso f :=
is_iso_of_fully_faithful coyoneda f

/-- The identity functor on `Type` is isomorphic to the coyoneda functor coming from `punit`. -/
def punit_iso : coyoneda.obj (opposite.op punit) ≅ 𝟭 (Type v₁) :=
nat_iso.of_components
  (λ X, { hom := λ f, f ⟨⟩, inv := λ x _, x })
  (by tidy)

end coyoneda

namespace functor


/--
A functor `F : Cᵒᵖ ⥤ Type v₁` is representable if there is object `X` so `F ≅ yoneda.obj X`.

See https://stacks.math.columbia.edu/tag/001Q.
-/
class representable (F : Cᵒᵖ ⥤ Type v₁) : Prop :=
(has_representation : ∃ X (f : yoneda.obj X ⟶ F), is_iso f)

instance {X : C} : representable (yoneda.obj X) :=
{ has_representation := ⟨X, 𝟙 _, infer_instance⟩ }

/--
A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.

See https://stacks.math.columbia.edu/tag/001Q.
-/
class corepresentable (F : C ⥤ Type v₁) : Prop :=
(has_corepresentation : ∃ X (f : coyoneda.obj X ⟶ F), is_iso f)

instance {X : Cᵒᵖ} : corepresentable (coyoneda.obj X) :=
{ has_corepresentation := ⟨X, 𝟙 _, infer_instance⟩ }

-- instance : corepresentable (𝟭 (Type v₁)) :=
-- corepresentable_of_nat_iso (op punit) coyoneda.punit_iso

section representable
variables (F : Cᵒᵖ ⥤ Type v₁)
variable [F.representable]

/-- The representing object for the representable functor `F`. -/
noncomputable def repr_X : C :=
(representable.has_representation : ∃ X (f : _ ⟶ F), _).some

/-- The (forward direction of the) isomorphism witnessing `F` is representable. -/
noncomputable def repr_f : yoneda.obj F.repr_X ⟶ F :=
representable.has_representation.some_spec.some

/--
The representing element for the representable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def repr_x : F.obj (op F.repr_X) :=
F.repr_f.app (op F.repr_X) (𝟙 F.repr_X)

instance : is_iso F.repr_f :=
representable.has_representation.some_spec.some_spec

/--
An isomorphism between `F` and a functor of the form `C(-, F.repr_X)`.  Note the components
`F.repr_w.app X` definitionally have type `(X.unop ⟶ F.repr_X) ≅ F.obj X`.
-/
noncomputable def repr_w : yoneda.obj F.repr_X ≅ F := as_iso F.repr_f

@[simp] lemma repr_w_hom : F.repr_w.hom = F.repr_f := rfl

lemma repr_w_app_hom (X : Cᵒᵖ) (f : unop X ⟶ F.repr_X) :
  (F.repr_w.app X).hom f = F.map f.op F.repr_x :=
begin
  change F.repr_f.app X f = (F.repr_f.app (op F.repr_X) ≫ F.map f.op) (𝟙 F.repr_X),
  rw ←F.repr_f.naturality,
  dsimp,
  simp
end

end representable

section corepresentable

variables (F : C ⥤ Type v₁)
variable [F.corepresentable]

/-- The representing object for the corepresentable functor `F`. -/
noncomputable def corepr_X : C :=
(corepresentable.has_corepresentation : ∃ X (f : _ ⟶ F), _).some.unop

/-- The (forward direction of the) isomorphism witnessing `F` is corepresentable. -/
noncomputable def corepr_f : coyoneda.obj (op F.corepr_X) ⟶ F :=
corepresentable.has_corepresentation.some_spec.some

/--
The representing element for the corepresentable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def corepr_x : F.obj F.corepr_X :=
F.corepr_f.app F.corepr_X (𝟙 F.corepr_X)

instance : is_iso F.corepr_f :=
corepresentable.has_corepresentation.some_spec.some_spec

/--
An isomorphism between `F` and a functor of the form `C(F.corepr X, -)`. Note the components
`F.corepr_w.app X` definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
noncomputable def corepr_w : coyoneda.obj (op F.corepr_X) ≅ F := as_iso F.corepr_f

lemma corepr_w_app_hom (X : C) (f : F.corepr_X ⟶ X) :
  (F.corepr_w.app X).hom f = F.map f F.corepr_x :=
begin
  change F.corepr_f.app X f = (F.corepr_f.app F.corepr_X ≫ F.map f) (𝟙 F.corepr_X),
  rw ←F.corepr_f.naturality,
  dsimp,
  simp
end

end corepresentable

end functor

lemma representable_of_nat_iso (F : Cᵒᵖ ⥤ Type v₁) {G} (i : F ≅ G) [F.representable] :
  G.representable :=
{ has_representation := ⟨F.repr_X, F.repr_f ≫ i.hom, infer_instance⟩ }

lemma corepresentable_of_nat_iso (F : C ⥤ Type v₁) {G} (i : F ≅ G) [F.corepresentable] :
  G.corepresentable :=
{ has_corepresentation := ⟨op F.corepr_X, F.corepr_f ≫ i.hom, infer_instance⟩ }

instance : functor.corepresentable (𝟭 (Type v₁)) :=
corepresentable_of_nat_iso (coyoneda.obj (op punit)) coyoneda.punit_iso

open opposite

variables (C)

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
    simp only [yoneda_map_app, quiver.hom.unop_op],
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
@[simps] def yoneda_sections (X : C) (F : Cᵒᵖ ⥤ Type v₁) :
  (yoneda.obj X ⟶ F) ≅ ulift.{u₁} (F.obj (op X)) :=
(yoneda_lemma C).app (op X, F)

/--
We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yoneda_equiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) :=
(yoneda_sections X F).to_equiv.trans equiv.ulift

@[simp]
lemma yoneda_equiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
  yoneda_equiv f = f.app (op X) (𝟙 X) :=
rfl

@[simp]
lemma yoneda_equiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X))
  (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
  (yoneda_equiv.symm x).app Y f = F.map f.op x :=
rfl

lemma yoneda_equiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) :
  F.map g.op (yoneda_equiv f) = yoneda_equiv (yoneda.map g ≫ f) :=
begin
  change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g),
  rw ←f.naturality,
  dsimp,
  simp,
end

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

local attribute[ext] functor.ext

/-- The curried version of yoneda lemma when `C` is small. -/
def curried_yoneda_lemma {C : Type u₁} [small_category C] :
  (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation Cᵒᵖ (Type u₁) :=
eq_to_iso (by tidy) ≪≫ curry.map_iso (yoneda_lemma C ≪≫
  iso_whisker_left (evaluation_uncurried Cᵒᵖ (Type u₁)) ulift_functor_trivial) ≪≫
    eq_to_iso (by tidy)

/-- The curried version of yoneda lemma when `C` is small. -/
def curried_yoneda_lemma' {C : Type u₁} [small_category C] :
  yoneda ⋙ (whiskering_left Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
eq_to_iso (by tidy) ≪≫ curry.map_iso (iso_whisker_left (prod.swap _ _)
  (yoneda_lemma C ≪≫ iso_whisker_left
    (evaluation_uncurried Cᵒᵖ (Type u₁)) ulift_functor_trivial : _)) ≪≫ eq_to_iso (by tidy)

end category_theory
