/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.types
import category_theory.monoidal.center

/-!
# Enriched categories

We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.

We do not assume here that `V` is a concrete category,
so there does not need to be a "honest" underlying category!

Use `X ⟶[V] Y` to obtain the `V` object of morphisms from `X` to `Y`.

This file contains the definitions of `V`-enriched categories and
`V`-functors.

We don't yet define the `V`-object of natural transformations
between a pair of `V`-functors (this requires limits in `V`),
but we do provide a presheaf isomorphic to the Yoneda embedding of this object.

We verify that when `V = Type v`, all these notion reduce to the usual ones.
-/

universes w v u₁ u₂ u₃

noncomputable theory

namespace category_theory

open opposite
open monoidal_category

variables (V : Type v) [category.{w} V] [monoidal_category V]

/--
A `V`-category is a category enriched in a monoidal category `V`.

Note that we do not assume that `V` is a concrete category,
so there may not be an "honest" underlying category at all!
-/
class enriched_category (C : Type u₁) :=
(hom : C → C → V)
(notation X ` ⟶[] ` Y:10 := hom X Y)
(id : Π X, 𝟙_ V ⟶ (X ⟶[] X))
(comp : Π X Y Z, (X ⟶[] Y) ⊗ (Y ⟶[] Z) ⟶ (X ⟶[] Z))
(id_comp : Π X Y, (λ_ (X ⟶[] Y)).inv ≫ (id X ⊗ 𝟙 _) ≫ comp X X Y = 𝟙 _ . obviously)
(comp_id : Π X Y, (ρ_ (X ⟶[] Y)).inv ≫ (𝟙 _ ⊗ id Y) ≫ comp X Y Y = 𝟙 _ . obviously)
(assoc :
  Π W X Y Z, (α_ _ _ _).inv ≫ (comp W X Y ⊗ 𝟙 _) ≫ comp W Y Z = (𝟙 _ ⊗ comp X Y Z) ≫ comp W X Z
  . obviously)

notation X ` ⟶[`V`] ` Y:10 := (enriched_category.hom X Y : V)

variables (V) {C : Type u₁} [enriched_category V C]

/--
The `𝟙_ V`-shaped generalized element giving the identity in a `V`-enriched category.
-/
def e_id (X : C) : 𝟙_ V ⟶ (X ⟶[V] X) := enriched_category.id X
/--
The composition `V`-morphism for a `V`-enriched category.
-/
def e_comp (X Y Z : C) : (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z) := enriched_category.comp X Y Z

-- We don't just use `restate_axiom` here; that would leave `V` as an implicit argument.
@[simp, reassoc]
lemma e_id_comp (X Y : C) :
  (λ_ (X ⟶[V] Y)).inv ≫ (e_id V X ⊗ 𝟙 _) ≫ e_comp V X X Y = 𝟙 (X ⟶[V] Y) :=
enriched_category.id_comp X Y

@[simp, reassoc]
lemma e_comp_id (X Y : C) :
  (ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 _ ⊗ e_id V Y) ≫ e_comp V X Y Y = 𝟙 (X ⟶[V] Y) :=
enriched_category.comp_id X Y

@[simp, reassoc]
lemma e_assoc (W X Y Z : C) :
  (α_ _ _ _).inv ≫ (e_comp V W X Y ⊗ 𝟙 _) ≫ e_comp V W Y Z =
    (𝟙 _ ⊗ e_comp V X Y Z) ≫ e_comp V W X Z :=
enriched_category.assoc W X Y Z

section
variables {V} {W : Type v} [category.{w} W] [monoidal_category W]

/--
A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : lax_monoidal_functor V W` to each hom object.
-/
@[nolint has_inhabited_instance unused_arguments]
def transport_enrichment (F : lax_monoidal_functor V W) (C : Type u₁) := C

instance (F : lax_monoidal_functor V W) :
  enriched_category W (transport_enrichment F C) :=
{ hom := λ (X Y : C), F.obj (X ⟶[V] Y),
  id := λ (X : C), F.ε ≫ F.map (e_id V X),
  comp := λ (X Y Z : C), F.μ _ _ ≫ F.map (e_comp V X Y Z),
  id_comp := λ X Y, begin
    rw [comp_tensor_id, category.assoc,
      ←F.to_functor.map_id, F.μ_natural_assoc, F.to_functor.map_id, F.left_unitality_inv_assoc,
      ←F.to_functor.map_comp, ←F.to_functor.map_comp, e_id_comp, F.to_functor.map_id],
  end,
  comp_id := λ X Y, begin
    rw [id_tensor_comp, category.assoc,
      ←F.to_functor.map_id, F.μ_natural_assoc, F.to_functor.map_id, F.right_unitality_inv_assoc,
      ←F.to_functor.map_comp, ←F.to_functor.map_comp, e_comp_id, F.to_functor.map_id],
  end,
  assoc := λ P Q R S, begin
    rw [comp_tensor_id, category.assoc, ←F.to_functor.map_id, F.μ_natural_assoc,
      F.to_functor.map_id, ←F.associativity_inv_assoc, ←F.to_functor.map_comp,
      ←F.to_functor.map_comp, e_assoc, id_tensor_comp, category.assoc, ←F.to_functor.map_id,
      F.μ_natural_assoc, F.to_functor.map_comp],
  end, }

end

/--
Construct an honest category from a `Type v`-enriched category.
-/
def category_of_enriched_category_Type (C : Type u₁) [𝒞 : enriched_category (Type v) C] :
  category.{v} C :=
{ hom := 𝒞.hom,
  id := λ X, e_id (Type v) X punit.star,
  comp := λ X Y Z f g, e_comp (Type v) X Y Z ⟨f, g⟩,
  id_comp' := λ X Y f, congr_fun (e_id_comp (Type v) X Y) f,
  comp_id' := λ X Y f, congr_fun (e_comp_id (Type v) X Y) f,
  assoc' := λ W X Y Z f g h, (congr_fun (e_assoc (Type v) W X Y Z) ⟨f, g, h⟩ : _), }

/--
Construct a `Type v`-enriched category from an honest category.
-/
def enriched_category_Type_of_category (C : Type u₁) [𝒞 : category.{v} C] :
  enriched_category (Type v) C :=
{ hom := 𝒞.hom,
  id := λ X p, 𝟙 X,
  comp := λ X Y Z p, p.1 ≫ p.2,
  id_comp := λ X Y, by { ext, simp, },
  comp_id := λ X Y, by { ext, simp, },
  assoc := λ W X Y Z, by { ext ⟨f, g, h⟩, simp, }, }

/--
We verify that an enriched category in `Type u` is just the same thing as an honest category.
-/
def enriched_category_Type_equiv_category (C : Type u₁) :
  (enriched_category (Type v) C) ≃ category.{v} C :=
{ to_fun := λ 𝒞, by exactI category_of_enriched_category_Type C,
  inv_fun := λ 𝒞, by exactI enriched_category_Type_of_category C,
  left_inv := λ 𝒞, begin
    cases 𝒞,
    dsimp [enriched_category_Type_of_category],
    congr,
    { ext X ⟨⟩, refl, },
    { ext X Y Z ⟨f, g⟩, refl, }
  end,
  right_inv := λ 𝒞, by { rcases 𝒞 with ⟨⟨⟨⟩⟩⟩, dsimp, congr, }, }.

section
variables {W : Type (v+1)} [category.{v} W] [monoidal_category W] [enriched_category W C]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the (honest) category structure
so that `X ⟶ Y` is `(𝟙_ W) ⟶ (X ⟶[W] Y)`.

We obtain this category by
transporting the enrichment in `V` along the lax monoidal functor `coyoneda_tensor_unit`,
then using the equivalence of `Type`-enriched categories with honest categories.

This is sometimes called the "underlying" category of an enriched category,
although some care is needed as the functor `coyoneda_tensor_unit`,
which always exists, does not necessarily coincide with
"the forgetful functor" from `V` to `Type`, if such exists.
When `V` is any of `Type`, `Top`, `AddCommGroup`, or `Module R`,
`coyoneda_tensor_unit` is just the usual forgetful functor, however.
For `V = Algebra R`, the usual forgetful functor is coyoneda of `polynomial R`, not of `R`.
(Perhaps we should have a typeclass for this situation: `concrete_monoidal`?)
-/
@[nolint has_inhabited_instance unused_arguments]
def forget_enrichment
  (W : Type (v+1)) [category.{v} W] [monoidal_category W] (C : Type u₁) [enriched_category W C] :=
C

variables (W)

/-- Typecheck an object of `C` as an object of `forget_enrichment W C`. -/
def forget_enrichment.of (X : C) : forget_enrichment W C := X

/-- Typecheck an object of `forget_enrichment W C` as an object of `C`. -/
def forget_enrichment.to (X : forget_enrichment W C) : C := X

@[simp] lemma forget_enrichment.to_of (X : C) :
  forget_enrichment.to W (forget_enrichment.of W X) = X := rfl
@[simp] lemma forget_enrichment.of_to (X : forget_enrichment W C) :
  forget_enrichment.of W (forget_enrichment.to W X) = X := rfl

instance category_forget_enrichment : category (forget_enrichment W C) :=
begin
  let I : enriched_category (Type v) (transport_enrichment (coyoneda_tensor_unit W) C) :=
    infer_instance,
  exact enriched_category_Type_equiv_category C I,
end

/--
We verify that the morphism types in `forget_enrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W] Y)`.
-/
example (X Y : forget_enrichment W C) :
  (X ⟶ Y) = ((𝟙_ W) ⟶ (forget_enrichment.to W X ⟶[W] forget_enrichment.to W Y)) :=
rfl

/-- Typecheck a `(𝟙_ W)`-shaped `W`-morphism as a morphism in `forget_enrichment W C`. -/
def forget_enrichment.hom_of {X Y : C} (f : (𝟙_ W) ⟶ (X ⟶[W] Y)) :
  forget_enrichment.of W X ⟶ forget_enrichment.of W Y :=
f

/-- Typecheck a morphism in `forget_enrichment W C` as a `(𝟙_ W)`-shaped `W`-morphism. -/
def forget_enrichment.hom_to {X Y : forget_enrichment W C} (f : X ⟶ Y) :
  (𝟙_ W) ⟶ (forget_enrichment.to W X ⟶[W] forget_enrichment.to W Y) := f

@[simp] lemma forget_enrichment.hom_to_hom_of {X Y : C} (f : (𝟙_ W) ⟶ (X ⟶[W] Y)) :
  forget_enrichment.hom_to W (forget_enrichment.hom_of W f) = f := rfl
@[simp] lemma forget_enrichment.hom_of_hom_to {X Y : forget_enrichment W C} (f : X ⟶ Y) :
  forget_enrichment.hom_of W (forget_enrichment.hom_to W f) = f := rfl

/-- The identity in the "underlying" category of an enriched category. -/
@[simp] lemma forget_enrichment_id (X : forget_enrichment W C) :
  forget_enrichment.hom_to W (𝟙 X) = (e_id W (forget_enrichment.to W X : C)) :=
category.id_comp _

@[simp] lemma forget_enrichment_id' (X : C) :
  forget_enrichment.hom_of W (e_id W X) = (𝟙 (forget_enrichment.of W X : C)) :=
(forget_enrichment_id W (forget_enrichment.of W X)).symm

/-- Composition in the "underlying" category of an enriched category. -/
@[simp] lemma forget_enrichment_comp {X Y Z : forget_enrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  forget_enrichment.hom_to W (f ≫ g) = (((λ_ (𝟙_ W)).inv ≫
    (forget_enrichment.hom_to W f ⊗ forget_enrichment.hom_to W g)) ≫ e_comp W _ _ _) :=
rfl

end

/--
A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
structure enriched_functor
  (C : Type u₁) [enriched_category V C] (D : Type u₂) [enriched_category V D] :=
(obj : C → D)
(map : Π X Y : C, (X ⟶[V] Y) ⟶ (obj X ⟶[V] obj Y))
(map_id' : ∀ X : C, e_id V X ≫ map X X = e_id V (obj X) . obviously)
(map_comp' : ∀ X Y Z : C,
  e_comp V X Y Z ≫ map X Z = (map X Y ⊗ map Y Z) ≫ e_comp V (obj X) (obj Y) (obj Z) . obviously)

restate_axiom enriched_functor.map_id'
restate_axiom enriched_functor.map_comp'
attribute [simp, reassoc] enriched_functor.map_id
attribute [simp, reassoc] enriched_functor.map_comp

/-- The identity enriched functor. -/
@[simps]
def enriched_functor.id (C : Type u₁) [enriched_category V C] : enriched_functor V C C :=
{ obj := λ X, X,
  map := λ X Y, 𝟙 _, }

instance : inhabited (enriched_functor V C C) := ⟨enriched_functor.id V C⟩

/-- Composition of enriched functors. -/
@[simps]
def enriched_functor.comp {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [enriched_category V C] [enriched_category V D] [enriched_category V E]
  (F : enriched_functor V C D) (G : enriched_functor V D E) :
  enriched_functor V C E :=
{ obj := λ X, G.obj (F.obj X),
  map := λ X Y, F.map _ _ ≫ G.map _ _, }

section
variables {W : Type (v+1)} [category.{v} W] [monoidal_category W]

/--
An enriched functor induces an honest functor of the underlying categories,
by mapping the `(𝟙_ W)`-shaped morphisms.
-/
def enriched_functor.forget {C : Type u₁} {D : Type u₂}
  [enriched_category W C] [enriched_category W D]
  (F : enriched_functor W C D) : (forget_enrichment W C) ⥤ (forget_enrichment W D) :=
{ obj := λ X, forget_enrichment.of W (F.obj (forget_enrichment.to W X)),
  map := λ X Y f, forget_enrichment.hom_of W
    (forget_enrichment.hom_to W f ≫ F.map (forget_enrichment.to W X) (forget_enrichment.to W Y)),
  map_comp' := λ X Y Z f g, begin
    dsimp,
    apply_fun forget_enrichment.hom_to W,
    { simp only [iso.cancel_iso_inv_left, category.assoc, tensor_comp,
        forget_enrichment.hom_to_hom_of, enriched_functor.map_comp, forget_enrichment_comp],
      refl, },
    { intros f g w, apply_fun forget_enrichment.hom_of W at w, simpa using w, },
  end, }

end

section
variables {V}
variables {D : Type u₂} [enriched_category V D]

/-!
We now turn to natural transformations between `V`-functors.

The mostly commonly encountered definition of an enriched natural transformation
is a collection of morphisms
```
(𝟙_ W) ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying an appropriate analogue of the naturality square.
(c.f. https://ncatlab.org/nlab/show/enriched+natural+transformation)

This is the same thing as a natural transformation `F.forget ⟶ G.forget`.

We formalize this as `enriched_nat_trans F G`, which is a `Type`.

However, there's also something much nicer: with appropriate additional hypotheses,
there is a `V`-object `enriched_nat_trans_obj F G` which contains more information,
and from which one can recover `enriched_nat_trans F G ≃ (𝟙_ V) ⟶ enriched_nat_trans_obj F G`.

Using these as the hom-objects, we can build a `V`-enriched category
with objects the `V`-functors.

For `enriched_nat_trans_obj` to exist, it suffices to have `V` braided and complete.

Before assuming `V` is complete, we assume it is braided and
define a presheaf `enriched_nat_trans_yoneda F G`
which is isomorphic to the Yoneda embedding of `enriched_nat_trans_obj F G`
whether or not that object actually exists.

This presheaf has components `(enriched_nat_trans_yoneda F G).obj A`
what we call the `A`-graded enriched natural transformations,
which are collections of morphisms
```
A ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying a similar analogue of the naturality square,
this time incorporating a half-braiding on `A`.

(We actually define `enriched_nat_trans F G`
as the special case `A := 𝟙_ V` with the trivial half-braiding,
and when defining `enriched_nat_trans_yoneda F G` we use the half-braidings
coming from the ambient braiding on `V`.)
-/

/--
The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural transformations.
-/
@[ext, nolint has_inhabited_instance]
structure graded_nat_trans (A : center V) (F G : enriched_functor V C D) :=
(app : Π (X : C), A.1 ⟶ (F.obj X ⟶[V] G.obj X))
(naturality :
  ∀ (X Y : C), (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ app Y) ≫ e_comp V _ _ _ =
    (app X ⊗ G.map X Y) ≫ e_comp V _ _ _)

variables [braided_category V]
open braided_category

/--
A presheaf isomorphic to the Yoneda embedding of
the `V`-object of natural transformations from `F` to `G`.
-/
@[simps]
def enriched_nat_trans_yoneda (F G : enriched_functor V C D) : Vᵒᵖ ⥤ (Type (max u₁ w)) :=
{ obj := λ A, graded_nat_trans ((center.of_braided V).obj (unop A)) F G,
  map := λ A A' f σ,
  { app := λ X, f.unop ≫ σ.app X,
    naturality := λ X Y, begin
      have p := σ.naturality X Y,
      dsimp at p ⊢,
      rw [←id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _, id_tensor_comp, category.assoc,
        category.assoc, ←braiding_naturality_assoc, id_tensor_comp_tensor_id_assoc, p,
        ←tensor_comp_assoc,category.id_comp],
     end }, }

-- TODO assuming `[has_limits C]` construct the actual object of natural transformations
-- and show that the functor category is `V`-enriched.

end

section
local attribute [instance] category_of_enriched_category_Type

/--
We verify that an enriched functor between `Type v` enriched categories
is just the same thing as an honest functor.
-/
@[simps]
def enriched_functor_Type_equiv_functor
  {C : Type u₁} [𝒞 : enriched_category (Type v) C]
  {D : Type u₂} [𝒟 : enriched_category (Type v) D] :
  enriched_functor (Type v) C D ≃ (C ⥤ D) :=
{ to_fun := λ F,
  { obj := λ X, F.obj X,
    map := λ X Y f, F.map X Y f,
    map_id' := λ X, congr_fun (F.map_id X) punit.star,
    map_comp' := λ X Y Z f g, congr_fun (F.map_comp X Y Z) ⟨f, g⟩, },
  inv_fun := λ F,
  { obj := λ X, F.obj X,
    map := λ X Y f, F.map f,
    map_id' := λ X, by { ext ⟨⟩, exact F.map_id X, },
    map_comp' := λ X Y Z, by { ext ⟨f, g⟩, exact F.map_comp f g, }, },
  left_inv := λ F, by { cases F, simp, },
  right_inv := λ F, by { cases F, simp, }, }

/--
We verify that the presheaf representing natural transformations
between `Type v`-enriched functors is actually represented by
the usual type of natural transformations!
-/
def enriched_nat_trans_yoneda_Type_iso_yoneda_nat_trans
  {C : Type v} [enriched_category (Type v) C]
  {D : Type v} [enriched_category (Type v) D]
  (F G : enriched_functor (Type v) C D) :
  enriched_nat_trans_yoneda F G ≅
  yoneda.obj ((enriched_functor_Type_equiv_functor F) ⟶ (enriched_functor_Type_equiv_functor G)) :=
nat_iso.of_components (λ α,
  { hom := λ σ x,
    { app := λ X, σ.app X x,
      naturality' := λ X Y f, congr_fun (σ.naturality X Y) ⟨x, f⟩, },
    inv := λ σ,
    { app := λ X x, (σ x).app X,
      naturality := λ X Y, by { ext ⟨x, f⟩, exact ((σ x).naturality f), }, }})
  (by tidy)

end

end category_theory
