/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.types
import category_theory.monoidal.braided

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
A type synonym for `C`, which should should come equipped with a `V`-enriched category structure.
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
A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
@[nolint has_inhabited_instance]
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

@[simps]
def enriched_functor.id (C : Type u₁) [enriched_category V C] : enriched_functor V C C :=
{ obj := λ X, X,
  map := λ X Y, 𝟙 _, }

@[simps]
def enriched_functor.comp {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [enriched_category V C] [enriched_category V D] [enriched_category V E]
  (F : enriched_functor V C D) (G : enriched_functor V D E) :
  enriched_functor V C E :=
{ obj := λ X, G.obj (F.obj X),
  map := λ X Y, F.map _ _ ≫ G.map _ _, }

section
variables {V} [braided_category V]
variables {D : Type u₂} [enriched_category V D]

/-!
For general `V`-enriched categories `C D`, and `V`-functors `F G`,
it's not possible to make sense of natural transformations between `F` and `G` at all.

An essential ingredient is a braiding (or symmetry) on `V`.

Even assuming that, we should only get an object in `V` worth of natural transformations,
rather than a type. Moreover, it's only possible to define this object if `V` has certain limits.

Here, we define a presheaf which is isomorphic to the Yoneda embedding of that object,
which we can do without any further assumptions.
-/

/--
The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural transformations.
-/
@[ext, nolint has_inhabited_instance]
structure graded_nat_trans (A : V) (F G : enriched_functor V C D) :=
(app : Π (X : C), A ⟶ (F.obj X ⟶[V] G.obj X))
(naturality :
  ∀ (X Y : C), (app Y ⊗ F.map X Y) ≫ (β_ _ _).hom ≫ e_comp V _ _ _ =
    (app X ⊗ G.map X Y) ≫ e_comp V _ _ _)

/--
A presheaf isomorphic to the Yoneda embedding of
the `V`-object of natural transformations from `F` to `G`.
-/
@[simps]
def enriched_nat_trans_yoneda (F G : enriched_functor V C D) : Vᵒᵖ ⥤ (Type (max u₁ w)) :=
{ obj := λ A, graded_nat_trans (unop A) F G,
  map := λ A A' f σ,
  { app := λ X, f.unop ≫ σ.app X,
    naturality := λ X Y, begin
      rw [←tensor_id_comp_id_tensor _ (f.unop ≫ σ.app Y),
        ←tensor_id_comp_id_tensor _ (f.unop ≫ σ.app X),
        comp_tensor_id, comp_tensor_id,
        category.assoc, category.assoc, category.assoc, category.assoc,
        tensor_id_comp_id_tensor_assoc, tensor_id_comp_id_tensor_assoc,
        σ.naturality],
     end }, }

-- TODO assuming `[has_limits C]` construct the actual object of natural transformations
-- and show that the functor category is `V`-enriched.

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
  {C : Type v} [𝒞 : enriched_category (Type v) C]
  {D : Type v} [𝒟 : enriched_category (Type v) D]
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
