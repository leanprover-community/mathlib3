/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.braided
import category_theory.functor.reflects_isomorphisms
import category_theory.monoidal.coherence

/-!
# Half braidings and the Drinfeld center of a monoidal category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

We show that `center C` is braided monoidal,
and provide the monoidal functor `center.forget` from `center C` back to `C`.

## Future work

Verifying the various axioms here is done by tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.

More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial;
   I'm unsure if the monoidal coherence theorem is even usable in dependent type theory).
3. Automating these proofs using `rewrite_search` or some relative.

-/

open category_theory
open category_theory.monoidal_category

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]

/--
A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`,
monoidally natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same as natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which send the unique
`0`-morphism to `X`.
-/
@[nolint has_nonempty_instance]
structure half_braiding (X : C) :=
(β : Π U, X ⊗ U ≅ U ⊗ X)
(monoidal' : ∀ U U', (β (U ⊗ U')).hom =
  (α_ _ _ _).inv ≫ ((β U).hom ⊗ 𝟙 U') ≫ (α_ _ _ _).hom ≫ (𝟙 U ⊗ (β U').hom) ≫ (α_ _ _ _).inv
  . obviously)
(naturality' : ∀ {U U'} (f : U ⟶ U'), (𝟙 X ⊗ f) ≫ (β U').hom = (β U).hom ≫ (f ⊗ 𝟙 X) . obviously)

restate_axiom half_braiding.monoidal'
attribute [reassoc, simp] half_braiding.monoidal -- the reassoc lemma is redundant as a simp lemma
restate_axiom half_braiding.naturality'
attribute [simp, reassoc] half_braiding.naturality

variables (C)
/--
The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, where `X : C`
and `b` is a half-braiding on `X`.
-/
@[nolint has_nonempty_instance]
def center := Σ X : C, half_braiding X

namespace center

variables {C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext, nolint has_nonempty_instance]
structure hom (X Y : center C) :=
(f : X.1 ⟶ Y.1)
(comm' : ∀ U, (f ⊗ 𝟙 U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (𝟙 U ⊗ f) . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

instance : category (center C) :=
{ hom := hom,
  id := λ X, { f := 𝟙 X.1, },
  comp := λ X Y Z f g, { f := f.f ≫ g.f, }, }

@[simp] lemma id_f (X : center C) : hom.f (𝟙 X) = 𝟙 X.1 := rfl
@[simp] lemma comp_f {X Y Z : center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f := rfl

@[ext]
lemma ext {X Y : center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g :=
by { cases f, cases g, congr, exact w, }

/--
Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
def iso_mk {X Y : center C} (f : X ⟶ Y) [is_iso f.f] : X ≅ Y :=
{ hom := f,
  inv := ⟨inv f.f, λ U, by simp [←cancel_epi (f.f ⊗ 𝟙 U), ←comp_tensor_id_assoc, ←id_tensor_comp]⟩ }

instance is_iso_of_f_is_iso {X Y : center C} (f : X ⟶ Y) [is_iso f.f] : is_iso f :=
begin
  change is_iso (iso_mk f).hom,
  apply_instance,
end

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_obj (X Y : center C) : center C :=
⟨X.1 ⊗ Y.1,
  { β := λ U, α_ _ _ _ ≪≫ (iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm
      ≪≫ (X.2.β U ⊗ iso.refl Y.1) ≪≫ α_ _ _ _,
    monoidal' := λ U U',
    begin
      dsimp,
      simp only [comp_tensor_id, id_tensor_comp, category.assoc, half_braiding.monoidal],
      -- On the RHS, we'd like to commute `((X.snd.β U).hom ⊗ 𝟙 Y.fst) ⊗ 𝟙 U'`
      -- and `𝟙 U ⊗ 𝟙 X.fst ⊗ (Y.snd.β U').hom` past each other,
      -- but there are some associators we need to get out of the way first.
      slice_rhs 6 8 { rw pentagon, },
      slice_rhs 5 6 { rw associator_naturality, },
      slice_rhs 7 8 { rw ←associator_naturality, },
      slice_rhs 6 7 { rw [tensor_id, tensor_id, tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id,
        ←tensor_id, ←tensor_id], },
      -- Now insert associators as needed to make the four half-braidings look identical
      slice_rhs 10 10 { rw associator_inv_conjugation, },
      slice_rhs 7 7 { rw associator_inv_conjugation, },
      slice_rhs 6 6 { rw associator_conjugation, },
      slice_rhs 3 3 { rw associator_conjugation, },
      -- Finish with an application of the coherence theorem.
      coherence,
    end,
    naturality' := λ U U' f,
    begin
      dsimp,
      rw [category.assoc, category.assoc, category.assoc, category.assoc,
        id_tensor_associator_naturality_assoc, ←id_tensor_comp_assoc, half_braiding.naturality,
        id_tensor_comp_assoc, associator_inv_naturality_assoc, ←comp_tensor_id_assoc,
        half_braiding.naturality, comp_tensor_id_assoc, associator_naturality, ←tensor_id],
    end, }⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_hom {X₁ Y₁ X₂ Y₂ : center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  tensor_obj X₁ X₂ ⟶ tensor_obj Y₁ Y₂ :=
{ f := f.f ⊗ g.f,
  comm' := λ U, begin
    dsimp,
    rw [category.assoc, category.assoc, category.assoc, category.assoc,
      associator_naturality_assoc, ←tensor_id_comp_id_tensor, category.assoc,
      ←id_tensor_comp_assoc, g.comm, id_tensor_comp_assoc, tensor_id_comp_id_tensor_assoc,
      ←id_tensor_comp_tensor_id, category.assoc, associator_inv_naturality_assoc,
      id_tensor_associator_inv_naturality_assoc, tensor_id,
      id_tensor_comp_tensor_id_assoc, ←tensor_id_comp_id_tensor g.f, category.assoc,
      ←comp_tensor_id_assoc, f.comm, comp_tensor_id_assoc, id_tensor_associator_naturality,
      associator_naturality_assoc, ←id_tensor_comp, tensor_id_comp_id_tensor],
  end }

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_unit : center C :=
⟨𝟙_ C,
  { β := λ U, (λ_ U) ≪≫ (ρ_ U).symm,
    monoidal' := λ U U', by simp,
    naturality' := λ U U' f, begin
      dsimp,
      rw [left_unitor_naturality_assoc, right_unitor_inv_naturality, category.assoc],
    end, }⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def associator (X Y Z : center C) : tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
iso_mk ⟨(α_ X.1 Y.1 Z.1).hom, λ U, begin
  dsimp,
  simp only [comp_tensor_id, id_tensor_comp, ←tensor_id, associator_conjugation],
  coherence,
end⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def left_unitor (X : center C) : tensor_obj tensor_unit X ≅ X :=
iso_mk ⟨(λ_ X.1).hom, λ U, begin
  dsimp,
  simp only [category.comp_id, category.assoc, tensor_inv_hom_id, comp_tensor_id,
    tensor_id_comp_id_tensor, triangle_assoc_comp_right_inv],
  rw [←left_unitor_tensor, left_unitor_naturality, left_unitor_tensor'_assoc],
end⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def right_unitor (X : center C) : tensor_obj X tensor_unit ≅ X :=
iso_mk ⟨(ρ_ X.1).hom, λ U, begin
  dsimp,
  simp only [tensor_id_comp_id_tensor_assoc, triangle_assoc, id_tensor_comp, category.assoc],
  rw [←tensor_id_comp_id_tensor_assoc (ρ_ U).inv, cancel_epi, ←right_unitor_tensor_inv_assoc,
    ←right_unitor_inv_naturality_assoc],
  simp,
end⟩

section
local attribute [simp] associator_naturality left_unitor_naturality right_unitor_naturality
  pentagon
local attribute [simp] center.associator center.left_unitor center.right_unitor

instance : monoidal_category (center C) :=
{ tensor_obj := λ X Y, tensor_obj X Y,
  tensor_hom := λ X₁ Y₁ X₂ Y₂ f g, tensor_hom f g,
  tensor_unit := tensor_unit,
  associator := associator,
  left_unitor := left_unitor,
  right_unitor := right_unitor, }

@[simp] lemma tensor_fst (X Y : center C) : (X ⊗ Y).1 = X.1 ⊗ Y.1 := rfl

@[simp] lemma tensor_β (X Y : center C) (U : C) :
  (X ⊗ Y).2.β U =
    α_ _ _ _ ≪≫ (iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm
      ≪≫ (X.2.β U ⊗ iso.refl Y.1) ≪≫ α_ _ _ _ :=
rfl
@[simp] lemma tensor_f {X₁ Y₁ X₂ Y₂ : center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  (f ⊗ g).f = f.f ⊗ g.f :=
rfl

@[simp] lemma tensor_unit_β (U : C) : (𝟙_ (center C)).2.β U = (λ_ U) ≪≫ (ρ_ U).symm := rfl

@[simp] lemma associator_hom_f (X Y Z : center C) : hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
rfl

@[simp] lemma associator_inv_f (X Y Z : center C) : hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv :=
by { ext, rw [←associator_hom_f, ←comp_f, iso.hom_inv_id], refl, }

@[simp] lemma left_unitor_hom_f (X : center C) : hom.f (λ_ X).hom = (λ_ X.1).hom :=
rfl

@[simp] lemma left_unitor_inv_f (X : center C) : hom.f (λ_ X).inv = (λ_ X.1).inv :=
by { ext, rw [←left_unitor_hom_f, ←comp_f, iso.hom_inv_id], refl, }

@[simp] lemma right_unitor_hom_f (X : center C) : hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
rfl

@[simp] lemma right_unitor_inv_f (X : center C) : hom.f (ρ_ X).inv = (ρ_ X.1).inv :=
by { ext, rw [←right_unitor_hom_f, ←comp_f, iso.hom_inv_id], refl, }

end

section
variables (C)

/-- The forgetful monoidal functor from the Drinfeld center to the original category. -/
@[simps]
def forget : monoidal_functor (center C) C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.f,
  ε := 𝟙 (𝟙_ C),
  μ := λ X Y, 𝟙 (X.1 ⊗ Y.1), }

instance : reflects_isomorphisms (forget C).to_functor :=
{ reflects := λ A B f i, by { dsimp at i, resetI, change is_iso (iso_mk f).hom, apply_instance, } }

end

/-- Auxiliary definition for the `braided_category` instance on `center C`. -/
@[simps]
def braiding (X Y : center C) : X ⊗ Y ≅ Y ⊗ X :=
iso_mk ⟨(X.2.β Y.1).hom, λ U, begin
  dsimp,
  simp only [category.assoc],
  rw [←is_iso.inv_comp_eq, is_iso.iso.inv_hom, ←half_braiding.monoidal_assoc,
    ←half_braiding.naturality_assoc, half_braiding.monoidal],
  simp,
end⟩

instance braided_category_center : braided_category (center C) :=
{ braiding := braiding,
  braiding_naturality' := λ X Y X' Y' f g, begin
    ext,
    dsimp,
    rw [←tensor_id_comp_id_tensor, category.assoc, half_braiding.naturality, f.comm_assoc,
      id_tensor_comp_tensor_id],
  end, } -- `obviously` handles the hexagon axioms

section
variables [braided_category C]

open braided_category

/-- Auxiliary construction for `of_braided`. -/
@[simps]
def of_braided_obj (X : C) : center C :=
⟨X, { β := λ Y, β_ X Y,
  monoidal' := λ U U', begin
    rw [iso.eq_inv_comp, ←category.assoc, ←category.assoc, iso.eq_comp_inv,
      category.assoc, category.assoc],
    exact hexagon_forward X U U',
  end }⟩

variables (C)

/--
The functor lifting a braided category to its center, using the braiding as the half-braiding.
-/
@[simps]
def of_braided : monoidal_functor C (center C) :=
{ obj := of_braided_obj,
  map := λ X X' f,
  { f := f,
    comm' := λ U, braiding_naturality _ _, },
  ε :=
  { f := 𝟙 _,
    comm' := λ U, begin
      dsimp,
      rw [tensor_id, category.id_comp, tensor_id, category.comp_id, ←braiding_right_unitor,
        category.assoc, iso.hom_inv_id, category.comp_id],
    end, },
  μ := λ X Y,
  { f := 𝟙 _,
    comm' := λ U, begin
      dsimp,
      rw [tensor_id, tensor_id, category.id_comp, category.comp_id,
        ←iso.inv_comp_eq, ←category.assoc, ←category.assoc, ←iso.comp_inv_eq,
        category.assoc, hexagon_reverse, category.assoc],
    end, }, }

end

end center

end category_theory
