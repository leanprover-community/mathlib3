/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.braided
import category_theory.reflects_isomorphisms
import category_theory.monoidal.coherence

/-!
# Half braidings and the Drinfeld center of a monoidal category

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
@[nolint has_inhabited_instance]
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
@[nolint has_inhabited_instance]
def center := Σ X : C, half_braiding X

namespace center

variables {C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext, nolint has_inhabited_instance]
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

/--
Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
def iso_mk {X Y : center C} (f : X ⟶ Y) [is_iso f.f] : X ≅ Y :=
{ hom := f,
  inv := ⟨inv f.f, λ U, begin
    dsimp,
    apply (cancel_epi (f.f ⊗ 𝟙 U)).mp,
    simp [←comp_tensor_id_assoc, ←id_tensor_comp],
  end⟩, }

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_obj (X Y : center C) : center C :=
⟨X.1 ⊗ Y.1,
  { β := λ U, α_ _ _ _ ≪≫ (iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm
      ≪≫ (X.2.β U ⊗ iso.refl Y.1) ≪≫ α_ _ _ _,
    monoidal' := λ U U',
    /-begin
      dsimp,
      -- We don't do this as a pure rewriting proof; we move isos from one side to the other,
      -- and use `congr` to strip off parts that are already equal.
      -- I suspect this is not the shortest path!
      simp only [comp_tensor_id, id_tensor_comp, category.assoc, half_braiding.monoidal],
      rw [pentagon_assoc, pentagon_inv_assoc, iso.eq_inv_comp, ←pentagon_assoc,
        ←id_tensor_comp_assoc, iso.hom_inv_id, tensor_id, category.id_comp,
        ←associator_naturality_assoc],
      congr' 2,
      conv_lhs {
        rw [←associator_inv_naturality_assoc (X.2.β U).hom,
        associator_inv_naturality_assoc _ _ (Y.2.β U').hom,
        tensor_id, tensor_id, id_tensor_comp_tensor_id_assoc], },
      conv_rhs {
        rw [associator_naturality_assoc (X.2.β U).hom,
          ←associator_naturality_assoc _ _ (Y.2.β U').hom,
          tensor_id, tensor_id, tensor_id_comp_id_tensor_assoc, ←id_tensor_comp_tensor_id], },
      rw [tensor_id, category.id_comp, ←is_iso.inv_comp_eq, inv_tensor, is_iso.inv_id,
        is_iso.iso.inv_inv, pentagon_assoc, iso.hom_inv_id_assoc],
      congr' 2,
      rw [←is_iso.inv_comp_eq, is_iso.iso.inv_hom, ←pentagon_inv_assoc, ←comp_tensor_id_assoc,
        iso.inv_hom_id, tensor_id, category.id_comp, ←associator_inv_naturality_assoc],
      congr' 2,
      rw [←is_iso.inv_comp_eq, inv_tensor, is_iso.iso.inv_hom, is_iso.inv_id, pentagon_inv_assoc,
        iso.inv_hom_id, category.comp_id],
    end,-/
    begin
      -- First make it canonical with explicit associators
      dsimp,
      simp only [comp_tensor_id, id_tensor_comp, category.assoc, half_braiding.monoidal],

      /- All of this can easily be automated. -/
      rw comp_eq_coherent_comp ((monoidal_obj.of X.fst).tensor ((monoidal_obj.of Y.fst).tensor ((monoidal_obj.of U).tensor (monoidal_obj.of U')))),
      rw comp_eq_coherent_comp ((((monoidal_obj.of U).tensor (monoidal_obj.of U')).tensor (monoidal_obj.of X.fst)).tensor (monoidal_obj.of Y.fst)),
      rw comp_eq_coherent_comp ((monoidal_obj.of X.fst).tensor (((monoidal_obj.of Y.fst).tensor (monoidal_obj.of U)).tensor (monoidal_obj.of U'))),
      rw comp_eq_coherent_comp ((monoidal_obj.of X.fst).tensor (((monoidal_obj.of U).tensor (monoidal_obj.of Y.fst)).tensor (monoidal_obj.of U'))),
      rw comp_eq_coherent_comp ((monoidal_obj.of X.fst).tensor ((monoidal_obj.of U).tensor ((monoidal_obj.of Y.fst).tensor (monoidal_obj.of U')))),
      rw comp_eq_coherent_comp ((monoidal_obj.of X.fst).tensor ((monoidal_obj.of U).tensor ((monoidal_obj.of U').tensor (monoidal_obj.of Y.fst)))),
      rw comp_eq_coherent_comp ((monoidal_obj.of X.fst).tensor (((monoidal_obj.of U).tensor (monoidal_obj.of U')).tensor (monoidal_obj.of Y.fst))),
      rw comp_eq_coherent_comp (((monoidal_obj.of X.fst).tensor ((monoidal_obj.of U).tensor (monoidal_obj.of U'))).tensor (monoidal_obj.of Y.fst)),
      rw comp_eq_coherent_comp ((((monoidal_obj.of X.fst).tensor (monoidal_obj.of U)).tensor (monoidal_obj.of U')).tensor (monoidal_obj.of Y.fst)),
      rw comp_eq_coherent_comp ((((monoidal_obj.of U).tensor (monoidal_obj.of X.fst)).tensor (monoidal_obj.of U')).tensor (monoidal_obj.of Y.fst)),
      rw comp_eq_coherent_comp (((monoidal_obj.of U).tensor ((monoidal_obj.of X.fst).tensor (monoidal_obj.of U'))).tensor (monoidal_obj.of Y.fst)),
      rw comp_eq_coherent_comp (((monoidal_obj.of U).tensor ((monoidal_obj.of U').tensor (monoidal_obj.of X.fst))).tensor (monoidal_obj.of Y.fst)),

      rw comp_eq_coherent_comp ((((monoidal_obj.of X.fst).tensor (monoidal_obj.of Y.fst)).tensor (monoidal_obj.of U)).tensor (monoidal_obj.of U')),
      rw comp_eq_coherent_comp (((monoidal_obj.of X.fst).tensor ((monoidal_obj.of Y.fst).tensor (monoidal_obj.of U))).tensor (monoidal_obj.of U')),
      rw comp_eq_coherent_comp (((monoidal_obj.of X.fst).tensor ((monoidal_obj.of U).tensor (monoidal_obj.of Y.fst))).tensor (monoidal_obj.of U')),
      rw comp_eq_coherent_comp ((((monoidal_obj.of X.fst).tensor (monoidal_obj.of U)).tensor (monoidal_obj.of Y.fst)).tensor (monoidal_obj.of U')),
      rw comp_eq_coherent_comp ((((monoidal_obj.of U).tensor (monoidal_obj.of X.fst)).tensor (monoidal_obj.of Y.fst)).tensor (monoidal_obj.of U')),
      rw comp_eq_coherent_comp (((monoidal_obj.of U).tensor ((monoidal_obj.of X.fst).tensor (monoidal_obj.of Y.fst))).tensor (monoidal_obj.of U')),
      rw comp_eq_coherent_comp ((monoidal_obj.of U).tensor (((monoidal_obj.of X.fst).tensor (monoidal_obj.of Y.fst)).tensor (monoidal_obj.of U'))),
      rw comp_eq_coherent_comp ((monoidal_obj.of U).tensor ((monoidal_obj.of X.fst).tensor ((monoidal_obj.of Y.fst).tensor (monoidal_obj.of U')))),
      rw comp_eq_coherent_comp ((monoidal_obj.of U).tensor ((monoidal_obj.of X.fst).tensor ((monoidal_obj.of U').tensor (monoidal_obj.of Y.fst)))),
      rw comp_eq_coherent_comp ((monoidal_obj.of U).tensor (((monoidal_obj.of X.fst).tensor (monoidal_obj.of U')).tensor (monoidal_obj.of Y.fst))),
      rw comp_eq_coherent_comp ((monoidal_obj.of U).tensor (((monoidal_obj.of U').tensor (monoidal_obj.of X.fst)).tensor (monoidal_obj.of Y.fst))),
      rw comp_eq_coherent_comp ((monoidal_obj.of U).tensor ((monoidal_obj.of U').tensor ((monoidal_obj.of X.fst).tensor (monoidal_obj.of Y.fst)))),

      /- Then hide all the associators (maybe this could be a simp-set?) -/
      simp,
      repeat { erw coherent_comp_id_coherent_comp' }, -- Why do simp and rw fail here?

      -- Restore the compositions which are up to eq, not just up to iso
      simp only [←comp_eq_coherent_comp],

      -- Finish!
      rw [coherent_reassoc (id_tensor_comp_tensor_id _ _),
          coherent_reassoc (tensor_id_comp_id_tensor _ _)],

      -- Uhhhhh......
      refl,
    end,
    naturality' := λ U U' f,
    begin
      dsimp,
      simp only [comp_eq_coherent_comp],
      simp,

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
  end  }

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
@[simps]
def associator (X Y Z : center C) : tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
iso_mk ⟨(α_ X.1 Y.1 Z.1).hom, λ U, begin
  dsimp,
  -- We don't do this as a pure rewriting proof; we move isos from one side to the other,
  -- and use `congr` to strip off parts that are already equal.
  simp only [category.assoc, comp_tensor_id, id_tensor_comp],
  rw [pentagon, pentagon_assoc, ←associator_naturality_assoc (𝟙 X.1) (𝟙 Y.1), tensor_id],
  congr' 2,
  rw [iso.eq_inv_comp, ←pentagon_assoc, ←id_tensor_comp_assoc, iso.hom_inv_id,
    tensor_id, category.id_comp, ←associator_naturality_assoc],
  congr' 2,
  rw [←is_iso.inv_comp_eq, inv_tensor, is_iso.inv_id, is_iso.iso.inv_inv, pentagon_assoc,
    iso.hom_inv_id_assoc, ←tensor_id, ←associator_naturality_assoc],
end⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def left_unitor (X : center C) : tensor_obj tensor_unit X ≅ X :=
iso_mk ⟨(λ_ X.1).hom, λ U, begin
  dsimp,
  simp only [category.comp_id, category.assoc, tensor_inv_hom_id, comp_tensor_id,
    tensor_id_comp_id_tensor, triangle_assoc_comp_right_inv],
  rw [←left_unitor_tensor, left_unitor_naturality, left_unitor_tensor'_assoc],
end⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def right_unitor (X : center C) : tensor_obj X tensor_unit ≅ X :=
iso_mk ⟨(ρ_ X.1).hom, λ U, begin
  dsimp,
  simp only [tensor_id_comp_id_tensor_assoc, triangle_assoc, id_tensor_comp, category.assoc],
  conv_rhs { rw [←tensor_id_comp_id_tensor_assoc], },
  congr' 1,
  rw [←right_unitor_tensor_inv_assoc, ←right_unitor_inv_naturality_assoc],
  simp,
end⟩

section
local attribute [simp] associator_naturality left_unitor_naturality right_unitor_naturality
  pentagon

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

@[simp] lemma associator_hom_f' (X Y Z : center C) : hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
rfl

@[simp] lemma associator_inv_f' (X Y Z : center C) : hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv :=
by { ext, rw [←associator_hom_f', ←comp_f, iso.hom_inv_id], refl, }

@[simp] lemma left_unitor_hom_f' (X : center C) : hom.f (λ_ X).hom = (λ_ X.1).hom :=
rfl

@[simp] lemma left_unitor_inv_f' (X : center C) : hom.f (λ_ X).inv = (λ_ X.1).inv :=
by { ext, rw [←left_unitor_hom_f', ←comp_f, iso.hom_inv_id], refl, }

@[simp] lemma right_unitor_hom_f' (X : center C) : hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
rfl

@[simp] lemma right_unitor_inv_f' (X : center C) : hom.f (ρ_ X).inv = (ρ_ X.1).inv :=
by { ext, rw [←right_unitor_hom_f', ←comp_f, iso.hom_inv_id], refl, }

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

instance : braided_category (center C) :=
{ braiding := braiding,
  braiding_naturality' := λ X Y X' Y' f g, begin
    ext,
    dsimp,
    rw [←tensor_id_comp_id_tensor, category.assoc, half_braiding.naturality, f.comm_assoc,
      id_tensor_comp_tensor_id],
  end, } -- `obviously` handles the hexagon axioms

end center

end category_theory
