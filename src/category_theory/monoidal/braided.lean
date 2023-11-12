/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.coherence_lemmas
import category_theory.monoidal.natural_transformation
import category_theory.monoidal.discrete

/-!
# Braided and symmetric monoidal categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `braided_monoidal_category` another typeclass, but then have `symmetric_monoidal_category`
extend this. The rationale is that we are not carrying any additional data,
just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

-/

open category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃

namespace category_theory

/--
A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class braided_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
-- braiding natural iso:
(braiding             : Π X Y : C, X ⊗ Y ≅ Y ⊗ X)
(braiding_naturality' : ∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
  (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) . obviously)
-- hexagon identities:
(hexagon_forward'     : Π X Y Z : C,
    (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom
  = ((braiding X Y).hom ⊗ (𝟙 Z)) ≫ (α_ Y X Z).hom ≫ ((𝟙 Y) ⊗ (braiding X Z).hom)
  . obviously)
(hexagon_reverse'     : Π X Y Z : C,
    (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv
  = ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ⊗ (𝟙 Y))
  . obviously)

restate_axiom braided_category.braiding_naturality'
attribute [simp,reassoc] braided_category.braiding_naturality
restate_axiom braided_category.hexagon_forward'
restate_axiom braided_category.hexagon_reverse'
attribute [reassoc] braided_category.hexagon_forward braided_category.hexagon_reverse

open category
open monoidal_category
open braided_category

notation `β_` := braiding

/--
Verifying the axioms for a braiding by checking that the candidate braiding is sent to a braiding
by a faithful monoidal functor.
-/
def braided_category_of_faithful {C D : Type*} [category C] [category D]
  [monoidal_category C] [monoidal_category D] (F : monoidal_functor C D) [faithful F.to_functor]
  [braided_category D] (β : Π X Y : C, X ⊗ Y ≅ Y ⊗ X)
  (w : ∀ X Y, F.μ _ _ ≫ F.map (β X Y).hom = (β_ _ _).hom ≫ F.μ _ _) : braided_category C :=
{ braiding := β,
  braiding_naturality' := begin
    intros,
    apply F.to_functor.map_injective,
    refine (cancel_epi (F.μ _ _)).1 _,
    rw [functor.map_comp, ←lax_monoidal_functor.μ_natural_assoc, w, functor.map_comp, reassoc_of w,
      braiding_naturality_assoc, lax_monoidal_functor.μ_natural],
  end,
  hexagon_forward' := begin
    intros,
    apply F.to_functor.map_injective,
    refine (cancel_epi (F.μ _ _)).1 _,
    refine (cancel_epi (F.μ _ _ ⊗ 𝟙 _)).1 _,
    rw [functor.map_comp, functor.map_comp, functor.map_comp, functor.map_comp,
      ←lax_monoidal_functor.μ_natural_assoc, functor.map_id, ←comp_tensor_id_assoc, w,
      comp_tensor_id, category.assoc, lax_monoidal_functor.associativity_assoc,
      lax_monoidal_functor.associativity_assoc, ←lax_monoidal_functor.μ_natural, functor.map_id,
      ←id_tensor_comp_assoc, w, id_tensor_comp_assoc, reassoc_of w, braiding_naturality_assoc,
      lax_monoidal_functor.associativity, hexagon_forward_assoc],
  end,
  hexagon_reverse' := begin
    intros,
    apply F.to_functor.map_injective,
    refine (cancel_epi (F.μ _ _)).1 _,
    refine (cancel_epi (𝟙 _ ⊗ F.μ _ _)).1 _,
    rw [functor.map_comp, functor.map_comp, functor.map_comp, functor.map_comp,
      ←lax_monoidal_functor.μ_natural_assoc, functor.map_id, ←id_tensor_comp_assoc, w,
      id_tensor_comp_assoc, lax_monoidal_functor.associativity_inv_assoc,
      lax_monoidal_functor.associativity_inv_assoc, ←lax_monoidal_functor.μ_natural, functor.map_id,
      ←comp_tensor_id_assoc, w, comp_tensor_id_assoc, reassoc_of w, braiding_naturality_assoc,
      lax_monoidal_functor.associativity_inv, hexagon_reverse_assoc],
  end, }

/-- Pull back a braiding along a fully faithful monoidal functor. -/
noncomputable
def braided_category_of_fully_faithful {C D : Type*} [category C] [category D]
  [monoidal_category C] [monoidal_category D] (F : monoidal_functor C D)
  [full F.to_functor] [faithful F.to_functor]
  [braided_category D] : braided_category C :=
braided_category_of_faithful F (λ X Y, F.to_functor.preimage_iso
  ((as_iso (F.μ _ _)).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫ (as_iso (F.μ _ _))))
  (by tidy)

section
/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories" , Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/

variables (C : Type u₁) [category.{v₁} C] [monoidal_category C] [braided_category C]

lemma braiding_left_unitor_aux₁ (X : C) :
  (α_ (𝟙_ C) (𝟙_ C) X).hom ≫ (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((λ_ X).hom ⊗ 𝟙 _) =
  ((λ_ _).hom ⊗ 𝟙 X) ≫ (β_ X (𝟙_ C)).inv :=
by { rw [←left_unitor_tensor, left_unitor_naturality], simp, }

lemma braiding_left_unitor_aux₂ (X : C) :
  ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C))) = (ρ_ X).hom ⊗ (𝟙 (𝟙_ C)) :=
calc ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
    = ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
        ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
         : by coherence
... = ((β_ X (𝟙_ C)).hom ⊗ (𝟙 (𝟙_ C))) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (β_ X _).hom) ≫
        (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
         : by { slice_rhs 3 4 { rw [←id_tensor_comp, iso.hom_inv_id, tensor_id], }, rw [id_comp], }
... = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫
        (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ⊗ (𝟙 (𝟙_ C)))
         : by { slice_lhs 1 3 { rw ←hexagon_forward }, simp only [assoc], }
... = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((λ_ _).hom ⊗ 𝟙 X) ≫ (β_ X _).inv
         : by rw braiding_left_unitor_aux₁
... = (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (λ_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv
         : by { slice_lhs 2 3 { rw [←braiding_naturality] }, simp only [assoc], }
... = (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (λ_ _).hom)
         : by rw [iso.hom_inv_id, comp_id]
... = (ρ_ X).hom ⊗ (𝟙 (𝟙_ C))
         : by rw triangle

@[simp]
lemma braiding_left_unitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom :=
by rw [←tensor_right_iff, comp_tensor_id, braiding_left_unitor_aux₂]

lemma braiding_right_unitor_aux₁ (X : C) :
  (α_ X (𝟙_ C) (𝟙_ C)).inv ≫ ((β_ (𝟙_ C) X).inv ⊗ 𝟙 (𝟙_ C)) ≫ (α_ _ X _).hom ≫ (𝟙 _ ⊗ (ρ_ X).hom) =
  (𝟙 X ⊗ (ρ_ _).hom) ≫ (β_ (𝟙_ C) X).inv :=
by { rw [←right_unitor_tensor, right_unitor_naturality], simp, }

lemma braiding_right_unitor_aux₂ (X : C) :
  ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom) = (𝟙 (𝟙_ C)) ⊗ (λ_ X).hom :=
calc ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
    = ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫
        ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
         : by coherence
... = ((𝟙 (𝟙_ C)) ⊗ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ⊗ 𝟙 _) ≫
        ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
         : by { slice_rhs 3 4 { rw [←comp_tensor_id, iso.hom_inv_id, tensor_id], }, rw [id_comp], }
... = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫
        (α_ _ _ _).inv ≫ ((β_ _ X).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ X).hom)
         : by { slice_lhs 1 3 { rw ←hexagon_reverse }, simp only [assoc], }
... = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (𝟙 X ⊗ (ρ_ _).hom) ≫ (β_ _ X).inv
         : by rw braiding_right_unitor_aux₁
... = (α_ _ _ _).inv ≫ ((ρ_ _).hom ⊗ 𝟙 _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv
         : by { slice_lhs 2 3 { rw [←braiding_naturality] }, simp only [assoc], }
... = (α_ _ _ _).inv ≫ ((ρ_ _).hom ⊗ 𝟙 _)
         : by rw [iso.hom_inv_id, comp_id]
... = (𝟙 (𝟙_ C)) ⊗ (λ_ X).hom
         : by rw [triangle_assoc_comp_right]

@[simp]
lemma braiding_right_unitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (λ_ X).hom :=
by rw [←tensor_left_iff, id_tensor_comp, braiding_right_unitor_aux₂]

@[simp]
lemma left_unitor_inv_braiding (X : C) : (λ_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv :=
begin
  apply (cancel_mono (ρ_ X).hom).1,
  simp only [assoc, braiding_right_unitor, iso.inv_hom_id],
end

@[simp]
lemma right_unitor_inv_braiding (X : C) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (λ_ X).inv :=
begin
  apply (cancel_mono (λ_ X).hom).1,
  simp only [assoc, braiding_left_unitor, iso.inv_hom_id],
end

end

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric.

See <https://stacks.math.columbia.edu/tag/0FFW>.
-/
class symmetric_category (C : Type u) [category.{v} C] [monoidal_category.{v} C]
   extends braided_category.{v} C :=
-- braiding symmetric:
(symmetry' : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) . obviously)

restate_axiom symmetric_category.symmetry'
attribute [simp,reassoc] symmetric_category.symmetry

initialize_simps_projections symmetric_category
  (to_braided_category_braiding → braiding, -to_braided_category)

variables (C : Type u₁) [category.{v₁} C] [monoidal_category C] [braided_category C]
variables (D : Type u₂) [category.{v₂} D] [monoidal_category D] [braided_category D]
variables (E : Type u₃) [category.{v₃} E] [monoidal_category E] [braided_category E]

/--
A lax braided functor between braided monoidal categories is a lax monoidal functor
which preserves the braiding.
-/
structure lax_braided_functor extends lax_monoidal_functor C D :=
(braided' : ∀ X Y : C, μ X Y ≫ map (β_ X Y).hom = (β_ (obj X) (obj Y)).hom ≫ μ Y X . obviously)

restate_axiom lax_braided_functor.braided'

namespace lax_braided_functor

/-- The identity lax braided monoidal functor. -/
@[simps] def id : lax_braided_functor C C :=
{ .. monoidal_functor.id C }

instance : inhabited (lax_braided_functor C C) := ⟨id C⟩

variables {C D E}

/-- The composition of lax braided monoidal functors. -/
@[simps]
def comp (F : lax_braided_functor C D) (G : lax_braided_functor D E) : lax_braided_functor C E :=
{ braided' := λ X Y,
  begin
    dsimp,
    slice_lhs 2 3 { rw [←category_theory.functor.map_comp, F.braided,
      category_theory.functor.map_comp], },
    slice_lhs 1 2 { rw [G.braided], },
    simp only [category.assoc],
  end,
  ..(lax_monoidal_functor.comp F.to_lax_monoidal_functor G.to_lax_monoidal_functor) }

instance category_lax_braided_functor : category (lax_braided_functor C D) :=
induced_category.category lax_braided_functor.to_lax_monoidal_functor

@[simp] lemma comp_to_nat_trans {F G H : lax_braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

/--
Interpret a natural isomorphism of the underlyling lax monoidal functors as an
isomorphism of the lax braided monoidal functors.
-/
@[simps]
def mk_iso {F G : lax_braided_functor C D}
  (i : F.to_lax_monoidal_functor ≅ G.to_lax_monoidal_functor) : F ≅ G :=
{ ..i }

end lax_braided_functor

/--
A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
structure braided_functor extends monoidal_functor C D :=
-- Note this is stated differently than for `lax_braided_functor`.
-- We move the `μ X Y` to the right hand side,
-- so that this makes a good `@[simp]` lemma.
(braided' :
  ∀ X Y : C, map (β_ X Y).hom = inv (μ X Y) ≫ (β_ (obj X) (obj Y)).hom ≫ μ Y X . obviously)

restate_axiom braided_functor.braided'
attribute [simp] braided_functor.braided

/-- A braided category with a braided functor to a symmetric category is itself symmetric. -/
def symmetric_category_of_faithful {C D : Type*} [category C] [category D]
  [monoidal_category C] [monoidal_category D] [braided_category C] [symmetric_category D]
  (F : braided_functor C D) [faithful F.to_functor] : symmetric_category C :=
{ symmetry' := λ X Y, F.to_functor.map_injective (by simp), }

namespace braided_functor

/-- Turn a braided functor into a lax braided functor. -/
@[simps]
def to_lax_braided_functor (F : braided_functor C D) : lax_braided_functor C D :=
{ braided' := λ X Y, by { rw F.braided, simp, }
  .. F }

/-- The identity braided monoidal functor. -/
@[simps] def id : braided_functor C C :=
{ .. monoidal_functor.id C }

instance : inhabited (braided_functor C C) := ⟨id C⟩

variables {C D E}

/-- The composition of braided monoidal functors. -/
@[simps]
def comp (F : braided_functor C D) (G : braided_functor D E) : braided_functor C E :=
{ ..(monoidal_functor.comp F.to_monoidal_functor G.to_monoidal_functor) }

instance category_braided_functor : category (braided_functor C D) :=
induced_category.category braided_functor.to_monoidal_functor

@[simp] lemma comp_to_nat_trans {F G H : braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

/--
Interpret a natural isomorphism of the underlyling monoidal functors as an
isomorphism of the braided monoidal functors.
-/
@[simps]
def mk_iso {F G : braided_functor C D}
  (i : F.to_monoidal_functor ≅ G.to_monoidal_functor) : F ≅ G :=
{ ..i }


end braided_functor

section comm_monoid

variables (M : Type u) [comm_monoid M]

instance : braided_category (discrete M) :=
{ braiding := λ X Y, discrete.eq_to_iso (mul_comm X.as Y.as), }

variables {M} {N : Type u} [comm_monoid N]

/--
A multiplicative morphism between commutative monoids gives a braided functor between
the corresponding discrete braided monoidal categories.
-/
@[simps]
def discrete.braided_functor (F : M →* N) : braided_functor (discrete M) (discrete N) :=
{ ..discrete.monoidal_functor F }

end comm_monoid

section tensor

/-- The strength of the tensor product functor from `C × C` to `C`. -/
def tensor_μ (X Y : C × C) : (tensor C).obj X ⊗ (tensor C).obj Y ⟶ (tensor C).obj (X ⊗ Y) :=
(α_ X.1 X.2 (Y.1 ⊗ Y.2)).hom ≫ (𝟙 X.1 ⊗ (α_ X.2 Y.1 Y.2).inv) ≫
  (𝟙 X.1 ⊗ ((β_ X.2 Y.1).hom ⊗ 𝟙 Y.2)) ≫
  (𝟙 X.1 ⊗ (α_ Y.1 X.2 Y.2).hom) ≫ (α_ X.1 Y.1 (X.2 ⊗ Y.2)).inv

lemma tensor_μ_def₁ (X₁ X₂ Y₁ Y₂ : C) :
    tensor_μ C (X₁, X₂) (Y₁, Y₂) ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ≫ (𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).inv)
  = (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ≫ (𝟙 X₁ ⊗ (α_ X₂ Y₁ Y₂).inv) ≫ (𝟙 X₁ ⊗ ((β_ X₂ Y₁).hom ⊗ 𝟙 Y₂)) :=
by { dsimp [tensor_μ], simp }

lemma tensor_μ_def₂ (X₁ X₂ Y₁ Y₂ : C) :
    (𝟙 X₁ ⊗ (α_ X₂ Y₁ Y₂).hom) ≫ (α_ X₁ X₂ (Y₁ ⊗ Y₂)).inv ≫ tensor_μ C (X₁, X₂) (Y₁, Y₂)
  = (𝟙 X₁ ⊗ ((β_ X₂ Y₁).hom ⊗ 𝟙 Y₂)) ≫ (𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).hom) ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv :=
by { dsimp [tensor_μ], simp }

lemma tensor_μ_natural {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁) (g₂ : U₂ ⟶ V₂) :
  ((f₁ ⊗ f₂) ⊗ (g₁ ⊗ g₂)) ≫ tensor_μ C (Y₁, Y₂) (V₁, V₂) =
    tensor_μ C (X₁, X₂) (U₁, U₂) ≫ ((f₁ ⊗ g₁) ⊗ (f₂ ⊗ g₂)) :=
begin
  dsimp [tensor_μ],
  slice_lhs 1 2 { rw [associator_naturality] },
  slice_lhs 2 3 { rw [←tensor_comp,
                      comp_id f₁, ←id_comp f₁,
                      associator_inv_naturality,
                      tensor_comp] },
  slice_lhs 3 4 { rw [←tensor_comp, ←tensor_comp,
                      comp_id f₁, ←id_comp f₁,
                      comp_id g₂, ←id_comp g₂,
                      braiding_naturality,
                      tensor_comp, tensor_comp] },
  slice_lhs 4 5 { rw [←tensor_comp,
                      comp_id f₁, ←id_comp f₁,
                      associator_naturality,
                      tensor_comp] },
  slice_lhs 5 6 { rw [associator_inv_naturality] },
  simp only [assoc],
end

lemma tensor_left_unitality (X₁ X₂ : C) :
    (λ_ (X₁ ⊗ X₂)).hom
  = ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫
    tensor_μ C (𝟙_ C, 𝟙_ C) (X₁, X₂) ≫
    ((λ_ X₁).hom ⊗ (λ_ X₂).hom) :=
begin
  dsimp [tensor_μ],
  have :
      ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫
      (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
      (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv)
    = 𝟙 (𝟙_ C) ⊗ ((λ_ X₁).inv ⊗ 𝟙 X₂) := by pure_coherence,
  slice_rhs 1 3 { rw this }, clear this,
  slice_rhs 1 2 { rw [←tensor_comp, ←tensor_comp,
                      comp_id, comp_id,
                      left_unitor_inv_braiding] },
  simp only [assoc],
  coherence,
end

lemma tensor_right_unitality (X₁ X₂ : C) :
    (ρ_ (X₁ ⊗ X₂)).hom
  = (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) ≫
    tensor_μ C (X₁, X₂) (𝟙_ C, 𝟙_ C) ≫
    ((ρ_ X₁).hom ⊗ (ρ_ X₂).hom) :=
begin
  dsimp [tensor_μ],
  have :
      (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) ≫
      (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).hom ≫
      (𝟙 X₁ ⊗ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv)
    = (α_ X₁ X₂ (𝟙_ C)).hom ≫
      (𝟙 X₁ ⊗ ((ρ_ X₂).inv ⊗ 𝟙 (𝟙_ C))) := by pure_coherence,
  slice_rhs 1 3 { rw this }, clear this,
  slice_rhs 2 3 { rw [←tensor_comp, ←tensor_comp,
                      comp_id, comp_id,
                      right_unitor_inv_braiding] },
  simp only [assoc],
  coherence,
end

/-
Diagram B6 from Proposition 1 of [Joyal and Street, *Braided monoidal categories*][Joyal_Street].
-/
lemma tensor_associativity_aux (W X Y Z : C) :
    ((β_ W X).hom ⊗ 𝟙 (Y ⊗ Z)) ≫
    (α_ X W (Y ⊗ Z)).hom ≫
    (𝟙 X ⊗ (α_ W Y Z).inv) ≫
    (𝟙 X ⊗ (β_ (W ⊗ Y) Z).hom) ≫
    (𝟙 X ⊗ (α_ Z W Y).inv)
  = (𝟙 (W ⊗ X) ⊗ (β_ Y Z).hom) ≫
    (α_ (W ⊗ X) Z Y).inv ≫
    ((α_ W X Z).hom ⊗ 𝟙 Y) ≫
    ((β_ W (X ⊗ Z)).hom ⊗ 𝟙 Y) ≫
    ((α_ X Z W).hom ⊗ 𝟙 Y) ≫
    (α_ X (Z ⊗ W) Y).hom :=
begin
  slice_rhs 3 5 { rw [←tensor_comp, ←tensor_comp,
                      hexagon_forward,
                      tensor_comp, tensor_comp] },
  slice_rhs 5 6 { rw [associator_naturality] },
  slice_rhs 2 3 { rw [←associator_inv_naturality] },
  slice_rhs 3 5 { rw [←pentagon_hom_inv] },
  slice_rhs 1 2 { rw [tensor_id,
                      id_tensor_comp_tensor_id,
                      ←tensor_id_comp_id_tensor] },
  slice_rhs 2 3 { rw [← tensor_id, associator_naturality] },
  slice_rhs 3 5 { rw [←tensor_comp, ←tensor_comp,
                      ←hexagon_reverse,
                      tensor_comp, tensor_comp] },
end

lemma tensor_associativity (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) :
    (tensor_μ C (X₁, X₂) (Y₁, Y₂) ⊗ 𝟙 (Z₁ ⊗ Z₂)) ≫
    tensor_μ C (X₁ ⊗ Y₁, X₂ ⊗ Y₂) (Z₁, Z₂) ≫
    ((α_ X₁ Y₁ Z₁).hom ⊗ (α_ X₂ Y₂ Z₂).hom)
  = (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
    (𝟙 (X₁ ⊗ X₂) ⊗ tensor_μ C (Y₁, Y₂) (Z₁, Z₂)) ≫
    tensor_μ C (X₁, X₂) (Y₁ ⊗ Z₁, Y₂ ⊗ Z₂) :=
begin
  have :
      ((α_ X₁ Y₁ Z₁).hom ⊗ (α_ X₂ Y₂ Z₂).hom)
    = (α_ (X₁ ⊗ Y₁) Z₁ ((X₂ ⊗ Y₂) ⊗ Z₂)).hom ≫
      (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ Z₁ (X₂ ⊗ Y₂) Z₂).inv) ≫
      (α_ X₁ Y₁ ((Z₁ ⊗ (X₂ ⊗ Y₂)) ⊗ Z₂)).hom ≫
      (𝟙 X₁ ⊗ (α_ Y₁ (Z₁ ⊗ (X₂ ⊗ Y₂)) Z₂).inv) ≫
      (α_ X₁ (Y₁ ⊗ (Z₁ ⊗ (X₂ ⊗ Y₂))) Z₂).inv ≫
      ((𝟙 X₁ ⊗ (𝟙 Y₁ ⊗ (α_ Z₁ X₂ Y₂).inv)) ⊗ 𝟙 Z₂) ≫
      ((𝟙 X₁ ⊗ (α_ Y₁ (Z₁ ⊗ X₂) Y₂).inv) ⊗ 𝟙 Z₂) ≫
      ((𝟙 X₁ ⊗ ((α_ Y₁ Z₁ X₂).inv ⊗ 𝟙 Y₂)) ⊗ 𝟙 Z₂) ≫
      (α_ X₁ (((Y₁ ⊗ Z₁) ⊗ X₂) ⊗ Y₂) Z₂).hom ≫
      (𝟙 X₁ ⊗ (α_ ((Y₁ ⊗ Z₁) ⊗ X₂) Y₂ Z₂).hom) ≫
      (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ Z₁) X₂ (Y₂ ⊗ Z₂)).hom) ≫
      (α_ X₁ (Y₁ ⊗ Z₁) (X₂ ⊗ (Y₂ ⊗ Z₂))).inv := by pure_coherence,
  rw this, clear this,
  slice_lhs 2 4 { rw [tensor_μ_def₁] },
  slice_lhs 4 5 { rw [←tensor_id, associator_naturality] },
  slice_lhs 5 6 { rw [←tensor_comp,
                      associator_inv_naturality,
                      tensor_comp] },
  slice_lhs 6 7 { rw [associator_inv_naturality] },
  have :
      (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
      (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ (X₂ ⊗ Y₂) Z₁ Z₂).inv) ≫
      (α_ X₁ Y₁ (((X₂ ⊗ Y₂) ⊗ Z₁) ⊗ Z₂)).hom ≫
      (𝟙 X₁ ⊗ (α_ Y₁ ((X₂ ⊗ Y₂) ⊗ Z₁) Z₂).inv) ≫
      (α_ X₁ (Y₁ ⊗ ((X₂ ⊗ Y₂) ⊗ Z₁)) Z₂).inv
    = ((α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ⊗ 𝟙 (Z₁ ⊗ Z₂)) ≫
      ((𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).inv) ⊗ 𝟙 (Z₁ ⊗ Z₂)) ≫
      (α_ (X₁ ⊗ ((Y₁ ⊗ X₂) ⊗ Y₂)) Z₁ Z₂).inv ≫
      ((α_ X₁ ((Y₁ ⊗ X₂) ⊗ Y₂) Z₁).hom ⊗ 𝟙 Z₂) ≫
      ((𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) Y₂ Z₁).hom) ⊗ 𝟙 Z₂) ≫
      ((𝟙 X₁ ⊗ (α_ Y₁ X₂ (Y₂ ⊗ Z₁)).hom) ⊗ 𝟙 Z₂) ≫
      ((𝟙 X₁ ⊗ (𝟙 Y₁ ⊗ (α_ X₂ Y₂ Z₁).inv)) ⊗ 𝟙 Z₂) := by pure_coherence,
  slice_lhs 2 6 { rw this }, clear this,
  slice_lhs 1 3 { rw [←tensor_comp, ←tensor_comp,
                      tensor_μ_def₁,
                      tensor_comp, tensor_comp] },
  slice_lhs 3 4 { rw [←tensor_id,
                      associator_inv_naturality] },
  slice_lhs 4 5 { rw [←tensor_comp,
                      associator_naturality,
                      tensor_comp] },
  slice_lhs 5 6 { rw [←tensor_comp, ←tensor_comp,
                      associator_naturality,
                      tensor_comp, tensor_comp] },
  slice_lhs 6 10 { rw [←tensor_comp, ←tensor_comp, ←tensor_comp, ←tensor_comp,
                       ←tensor_comp, ←tensor_comp, ←tensor_comp, ←tensor_comp,
                       tensor_id,
                       tensor_associativity_aux,
                       ←tensor_id,
                       ←id_comp (𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁),
                       ←id_comp (𝟙 Z₂ ≫ 𝟙 Z₂ ≫ 𝟙 Z₂ ≫ 𝟙 Z₂ ≫ 𝟙 Z₂),
                       tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp,
                       tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp] },
  slice_lhs 11 12 { rw [←tensor_comp, ←tensor_comp,
                        iso.hom_inv_id],
                    simp },
  simp only [assoc, id_comp],
  slice_lhs 10 11 { rw [←tensor_comp, ←tensor_comp, ←tensor_comp,
                        iso.hom_inv_id],
                    simp },
  simp only [assoc, id_comp],
  slice_lhs 9 10 { rw [associator_naturality] },
  slice_lhs 10 11 { rw [←tensor_comp,
                        associator_naturality,
                        tensor_comp] },
  slice_lhs 11 13 { rw [tensor_id, ←tensor_μ_def₂] },
  have :
      ((𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁) Z₁ Y₂).inv) ⊗ 𝟙 Z₂) ≫
      ((𝟙 X₁ ⊗ (α_ X₂ Y₁ Z₁).hom ⊗ 𝟙 Y₂) ⊗ 𝟙 Z₂) ≫
      (α_ X₁ ((X₂ ⊗ Y₁ ⊗ Z₁) ⊗ Y₂) Z₂).hom ≫
      (𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁ ⊗ Z₁) Y₂ Z₂).hom) ≫
      (𝟙 X₁ ⊗ (α_ X₂ (Y₁ ⊗ Z₁) (Y₂ ⊗ Z₂)).hom) ≫
      (α_ X₁ X₂ ((Y₁ ⊗ Z₁) ⊗ Y₂ ⊗ Z₂)).inv
    = (α_ X₁ ((X₂ ⊗ Y₁) ⊗ (Z₁ ⊗ Y₂)) Z₂).hom ≫
      (𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁) (Z₁ ⊗ Y₂) Z₂).hom) ≫
      (𝟙 X₁ ⊗ (α_ X₂ Y₁ ((Z₁ ⊗ Y₂) ⊗ Z₂)).hom) ≫
      (α_ X₁ X₂ (Y₁ ⊗ ((Z₁ ⊗ Y₂) ⊗ Z₂))).inv ≫
      (𝟙 (X₁ ⊗ X₂) ⊗ (𝟙 Y₁ ⊗ (α_ Z₁ Y₂ Z₂).hom)) ≫
      (𝟙 (X₁ ⊗ X₂) ⊗ (α_ Y₁ Z₁ (Y₂ ⊗ Z₂)).inv) := by pure_coherence,
  slice_lhs 7 12 { rw this }, clear this,
  slice_lhs 6 7 { rw [associator_naturality] },
  slice_lhs 7 8 { rw [←tensor_comp,
                      associator_naturality,
                      tensor_comp] },
  slice_lhs 8 9 { rw [←tensor_comp,
                      associator_naturality,
                      tensor_comp] },
  slice_lhs 9 10 { rw [associator_inv_naturality] },
  slice_lhs 10 12 { rw [←tensor_comp, ←tensor_comp,
                        ←tensor_μ_def₂,
                        tensor_comp, tensor_comp] },
  dsimp,
  coherence,
end

/-- The tensor product functor from `C × C` to `C` as a monoidal functor. -/
@[simps]
def tensor_monoidal : monoidal_functor (C × C) C :=
{ ε := (λ_ (𝟙_ C)).inv,
  μ := λ X Y, tensor_μ C X Y,
  μ_natural' := λ X Y X' Y' f g, tensor_μ_natural C f.1 f.2 g.1 g.2,
  associativity' := λ X Y Z, tensor_associativity C X.1 X.2 Y.1 Y.2 Z.1 Z.2,
  left_unitality' := λ ⟨X₁, X₂⟩, tensor_left_unitality C X₁ X₂,
  right_unitality' := λ ⟨X₁, X₂⟩, tensor_right_unitality C X₁ X₂,
  μ_is_iso := by { dsimp [tensor_μ], apply_instance },
  .. tensor C }

lemma left_unitor_monoidal (X₁ X₂ : C) :
    (λ_ X₁).hom ⊗ (λ_ X₂).hom
  = tensor_μ C (𝟙_ C, X₁) (𝟙_ C, X₂) ≫
    ((λ_ (𝟙_ C)).hom ⊗ 𝟙 (X₁ ⊗ X₂)) ≫
    (λ_ (X₁ ⊗ X₂)).hom :=
begin
  dsimp [tensor_μ],
  have :
      (λ_ X₁).hom ⊗ (λ_ X₂).hom
    = (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).hom ≫
      (𝟙 (𝟙_ C) ⊗ (α_ X₁ (𝟙_ C) X₂).inv) ≫
      (λ_ ((X₁ ⊗ (𝟙_ C)) ⊗ X₂)).hom ≫
      ((ρ_ X₁).hom ⊗ (𝟙 X₂)) := by pure_coherence,
  rw this, clear this,
  rw ←braiding_left_unitor,
  slice_lhs 3 4 { rw [←id_comp (𝟙 X₂), tensor_comp] },
  slice_lhs 3 4 { rw [←left_unitor_naturality] },
  coherence,
end

lemma right_unitor_monoidal (X₁ X₂ : C) :
    (ρ_ X₁).hom ⊗ (ρ_ X₂).hom
  = tensor_μ C (X₁, 𝟙_ C) (X₂, 𝟙_ C) ≫
    (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).hom) ≫
    (ρ_ (X₁ ⊗ X₂)).hom :=
begin
  dsimp [tensor_μ],
  have :
      (ρ_ X₁).hom ⊗ (ρ_ X₂).hom
    = (α_ X₁ (𝟙_ C) (X₂ ⊗ (𝟙_ C))).hom ≫
      (𝟙 X₁ ⊗ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫
      (𝟙 X₁ ⊗ (ρ_ (𝟙_ C ⊗ X₂)).hom) ≫
      (𝟙 X₁ ⊗ (λ_ X₂).hom) := by pure_coherence,
  rw this, clear this,
  rw ←braiding_right_unitor,
  slice_lhs 3 4 { rw [←id_comp (𝟙 X₁), tensor_comp, id_comp] },
  slice_lhs 3 4 { rw [←tensor_comp,
                      ←right_unitor_naturality,
                      tensor_comp] },
  coherence,
end

lemma associator_monoidal_aux (W X Y Z : C) :
    (𝟙 W ⊗ (β_ X (Y ⊗ Z)).hom) ≫
    (𝟙 W ⊗ (α_ Y Z X).hom) ≫
    (α_ W Y (Z ⊗ X)).inv ≫
    ((β_ W Y).hom ⊗ 𝟙 (Z ⊗ X))
  = (α_ W X (Y ⊗ Z)).inv ≫
    (α_ (W ⊗ X) Y Z).inv ≫
    ((β_ (W ⊗ X) Y).hom ⊗ 𝟙 Z) ≫
    ((α_ Y W X).inv ⊗ 𝟙 Z) ≫
    (α_ (Y ⊗ W) X Z).hom ≫
    (𝟙 (Y ⊗ W) ⊗ (β_ X Z).hom) :=
begin
  slice_rhs 1 2 { rw ←pentagon_inv },
  slice_rhs 3 5 { rw [←tensor_comp, ←tensor_comp,
                      hexagon_reverse,
                      tensor_comp, tensor_comp] },
  slice_rhs 5 6 { rw associator_naturality },
  slice_rhs 6 7 { rw [tensor_id,
                      tensor_id_comp_id_tensor,
                      ←id_tensor_comp_tensor_id] },
  slice_rhs 2 3 { rw ←associator_inv_naturality },
  slice_rhs 3 5 { rw pentagon_inv_inv_hom },
  slice_rhs 4 5 { rw [←tensor_id,
                      ←associator_inv_naturality] },
  slice_rhs 2 4 { rw [←tensor_comp, ←tensor_comp,
                      ←hexagon_forward,
                      tensor_comp, tensor_comp] },
  simp,
end

lemma associator_monoidal (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensor_μ C (X₁ ⊗ X₂, X₃) (Y₁ ⊗ Y₂, Y₃) ≫
    (tensor_μ C (X₁, X₂) (Y₁, Y₂) ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
    (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom
  = ((α_ X₁ X₂ X₃).hom ⊗ (α_ Y₁ Y₂ Y₃).hom) ≫
    tensor_μ C (X₁, X₂ ⊗ X₃) (Y₁, Y₂ ⊗ Y₃) ≫
    (𝟙 (X₁ ⊗ Y₁) ⊗ tensor_μ C (X₂, X₃) (Y₂, Y₃)) :=
begin
  have :
      (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom
    = ((α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
      ((𝟙 X₁ ⊗ (α_ Y₁ X₂ Y₂).inv) ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
      (α_ (X₁ ⊗ ((Y₁ ⊗ X₂) ⊗ Y₂)) X₃ Y₃).inv ≫
      ((α_ X₁ ((Y₁ ⊗ X₂) ⊗ Y₂) X₃).hom ⊗ 𝟙 Y₃) ≫
      ((𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) Y₂ X₃).hom) ⊗ 𝟙 Y₃) ≫
      (α_ X₁ ((Y₁ ⊗ X₂) ⊗ (Y₂ ⊗ X₃)) Y₃).hom ≫
      (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) (Y₂ ⊗ X₃) Y₃).hom) ≫
      (𝟙 X₁ ⊗ (α_ Y₁ X₂ ((Y₂ ⊗ X₃) ⊗ Y₃)).hom) ≫
      (α_ X₁ Y₁ (X₂ ⊗ ((Y₂ ⊗ X₃) ⊗ Y₃))).inv ≫
      (𝟙 (X₁ ⊗ Y₁) ⊗ (𝟙 X₂ ⊗ (α_ Y₂ X₃ Y₃).hom)) ≫
      (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ X₂ Y₂ (X₃ ⊗ Y₃)).inv) := by pure_coherence,
  rw this, clear this,
  slice_lhs 2 4 { rw [←tensor_comp, ←tensor_comp,
                      tensor_μ_def₁,
                      tensor_comp, tensor_comp] },
  slice_lhs 4 5 { rw [←tensor_id,
                      associator_inv_naturality] },
  slice_lhs 5 6 { rw [←tensor_comp,
                      associator_naturality,
                      tensor_comp] },
  slice_lhs 6 7 { rw [←tensor_comp, ←tensor_comp,
                      associator_naturality,
                      tensor_comp, tensor_comp] },
  have :
      ((α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
      ((𝟙 X₁ ⊗ (α_ X₂ Y₁ Y₂).inv) ⊗ 𝟙 (X₃ ⊗ Y₃)) ≫
      (α_ (X₁ ⊗ ((X₂ ⊗ Y₁) ⊗ Y₂)) X₃ Y₃).inv ≫
      ((α_ X₁ ((X₂ ⊗ Y₁) ⊗ Y₂) X₃).hom ⊗ 𝟙 Y₃) ≫
      ((𝟙 X₁ ⊗ (α_ (X₂ ⊗ Y₁) Y₂ X₃).hom) ⊗ 𝟙 Y₃)
    = (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (X₃ ⊗ Y₃)).hom ≫
      (𝟙 (X₁ ⊗ X₂) ⊗ (α_ (Y₁ ⊗ Y₂) X₃ Y₃).inv) ≫
      (α_ X₁ X₂ (((Y₁ ⊗ Y₂) ⊗ X₃) ⊗ Y₃)).hom ≫
      (𝟙 X₁ ⊗ (α_ X₂ ((Y₁ ⊗ Y₂) ⊗ X₃) Y₃).inv) ≫
      (α_ X₁ (X₂ ⊗ ((Y₁ ⊗ Y₂) ⊗ X₃)) Y₃).inv ≫
      ((𝟙 X₁ ⊗ (𝟙 X₂ ⊗ (α_ Y₁ Y₂ X₃).hom)) ⊗ 𝟙 Y₃) ≫
      ((𝟙 X₁ ⊗ (α_ X₂ Y₁ (Y₂ ⊗ X₃)).inv) ⊗ 𝟙 Y₃) := by pure_coherence,
  slice_lhs 2 6 { rw this }, clear this,
  slice_lhs 1 3 { rw tensor_μ_def₁ },
  slice_lhs 3 4 { rw [←tensor_id,
                      associator_naturality] },
  slice_lhs 4 5 { rw [←tensor_comp,
                      associator_inv_naturality,
                      tensor_comp] },
  slice_lhs 5 6 { rw associator_inv_naturality },
  slice_lhs 6 9 { rw [←tensor_comp, ←tensor_comp, ←tensor_comp,
                      ←tensor_comp, ←tensor_comp, ←tensor_comp,
                      tensor_id,
                      associator_monoidal_aux,
                      ←id_comp (𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁),
                      ←id_comp (𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁ ≫ 𝟙 X₁),
                      ←id_comp (𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃),
                      ←id_comp (𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃ ≫ 𝟙 Y₃),
                      tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp,
                      tensor_comp, tensor_comp, tensor_comp, tensor_comp, tensor_comp] },
  slice_lhs 11 12 { rw associator_naturality },
  slice_lhs 12 13 { rw [←tensor_comp,
                        associator_naturality,
                        tensor_comp] },
  slice_lhs 13 14 { rw [←tensor_comp, ←tensor_id,
                        associator_naturality,
                        tensor_comp] },
  slice_lhs 14 15 { rw associator_inv_naturality },
  slice_lhs 15 17 { rw [tensor_id, ←tensor_comp, ←tensor_comp,
                        ←tensor_μ_def₂,
                        tensor_comp, tensor_comp] },
  have :
      ((𝟙 X₁ ⊗ ((α_ Y₁ X₂ X₃).inv ⊗ 𝟙 Y₂)) ⊗ 𝟙 Y₃) ≫
      ((𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) X₃ Y₂).hom) ⊗ 𝟙 Y₃) ≫
      (α_ X₁ ((Y₁ ⊗ X₂) ⊗ (X₃ ⊗ Y₂)) Y₃).hom ≫
      (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ X₂) (X₃ ⊗ Y₂) Y₃).hom) ≫
      (𝟙 X₁ ⊗ (α_ Y₁ X₂ ((X₃ ⊗ Y₂) ⊗ Y₃)).hom) ≫
      (α_ X₁ Y₁ (X₂ ⊗ ((X₃ ⊗ Y₂) ⊗ Y₃))).inv ≫
      (𝟙 (X₁ ⊗ Y₁) ⊗ (𝟙 X₂ ⊗ (α_ X₃ Y₂ Y₃).hom)) ≫
      (𝟙 (X₁ ⊗ Y₁) ⊗ (α_ X₂ X₃ (Y₂ ⊗ Y₃)).inv)
    = (α_ X₁ ((Y₁ ⊗ (X₂ ⊗ X₃)) ⊗ Y₂) Y₃).hom ≫
      (𝟙 X₁ ⊗ (α_ (Y₁ ⊗ (X₂ ⊗ X₃)) Y₂ Y₃).hom) ≫
      (𝟙 X₁ ⊗ (α_ Y₁ (X₂ ⊗ X₃) (Y₂ ⊗ Y₃)).hom) ≫
      (α_ X₁ Y₁ ((X₂ ⊗ X₃) ⊗ (Y₂ ⊗ Y₃))).inv := by pure_coherence,
  slice_lhs 9 16 { rw this }, clear this,
  slice_lhs 8 9 { rw associator_naturality },
  slice_lhs 9 10 { rw [←tensor_comp,
                       associator_naturality,
                       tensor_comp] },
  slice_lhs 10 12 { rw [tensor_id,
                        ←tensor_μ_def₂] },
  dsimp,
  coherence,
end

end tensor

end category_theory
