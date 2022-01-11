 /-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.functor

/-!
# Pseudonatural transformations

Just as there are natural transformations between functors, there are pseudonatural
transformations between oplax_functors. The equality in the naturality of natural
transformations is replaced by an specified isomorphism
`F.map f ≫ app b ≅ app a ≫ G.map f`
in the case of pseudonatural transformations.

We give a bicategory structure on the oplax_functors between bicategories. In this bicategory,
* 1-morphisms are are the pseudonatural transformations, given by `oplax_nat_trans F G`,
* the composition of 1-morphisms is the vertical composition, given by `η.vcomp θ`,
* 2-morphisms are the modifications, given by `modification η θ`.
-/

open category_theory

universes w₁ w₂ v₁ v₂ u₁ u₂

namespace category_theory

open category bicategory
open_locale bicategory

variables
{B : Type u₁} [bicategory.{w₁ v₁} B]
{C : Type u₂} [bicategory.{w₂ v₂} C]

/--
If `η` is a pseudonatural transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have an isomorphism
`η.naturality f : F.map f ≫ app b ≅ app a ≫ G.map f` for each 1-morphisms `f : a ⟶ b`.
This family of isomorphisms satisfies certain equations.
-/
structure oplax_nat_trans (F G : oplax_functor B C) :=
(app (a : B) : F.obj a ⟶ G.obj a)
(naturality {a b: B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f)
(naturality_naturality' : ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
  (F.map₂ η ▷ _) ≫ naturality g = naturality f ≫ (_ ◁ G.map₂ η) . obviously)
(naturality_id' : ∀ a : B,
  (naturality (𝟙 a)) ≫ (_ ◁ G.map_id a)
  = (F.map_id a ▷ _) ≫ (λ_ _).hom  ≫ (ρ_ _).inv . obviously)
(naturality_comp' : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
   (naturality (f ≫ g)) ≫ (_ ◁ (G.map_comp f g))
  = (F.map_comp f g ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ naturality g)
  ≫ (α_ _ _ _).inv ≫ (naturality f ▷ G.map g)
  ≫ (α_ _ _ _).hom  . obviously)

restate_axiom oplax_nat_trans.naturality_naturality'
attribute [simp, reassoc] oplax_nat_trans.naturality_naturality
restate_axiom oplax_nat_trans.naturality_comp'
attribute [simp, reassoc] oplax_nat_trans.naturality_comp
restate_axiom oplax_nat_trans.naturality_id'
attribute [simp, reassoc] oplax_nat_trans.naturality_id

structure pseudonat_trans (F G : pseudofunctor B C) extends oplax_nat_trans F.to_oplax_functor G.to_oplax_functor :=
(naturality_iso {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f)
(naturality_iso_hom' : ∀ {a b : B} (f : a ⟶ b), (naturality_iso f).hom = naturality f . obviously)

restate_axiom pseudonat_trans.naturality_iso_hom'
attribute [simp] pseudonat_trans.naturality_iso_hom

namespace oplax_nat_trans

/--
The identity pseudonatural transformation.
-/
@[simps]
def id (F : oplax_functor B C) : oplax_nat_trans F F :=
{ app := λ a, 𝟙 (F.obj a),
  naturality := λ a b f, (ρ_ _).hom ≫ (λ_ _).inv,
  naturality_naturality' := λ a b f f' η, by
  { rw [assoc, ←left_unitor_inv_naturality, ←right_unitor_naturality_assoc] },
  naturality_comp' := λ a b c f g, by
  { rw [assoc, ←left_unitor_inv_naturality, ←right_unitor_naturality_assoc],
    simp only [triangle_assoc_comp_right_assoc, right_unitor_comp, left_unitor_comp_inv, bicategory.whisker_right_comp,
      inv_hom_whisker_left_assoc, assoc, bicategory.whisker_left_comp], },
  naturality_id' := λ a, by
  { rw [assoc, ←left_unitor_inv_naturality, ←right_unitor_naturality_assoc,
      unitors_equal, unitors_inv_equal] } }

instance (F : oplax_functor B C) : inhabited (oplax_nat_trans F F) := ⟨id F⟩

section
variables {F G H : oplax_functor B C}
(φ : oplax_nat_trans F G) (ψ : oplax_nat_trans G H) {a b c : B} {a' : C}

@[simp, reassoc]
lemma whisker_left_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (η : g ⟶ h) :
  (f ◁ (G.map₂ η ▷ ψ.app b)) ≫ (f ◁ ψ.naturality h)
  = (f ◁ ψ.naturality g) ≫ (f ◁ (ψ.app a ◁ H.map₂ η)) :=
by { simp only [←bicategory.whisker_left_comp], rw naturality_naturality }

@[simp, reassoc]
lemma whisker_right_naturality_naturality {f g : a ⟶ b} (η : f ⟶ g) (h : G.obj b ⟶ a') :
  ((F.map₂ η ▷ φ.app b) ▷ h) ≫ (φ.naturality g ▷ h)
  = (φ.naturality f ▷ h) ≫ ((φ.app a ◁ G.map₂ η) ▷ h) :=
by { simp only [←bicategory.whisker_right_comp], rw naturality_naturality }

@[simp, reassoc]
lemma whisker_left_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
  (f ◁ ψ.naturality (g ≫ h)) ≫ (f ◁ (_ ◁ H.map_comp g h))
  = (f ◁ (G.map_comp g h ▷ _)) ≫(f ◁ (α_ _ _ _).hom) ≫ (f ◁ (_ ◁ ψ.naturality h))
  ≫ (f ◁ (α_ _ _ _).inv) ≫ (f ◁ (ψ.naturality g ▷ H.map h))
  ≫ (f ◁ (α_ _ _ _).hom)  :=
by { simp only [←bicategory.whisker_left_comp], rw naturality_comp }

@[simp, reassoc]
lemma whisker_right_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a')  :
  (φ.naturality (f ≫ g) ▷ h) ≫ ((_ ◁ G.map_comp f g) ▷ h)
  = ((F.map_comp f g ▷ _) ▷ h) ≫ ((α_ _ _ _).hom ▷ h) ≫ ((_ ◁ φ.naturality g) ▷ h)
  ≫ ((α_ _ _ _).inv ▷ h) ≫ ((φ.naturality f ▷ G.map g) ▷ h)
  ≫ ((α_ _ _ _).hom ▷ h)  :=
by { simp only [←bicategory.whisker_right_comp], rw naturality_comp }

@[simp, reassoc]
lemma whisker_left_naturality_id (f : a' ⟶ G.obj a) :
   (f ◁ ψ.naturality (𝟙 a)) ≫ (f ◁ (_ ◁ H.map_id a))
  = (f ◁ (G.map_id a ▷ _)) ≫ (f ◁ (λ_ _).hom) ≫ (f ◁ (ρ_ _).inv) :=
by { simp only [←bicategory.whisker_left_comp], rw naturality_id }

@[simp, reassoc]
lemma whisker_right_naturality_id (f : G.obj a ⟶ a') :
   ((φ.naturality (𝟙 a)) ▷ f)≫ ((_ ◁ (G.map_id a)) ▷ f)
  = ((F.map_id a ▷ _) ▷ f) ≫ ((λ_ _).hom ▷ f) ≫ ((ρ_ _).inv ▷ f) :=
by { simp only [←bicategory.whisker_right_comp], rw naturality_id }

end

/--
Vertical composition of pseudonatural transformations.
-/
@[simps]
def vcomp {F G H : oplax_functor B C} (η : oplax_nat_trans F G) (θ : oplax_nat_trans G H) :
  oplax_nat_trans F H :=
{ app := λ a, η.app a ≫ θ.app a,
  naturality := λ a b f,
    (α_ _ _ _).inv ≫ (η.naturality f ▷ θ.app b) ≫ (α_ _ _ _).hom ≫
    (η.app a ◁ θ.naturality f) ≫ (α_ _ _ _).inv,
  naturality_naturality' := λ a b f g ι, by
  { simp only [bicategory.whisker_right_comp, assoc, bicategory.whisker_left_comp],
    rw [←associator_inv_naturality_right, ←whisker_left_naturality_naturality_assoc,
        ←associator_naturality_middle_assoc, ←whisker_right_naturality_naturality_assoc,
        ←associator_inv_naturality_left_assoc] },
  naturality_comp' := λ a b c f g, by
  { simp only [bicategory.whisker_right_comp, assoc, bicategory.whisker_left_comp],
    rw [←associator_inv_naturality_right, whisker_left_naturality_comp_assoc,
        ←associator_naturality_middle_assoc, whisker_right_naturality_comp_assoc,
        ←associator_inv_naturality_left_assoc],
    rw [←pentagon_hom_hom_inv_inv_hom, associator_naturality_middle_assoc,
        ←pentagon_inv_hom_hom_hom_inv_assoc, ←associator_naturality_middle_assoc],
    slice_rhs 5 13
    { rw [←pentagon_inv_hom_hom_hom_hom_assoc, ←pentagon_hom_hom_inv_hom_hom,
          associator_naturality_left_assoc, ←associator_naturality_right_assoc,
          pentagon_inv_inv_hom_hom_inv_assoc, inv_hom_whisker_left_assoc, iso.hom_inv_id_assoc,
          whisker_exchange_assoc, associator_naturality_right_assoc,
          ←associator_naturality_left_assoc, ←pentagon_assoc] },
    simp only [assoc] },
  naturality_id' := λ a, by
  { simp only [bicategory.whisker_right_comp, assoc, bicategory.whisker_left_comp],
    rw [←associator_inv_naturality_right, whisker_left_naturality_id_assoc,
        ←associator_naturality_middle_assoc, whisker_right_naturality_id_assoc,
        ←associator_inv_naturality_left_assoc],
    simp only [left_unitor_comp, triangle_assoc, inv_hom_whisker_right_assoc, assoc,
      right_unitor_comp_inv] } }

end oplax_nat_trans

namespace pseudonat_trans

/--
The identity pseudonatural transformation.
-/
@[simps]
def id (F : pseudofunctor B C) : pseudonat_trans F F :=
{ naturality_iso := λ a b f, (ρ_ _) ≪≫ (λ_ _).symm,
  .. oplax_nat_trans.id F.to_oplax_functor }

/--
Vertical composition of pseudonatural transformations.
-/
@[simps]
def vcomp {F G H : pseudofunctor B C} (η : pseudonat_trans F G) (θ : pseudonat_trans G H) :
  pseudonat_trans F H :=
{ naturality_iso := λ a b f,
    (α_ _ _ _).symm ≪≫ (whisker_right_iso (η.naturality_iso f) (θ.app b)) ≪≫ (α_ _ _ _) ≪≫
    (whisker_left_iso (η.app a) (θ.naturality_iso f)) ≪≫ (α_ _ _ _).symm,
  .. η.to_oplax_nat_trans.vcomp θ.to_oplax_nat_trans }

end pseudonat_trans

section
variables {F G H I : oplax_functor B C}

namespace oplax_nat_trans

/--
A modification `Γ` between pseudonatural transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure modification (η θ : oplax_nat_trans F G) :=
(app (a : B) : η.app a ⟶ θ.app a)
(naturality' : ∀ {a b : B} (f : a ⟶ b),
  (F.map f ◁ app b) ≫ (θ.naturality f)
  = (η.naturality f) ≫ (app a ▷ G.map f) . obviously)

restate_axiom modification.naturality'
attribute [reassoc] modification.naturality

namespace modification

/--
Vertical composition of modifications.
-/
@[simps]
def vcomp  (η θ ι : oplax_nat_trans F G)
  (Γ : modification η θ) (Δ : modification θ ι) : modification η ι :=
{ app := λ a, Γ.app a ≫ Δ.app a,
  naturality' := λ a b f, by { simp [naturality_assoc, naturality] } }

/--
The identity modification.
-/
@[simps]
def id (η : oplax_nat_trans F G) : modification η η :=
{ app := λ a, 𝟙 (η.app a) }

instance (η : oplax_nat_trans F G) : inhabited (modification η η) := ⟨modification.id η⟩

section

variables {η θ : oplax_nat_trans F G} (Γ : modification η θ) {a b c : B} {a' : C}

@[reassoc]
lemma whisker_left_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
  (f ◁ (_ ◁ Γ.app c)) ≫ (f ◁ (θ.naturality g))
  = (f ◁ (η.naturality g)) ≫ (f ◁ (Γ.app b ▷ _)) :=
by { simp only [←bicategory.whisker_left_comp], rw modification.naturality }

@[reassoc]
lemma whisker_right_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
  ((_ ◁ Γ.app b) ▷ g) ≫ ((θ.naturality f) ▷ g)
  = ((η.naturality f) ▷ g) ≫ ((Γ.app a ▷ _) ▷ g) :=
by { simp only [←bicategory.whisker_right_comp], rw modification.naturality }

end

end modification

/--
A category structure on the pseudonatural transformations between oplax_functors.
-/
@[simps]
instance category (F G : oplax_functor B C) : category (oplax_nat_trans F G) :=
{ hom   := modification,
  id    := modification.id,
  comp  := modification.vcomp }

/--
Construct a modification isomorphism between pseudonatural transformation
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def modification_iso.of_components {η θ : oplax_nat_trans F G}
  (app : ∀ a, η.app a ≅ θ.app a)
  (naturality : ∀ {a b} (f : a ⟶ b),
    (_ ◁ (app b).hom) ≫ (θ.naturality f) = (η.naturality f) ≫ ((app a).hom ▷ _)) :
      η ≅ θ :=
{ hom := { app := λ a, (app a).hom },
  inv :=
  { app := λ a, (app a).inv,
    naturality' := λ a b f, by
    { have h := congr_arg (λ f, (_ ◁ (app b).inv) ≫ f ≫ ((app a).inv ▷ _)) (naturality f).symm,
      simp only [category.comp_id, inv_hom_whisker_left_assoc, category.assoc,
        hom_inv_whisker_right] at h,
      exact h } } }

/--
Left whiskering of a pseudonatural transformation and a modification.
-/
@[simps] def whisker_left
  (η : oplax_nat_trans F G) {θ ι : oplax_nat_trans G H} (Γ : modification θ ι) :
    modification (η.vcomp θ) (η.vcomp ι) :=
{ app := λ a, η.app a ◁ Γ.app a,
  naturality' := λ a b f, by
  { dsimp,
    simp only [category.assoc],
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
        associator_naturality_right_assoc, Γ.whisker_left_naturality_assoc,
        associator_inv_naturality_middle] } }

/--
Right whiskering of a pseudonatural transformation and a modification.
-/
@[simps] def whisker_right
  {η θ : oplax_nat_trans F G} (Γ : modification η θ) (ι : oplax_nat_trans G H) :
    modification (η.vcomp ι) (θ.vcomp ι) :=
{ app := λ a, Γ.app a ▷ ι.app a,
  naturality' := λ a b f, by
  { dsimp,
    simp only [category.assoc],
    rw [associator_inv_naturality_middle_assoc, Γ.whisker_right_naturality_assoc,
        associator_naturality_left_assoc, ←whisker_exchange_assoc,
        associator_inv_naturality_left] } }

/--
Associator for the vertical composition between pseudonatural transformations.
-/
@[simps] def associator
  (η : oplax_nat_trans F G) (θ : oplax_nat_trans G H) (ι : oplax_nat_trans H I) :
    (η.vcomp θ).vcomp ι ≅ η.vcomp (θ.vcomp ι) :=
modification_iso.of_components (λ a, α_ (η.app a) (θ.app a) (ι.app a))
begin
  intros a b f,
  dsimp,
  simp only [bicategory.whisker_right_comp, bicategory.whisker_left_comp, category.assoc],
  rw [←pentagon_inv_inv_hom_hom_inv_assoc, ←associator_naturality_left_assoc,
      pentagon_hom_hom_inv_hom_hom_assoc, ←associator_naturality_middle_assoc,
      ←pentagon_inv_hom_hom_hom_hom_assoc, ←associator_naturality_right_assoc,
      pentagon_hom_inv_inv_inv_hom]
end

/--
Left unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def left_unitor (η : oplax_nat_trans F G) : (oplax_nat_trans.id F).vcomp η ≅ η :=
modification_iso.of_components (λ a, λ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←left_unitor_comp, left_unitor_naturality, left_unitor_comp],
  simp
end

/--
Right unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def right_unitor  (η : oplax_nat_trans F G) : η.vcomp (oplax_nat_trans.id G) ≅ η :=
modification_iso.of_components (λ a, ρ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←right_unitor_comp, right_unitor_naturality, right_unitor_comp],
  simp
end

end oplax_nat_trans

end

section
variables (B C)

/--
A bicategory structure on the oplax_functors between bicategories. The 1-morphisms in this bicategory are
the pseudonatural transformations, and the composition of 1-morphisms is the vertical composition
of pseudonatural transformations. The 2-morphisms are the modifications.
-/
@[simps]
instance : bicategory (oplax_functor B C) :=
{ hom := oplax_nat_trans,
  id := oplax_nat_trans.id,
  hom_category := oplax_nat_trans.category,
  comp := λ F G H, oplax_nat_trans.vcomp,
  whisker_left  := λ F G H η _ _ Γ, oplax_nat_trans.whisker_left η Γ,
  whisker_right := λ F G H _ _ Γ η, oplax_nat_trans.whisker_right Γ η,
  associator := λ F G H I, oplax_nat_trans.associator,
  left_unitor   := λ F G, oplax_nat_trans.left_unitor,
  right_unitor  := λ F G, oplax_nat_trans.right_unitor,
  associator_naturality_left'   := by { intros, ext, dsimp, rw associator_naturality_left },
  associator_naturality_middle' := by { intros, ext, dsimp, rw associator_naturality_middle },
  associator_naturality_right'  := by { intros, ext, dsimp, rw associator_naturality_right },
  left_unitor_naturality'   := by { intros, ext, dsimp, rw left_unitor_naturality },
  right_unitor_naturality'  := by { intros, ext, dsimp, rw right_unitor_naturality },
  pentagon' := by { intros, ext, dsimp, rw pentagon },
  triangle' := by { intros, ext, dsimp, rw triangle } }

end

namespace pseudonat_trans

/--
A category structure on the pseudonatural transformations between oplax_functors.
-/
@[simps]
instance category (F G : pseudofunctor B C) : category (pseudonat_trans F G) :=
{ hom   := λ η θ, oplax_nat_trans.modification η.to_oplax_nat_trans θ.to_oplax_nat_trans,
  id    := λ η, oplax_nat_trans.modification.id η.to_oplax_nat_trans,
  comp  := λ η θ ι,
    oplax_nat_trans.modification.vcomp η.to_oplax_nat_trans θ.to_oplax_nat_trans ι.to_oplax_nat_trans }

/--
Construct a modification isomorphism between pseudonatural transformation
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def modification_iso.of_components {F G : pseudofunctor B C} {η θ : pseudonat_trans F G}
  (app : ∀ a, η.app a ≅ θ.app a)
  (naturality : ∀ {a b} (f : a ⟶ b),
    (_ ◁ (app b).hom) ≫ (θ.naturality f) = (η.naturality f) ≫ ((app a).hom ▷ _)) :
      η ≅ θ :=
{ hom := { app := λ a, (app a).hom },
  inv :=
  { app := λ a, (app a).inv,
    naturality' := λ a b f, by
    { have h := congr_arg (λ f, (_ ◁ (app b).inv) ≫ f ≫ ((app a).inv ▷ _)) (naturality f).symm,
      simp only [category.comp_id, inv_hom_whisker_left_assoc, category.assoc,
        hom_inv_whisker_right] at h,
      exact h } } }

section
variables {F G H I : pseudofunctor B C}
/--
Associator for the vertical composition between pseudonatural transformations.
-/
@[simps] def associator
  (η : pseudonat_trans F G) (θ : pseudonat_trans G H) (ι : pseudonat_trans H I) :
    (η.vcomp θ).vcomp ι ≅ η.vcomp (θ.vcomp ι) :=
modification_iso.of_components
  (λ a, α_ _ _ _)
begin
  intros a b f,
  dsimp,
  simp only [bicategory.whisker_right_comp, bicategory.whisker_left_comp, category.assoc],
  rw [←pentagon_inv_inv_hom_hom_inv_assoc, ←associator_naturality_left_assoc,
      pentagon_hom_hom_inv_hom_hom_assoc, ←associator_naturality_middle_assoc,
      ←pentagon_inv_hom_hom_hom_hom_assoc, ←associator_naturality_right_assoc,
      pentagon_hom_inv_inv_inv_hom]
end

/--
Left unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def left_unitor (η : pseudonat_trans F G) : (pseudonat_trans.id F).vcomp η ≅ η :=
modification_iso.of_components (λ a, λ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←left_unitor_comp, left_unitor_naturality, left_unitor_comp],
  simp
end

/--
Right unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def right_unitor  (η : pseudonat_trans F G) : η.vcomp (pseudonat_trans.id G) ≅ η :=
modification_iso.of_components (λ a, ρ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←right_unitor_comp, right_unitor_naturality, right_unitor_comp],
  simp
end

end

end pseudonat_trans


/--
A bicategory structure on the oplax_functors between bicategories. The 1-morphisms in this bicategory are
the pseudonatural transformations, and the composition of 1-morphisms is the vertical composition
of pseudonatural transformations. The 2-morphisms are the modifications.
-/
@[simps]
instance : bicategory (pseudofunctor B C) :=
{ hom := pseudonat_trans,
  id := pseudonat_trans.id,
  hom_category := pseudonat_trans.category,
  comp := λ F G H, pseudonat_trans.vcomp,
  whisker_left  := λ F G H η _ _ Γ, oplax_nat_trans.whisker_left η.to_oplax_nat_trans Γ,
  whisker_right := λ F G H _ _ Γ η, oplax_nat_trans.whisker_right Γ η.to_oplax_nat_trans,
  associator := λ F G H I η θ ι, pseudonat_trans.associator η θ ι,
  left_unitor   := λ F G η, pseudonat_trans.left_unitor η,
  right_unitor  := λ F G η, pseudonat_trans.right_unitor η,
  associator_naturality_left'   := by { intros, ext, dsimp, rw associator_naturality_left },
  associator_naturality_middle' := by { intros, ext, dsimp, rw associator_naturality_middle },
  associator_naturality_right'  := by { intros, ext, dsimp, rw associator_naturality_right },
  left_unitor_naturality'   := by { intros, ext, dsimp, rw left_unitor_naturality },
  right_unitor_naturality'  := by { intros, ext, dsimp, rw right_unitor_naturality },
  pentagon' := by { intros, ext, dsimp, rw pentagon },
  triangle' := by { intros, ext, dsimp, rw triangle } }

end category_theory
