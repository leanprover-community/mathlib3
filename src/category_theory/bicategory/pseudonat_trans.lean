/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.pseudofunctor

/-!
# Pseudonatural transformations

Just as there are natural transformations between functors, there are pseudonatural
transformations between pseudofunctors. The equality in the naturality of natural
transformations is replaced by an specified isomorphism
`F.map₁ f ≫ app b ≅ app a ≫ G.map₁ f`
in the case of pseudonatural transformations.

The pseudonatural transformation between pseudofunctors form a category. Morphisms
in this category are called modifications.

We define the vertical composition of pseudofunctors. We show that pseudofunctors between
bicategories form a bicategory. The 1-morphisms in this bicategory are the pseudonatural
transformations, and the composition of 1-morphisms is the vertical composition of
pseudonatural transformations.
-/

open category_theory

universes w₁ w₂ v₁ v₂ u₁ u₂

namespace category_theory

open bicategory

variables
{B : Type u₁} [bicategory.{w₁ v₁} B]
{C : Type u₂} [bicategory.{w₂ v₂} C]

/--
If `η` is a pseudonatural transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.map₀ a ⟶ G.map₀ a` for each object `a : B`. We also have an isomorphism
`η.naturality f : F.map₁ f ≫ app b ≅ app a ≫ G.map₁ f` for each 1-morphisms `f : a ⟶ b`.
This family of isomorphisms satisfies certain equations.
-/
structure pseudonat_trans (F G : pseudofunctor B C) :=
(app (a : B) : F.map₀ a ⟶ G.map₀ a)
(naturality {a b} (f : a ⟶ b) : F.map₁ f ≫ app b ≅ app a ≫ G.map₁ f)
(naturality_naturality' : ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
  (F.map₂ η ▹ _) ≫ (naturality g).hom = (naturality f).hom ≫ (_ ◃ G.map₂ η) . obviously)
(naturality_id' : ∀ (a),
  ((F.map₁_id a).hom ▹ _) ≫ (naturality (𝟙 a)).hom
  = (λ_ _).hom  ≫ (ρ_ _).inv ≫ (_ ◃ (G.map₁_id a).hom) . obviously)
(naturality_comp' : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
  ((F.map₁_comp f g).hom ▹ _) ≫ (naturality (f ≫ g)).hom
  = (α_ _ _ _).hom ≫ (_ ◃ (naturality g).hom)
  ≫ (α_ _ _ _).inv ≫ ((naturality f).hom ▹ G.map₁ g)
  ≫ (α_ _ _ _).hom ≫ (_ ◃ (G.map₁_comp f g).hom) . obviously)

restate_axiom pseudonat_trans.naturality_naturality'
attribute [simp, reassoc] pseudonat_trans.naturality_naturality
restate_axiom pseudonat_trans.naturality_comp'
attribute [simp, reassoc] pseudonat_trans.naturality_comp
restate_axiom pseudonat_trans.naturality_id'
attribute [simp, reassoc] pseudonat_trans.naturality_id

namespace pseudonat_trans

/--
The identity pseudonatural transformation.
-/
@[simps]
def id (F : pseudofunctor B C) : pseudonat_trans F F :=
{ app := λ a, 𝟙 (F.map₀ a),
  naturality := λ a b f, (ρ_ _) ≪≫ (λ_ _).symm,
  naturality_naturality' := λ a b f f' η, by
  { dsimp, rw [right_unitor_naturality_assoc, left_unitor_inv_naturality], simp, },
  naturality_comp' := λ a b c f g, by
  { dsimp,
    rw [right_unitor_naturality_assoc, left_unitor_inv_naturality],
    simp },
  naturality_id' := λ a, by
  { dsimp,
    rw [right_unitor_naturality_assoc, left_unitor_inv_naturality,
      unitors_equal, unitors_inv_equal] } }

instance (F : pseudofunctor B C) : inhabited (pseudonat_trans F F) := ⟨id F⟩

section
variables {F G H : pseudofunctor B C}
(φ : pseudonat_trans F G) (ψ : pseudonat_trans G H) {a b c : B} {a' : C}

@[simp, reassoc]
lemma whisker_left_naturality_naturality (f : a' ⟶ G.map₀ a) {g h : a ⟶ b} (η : g ⟶ h) :
  (f ◃ (G.map₂ η ▹ ψ.app b)) ≫ (f ◃ (ψ.naturality h).hom)
  = (f ◃ (ψ.naturality g).hom) ≫ (f ◃ (ψ.app a ◃ H.map₂ η)) :=
by { simp only [←whisker_left_comp], rw naturality_naturality }

@[simp, reassoc]
lemma whisker_right_naturality_naturality {f g : a ⟶ b} (η : f ⟶ g) (h : G.map₀ b ⟶ a') :
  ((F.map₂ η ▹ φ.app b) ▹ h) ≫ ((φ.naturality g).hom ▹ h)
  = ((φ.naturality f).hom ▹ h) ≫ ((φ.app a ◃ G.map₂ η) ▹ h) :=
by { simp only [←whisker_right_comp], rw naturality_naturality }

@[simp, reassoc]
lemma whisker_left_naturality_comp (f : a' ⟶ G.map₀ a) (g : a ⟶ b) (h : b ⟶ c) :
  (f ◃ ((G.map₁_comp g h).hom ▹ _)) ≫ (f ◃ (ψ.naturality (g ≫ h)).hom)
  = (f ◃ (α_ _ _ _).hom) ≫ (f ◃ (_ ◃ (ψ.naturality h).hom))
  ≫ (f ◃ (α_ _ _ _).inv) ≫ (f ◃ ((ψ.naturality g).hom ▹ H.map₁ h))
  ≫ (f ◃ (α_ _ _ _).hom) ≫ (f ◃ (_ ◃ (H.map₁_comp g h).hom)) :=
by { simp only [←whisker_left_comp], rw naturality_comp }

@[simp, reassoc]
lemma whisker_right_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.map₀ c ⟶ a')  :
  (((F.map₁_comp f g).hom ▹ _) ▹ h) ≫ ((φ.naturality (f ≫ g)).hom ▹ h)
  = ((α_ _ _ _).hom ▹ h) ≫ ((_ ◃ (φ.naturality g).hom) ▹ h)
  ≫ ((α_ _ _ _).inv ▹ h) ≫ (((φ.naturality f).hom ▹ G.map₁ g) ▹ h)
  ≫ ((α_ _ _ _).hom ▹ h) ≫ ((_ ◃ (G.map₁_comp f g).hom) ▹ h) :=
by { simp only [←whisker_right_comp], rw naturality_comp }

@[simp, reassoc]
lemma whisker_left_naturality_id (f : a' ⟶ G.map₀ a) :
  (f ◃ ((G.map₁_id a).hom ▹ _)) ≫ (f ◃ (ψ.naturality (𝟙 a)).hom)
  = (f ◃ (λ_ _).hom)  ≫ (f ◃ (ρ_ _).inv) ≫ (f ◃ (_ ◃ (H.map₁_id a).hom)) :=
by { simp only [←whisker_left_comp], rw naturality_id }

@[simp, reassoc]
lemma whisker_right_naturality_id (f : G.map₀ a ⟶ a') :
  (((F.map₁_id a).hom ▹ _) ▹ f) ≫ ((φ.naturality (𝟙 a)).hom ▹ f)
  = ((λ_ _).hom ▹ f)  ≫ ((ρ_ _).inv ▹ f) ≫ ((_ ◃ (G.map₁_id a).hom) ▹ f) :=
by { simp only [←whisker_right_comp], rw naturality_id }

end

/--
Vertical composition of pseudonatural transformations.
-/
@[simps]
def vcomp {F G H : pseudofunctor B C} (η : pseudonat_trans F G) (θ : pseudonat_trans G H) :
  pseudonat_trans F H :=
{ app := λ a, η.app a ≫ θ.app a,
  naturality := λ a b f,
    (α_ _ _ _).symm
    ≪≫ whisker_right_iso (η.naturality f) (θ.app b)
    ≪≫ (α_ _ _ _)
    ≪≫ whisker_left_iso (η.app a) (θ.naturality f)
    ≪≫ (α_ _ _ _).symm,
  naturality_naturality' := λ a b f g ι,
  begin
    dsimp,
    rw [associator_inv_naturality_left_assoc, whisker_right_naturality_naturality_assoc,
        associator_naturality_middle_assoc, whisker_left_naturality_naturality_assoc,
        associator_inv_naturality_right],
    simp
  end,
  naturality_comp' := λ a b c f g,
  begin
    dsimp,
    rw [associator_inv_naturality_left_assoc, whisker_right_naturality_comp_assoc,
        associator_naturality_middle_assoc, whisker_left_naturality_comp_assoc,
        associator_inv_naturality_right],
    simp only [whisker_right_comp, whisker_left_comp, category.assoc],
    rw [←pentagon_inv_hom_hom_hom_inv_assoc, ←associator_naturality_middle_assoc,
        ←pentagon_hom_hom_inv_inv_hom_assoc, associator_naturality_middle_assoc (η.app a)],
    slice_rhs 4 12
    { rw [←pentagon_inv_hom_hom_hom_hom_assoc, ←pentagon_hom_hom_inv_hom_hom,
          associator_naturality_left_assoc, ←associator_naturality_right_assoc,
          pentagon_inv_inv_hom_hom_inv_assoc, inv_hom_whisker_left_assoc, iso.hom_inv_id_assoc,
          whisker_exchange_assoc, associator_naturality_right_assoc,
          ←associator_naturality_left_assoc, ←pentagon_assoc] },
    simp only [category.assoc]
  end,
  naturality_id' := λ a,
  begin
    dsimp,
    rw [associator_inv_naturality_left_assoc, whisker_right_naturality_id_assoc,
        associator_naturality_middle_assoc, whisker_left_naturality_id_assoc,
        associator_inv_naturality_right],
    simp
  end }


end pseudonat_trans

section
variables {F G H : pseudofunctor B C}

/--
A modification between pseudonatural transformations.
-/
@[ext]
structure modification (η θ : pseudonat_trans F G) :=
(app (a : B) : η.app a ⟶ θ.app a)
(naturality' : ∀ {a b : B} (f : a ⟶ b),
  (_ ◃ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▹ _) . obviously)

restate_axiom modification.naturality'
attribute [reassoc] modification.naturality

namespace modification

/--
Vertical composition of modifications.
-/
@[simps]
def vcomp  (η θ ι : pseudonat_trans F G)
  (Γ : modification η θ) (Δ : modification θ ι) : modification η ι :=
{ app := λ a, Γ.app a ≫ Δ.app a,
  naturality' := λ a b f, by { simp [naturality_assoc, naturality] } }

/--
The identity modification.
-/
@[simps]
def id (η : pseudonat_trans F G) : modification η η :=
{ app := λ a, 𝟙 (η.app a) }

instance (η : pseudonat_trans F G) : inhabited (modification η η) := ⟨modification.id η⟩

section

variables {η θ : pseudonat_trans F G} (Γ : modification η θ) {a b c : B} {a' : C}

@[reassoc]
lemma whisker_left_naturality (f : a' ⟶ F.map₀ b) (g : b ⟶ c) :
  (f ◃ (_ ◃ Γ.app c)) ≫ (f ◃ (θ.naturality g).hom)
  = (f ◃ (η.naturality g).hom) ≫ (f ◃ (Γ.app b ▹ _)) :=
by { simp only [←whisker_left_comp], rw modification.naturality }

@[reassoc]
lemma whisker_right_naturality (f : a ⟶ b) (g : G.map₀ b ⟶ a') :
  ((_ ◃ Γ.app b) ▹ g) ≫ ((θ.naturality f).hom ▹ g)
  = ((η.naturality f).hom ▹ g) ≫ ((Γ.app a ▹ _) ▹ g) :=
by { simp only [←whisker_right_comp], rw modification.naturality }

end

end modification

variables (F G)

/--
Pseudonatural transformations between pseudofunctors form a category.
-/
@[simps]
instance : category (pseudonat_trans F G) :=
{ hom   := modification,
  id    := modification.id,
  comp  := modification.vcomp }

end

/--
Construct a modification isomorphism between pseudonatural transformation
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def modification_iso.of_components {F G : pseudofunctor B C} {η θ : pseudonat_trans F G}
  (app : ∀ a, η.app a ≅ θ.app a)
  (naturality : ∀ {a b} (f : a ⟶ b),
    (_ ◃ (app b).hom) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ ((app a).hom ▹ _)) :
      η ≅ θ :=
{ hom := { app := λ a, (app a).hom },
  inv :=
  { app := λ a, (app a).inv,
    naturality' := λ a b f,
    begin
      have h := congr_arg (λ f, (_ ◃ (app b).inv) ≫ f ≫ ((app a).inv ▹ _)) (naturality f).symm,
      simp only [category.comp_id, inv_hom_whisker_left_assoc, category.assoc,
        hom_inv_whisker_right] at h,
      exact h
    end } }

namespace pseudonat_trans

section
variables {F G H I : pseudofunctor B C}

/--
Left whiskering of a pseudonatural transformation and a modification.
-/
@[simps] def whisker_left
  (η : pseudonat_trans F G) {θ ι : pseudonat_trans G H} (Γ : modification θ ι) :
    modification (η.vcomp θ) (η.vcomp ι) :=
{ app := λ a, η.app a ◃ Γ.app a,
  naturality' := λ a b f,
  begin
    dsimp,
    simp only [category.assoc],
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
        associator_naturality_right_assoc, Γ.whisker_left_naturality_assoc,
        associator_inv_naturality_middle]
  end }

/--
Right whiskering of a pseudonatural transformation and a modification.
-/
@[simps] def whisker_right
  {η θ : pseudonat_trans F G} (Γ : modification η θ) (ι : pseudonat_trans G H) :
    modification (η.vcomp ι) (θ.vcomp ι) :=
{ app := λ a, Γ.app a ▹ ι.app a,
  naturality' := λ a b f,
  begin
    dsimp,
    simp only [category.assoc],
    rw [associator_inv_naturality_middle_assoc, Γ.whisker_right_naturality_assoc,
        associator_naturality_left_assoc, ←whisker_exchange_assoc,
        associator_inv_naturality_left]
  end }

/--
Associator for the vertical composition between pseudonatural transformations.
-/
@[simps] def associator
    (η : pseudonat_trans F G) (θ : pseudonat_trans G H) (ι : pseudonat_trans H I) :
  (η.vcomp θ).vcomp ι ≅ η.vcomp (θ.vcomp ι) :=
modification_iso.of_components (λ a, α_ (η.app a) (θ.app a) (ι.app a))
begin
  intros a b f,
  dsimp,
  simp only [whisker_right_comp, whisker_left_comp, category.assoc],
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

section
variables (B C)

/--
Pseudofunctors between bicategories form a bicategory. The 1-morphisms in this bicategory are
the pseudonatural transformations, and the composition of 1-morphisms is the vertical composition
of pseudonatural transformations.
-/
@[simps]
instance : bicategory (pseudofunctor B C) :=
{ hom := pseudonat_trans,
  id := pseudonat_trans.id,
  category_hom := pseudonat_trans.category,
  comp := λ F G H, pseudonat_trans.vcomp,
  whisker_left  := λ F G H η _ _ Γ, pseudonat_trans.whisker_left η Γ,
  whisker_right := λ F G H _ _ Γ η, pseudonat_trans.whisker_right Γ η,
  associator := λ F G H I, pseudonat_trans.associator,
  left_unitor   := λ F G, pseudonat_trans.left_unitor,
  right_unitor  := λ F G, pseudonat_trans.right_unitor,
  associator_naturality_left'   := by { intros, ext, dsimp, rw associator_naturality_left },
  associator_naturality_middle' := by { intros, ext, dsimp, rw associator_naturality_middle },
  associator_naturality_right'  := by { intros, ext, dsimp, rw associator_naturality_right },
  left_unitor_naturality'   := by { intros, ext, dsimp, rw left_unitor_naturality },
  right_unitor_naturality'  := by { intros, ext, dsimp, rw right_unitor_naturality },
  pentagon' := by { intros, ext, dsimp, rw pentagon },
  triangle' := by { intros, ext, dsimp, rw triangle } }

end

end category_theory
