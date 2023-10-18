/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.coherence

/-!
# A `coherence` tactic for bicategories, and `⊗≫` (composition up to associators)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide a `coherence` tactic,
which proves that any two 2-morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `bicategorical_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

This file mainly deals with the type class setup for the coherence tactic. The actual front end
tactic is given in `category_theory/monooidal/coherence.lean` at the same time as the coherence
tactic for monoidal categories.
-/

noncomputable theory

universes w v u

open category_theory
open category_theory.free_bicategory
open_locale bicategory

variables {B : Type u} [bicategory.{w v} B] {a b c d e : B}

namespace category_theory.bicategory

/-- A typeclass carrying a choice of lift of a 1-morphism from `B` to `free_bicategory B`. -/
class lift_hom {a b : B} (f : a ⟶ b) :=
(lift : of.obj a ⟶ of.obj b)

instance lift_hom_id : lift_hom (𝟙 a) := { lift := 𝟙 (of.obj a), }
instance lift_hom_comp (f : a ⟶ b) (g : b ⟶ c) [lift_hom f] [lift_hom g] : lift_hom (f ≫ g) :=
{ lift := lift_hom.lift f ≫ lift_hom.lift g, }
@[priority 100]
instance lift_hom_of (f : a ⟶ b) : lift_hom f := { lift := of.map f, }

/-- A typeclass carrying a choice of lift of a 2-morphism from `B` to `free_bicategory B`. -/
class lift_hom₂ {f g : a ⟶ b} [lift_hom f] [lift_hom g] (η : f ⟶ g) :=
(lift : lift_hom.lift f ⟶ lift_hom.lift g)

instance lift_hom₂_id (f : a ⟶ b) [lift_hom f] : lift_hom₂ (𝟙 f) :=
{ lift := 𝟙 _, }
instance lift_hom₂_left_unitor_hom (f : a ⟶ b) [lift_hom f] : lift_hom₂ (λ_ f).hom :=
{ lift := (λ_ (lift_hom.lift f)).hom, }
instance lift_hom₂_left_unitor_inv (f : a ⟶ b) [lift_hom f] : lift_hom₂ (λ_ f).inv :=
{ lift := (λ_ (lift_hom.lift f)).inv, }
instance lift_hom₂_right_unitor_hom (f : a ⟶ b) [lift_hom f] : lift_hom₂ (ρ_ f).hom :=
{ lift := (ρ_ (lift_hom.lift f)).hom, }
instance lift_hom₂_right_unitor_inv (f : a ⟶ b) [lift_hom f] : lift_hom₂ (ρ_ f).inv :=
{ lift := (ρ_ (lift_hom.lift f)).inv, }
instance lift_hom₂_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] :
  lift_hom₂ (α_ f g h).hom :=
{ lift := (α_ (lift_hom.lift f) (lift_hom.lift g) (lift_hom.lift h)).hom, }
instance lift_hom₂_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] :
  lift_hom₂ (α_ f g h).inv :=
{ lift := (α_ (lift_hom.lift f) (lift_hom.lift g) (lift_hom.lift h)).inv, }
instance lift_hom₂_comp {f g h : a ⟶ b} [lift_hom f] [lift_hom g] [lift_hom h]
  (η : f ⟶ g) (θ : g ⟶ h) [lift_hom₂ η] [lift_hom₂ θ] : lift_hom₂ (η ≫ θ) :=
{ lift := lift_hom₂.lift η ≫ lift_hom₂.lift θ }
instance lift_hom₂_whisker_left (f : a ⟶ b) [lift_hom f] {g h : b ⟶ c} (η : g ⟶ h)
  [lift_hom g] [lift_hom h] [lift_hom₂ η] : lift_hom₂ (f ◁ η) :=
{ lift := lift_hom.lift f ◁ lift_hom₂.lift η }
instance lift_hom₂_whisker_right {f g : a ⟶ b} (η : f ⟶ g) [lift_hom f] [lift_hom g] [lift_hom₂ η]
  {h : b ⟶ c} [lift_hom h] : lift_hom₂ (η ▷ h) :=
{ lift := lift_hom₂.lift η ▷ lift_hom.lift h }

/--
A typeclass carrying a choice of bicategorical structural isomorphism between two objects.
Used by the `⊗≫` bicategorical composition operator, and the `coherence` tactic.
-/
class bicategorical_coherence (f g : a ⟶ b) [lift_hom f] [lift_hom g] :=
(hom [] : f ⟶ g)
[is_iso : is_iso hom . tactic.apply_instance]

attribute [instance] bicategorical_coherence.is_iso

namespace bicategorical_coherence

@[simps]
instance refl (f : a ⟶ b) [lift_hom f] : bicategorical_coherence f f := ⟨𝟙 _⟩

@[simps]
instance whisker_left
  (f : a ⟶ b) (g h : b ⟶ c) [lift_hom f][lift_hom g] [lift_hom h] [bicategorical_coherence g h] :
  bicategorical_coherence (f ≫ g) (f ≫ h) :=
⟨f ◁ bicategorical_coherence.hom g h⟩

@[simps]
instance whisker_right
  (f g : a ⟶ b) (h : b ⟶ c) [lift_hom f] [lift_hom g] [lift_hom h] [bicategorical_coherence f g] :
  bicategorical_coherence (f ≫ h) (g ≫ h) :=
⟨bicategorical_coherence.hom f g ▷ h⟩

@[simps]
instance tensor_right (f : a ⟶ b) (g : b ⟶ b) [lift_hom f] [lift_hom g]
  [bicategorical_coherence (𝟙 b) g] :
  bicategorical_coherence f (f ≫ g) :=
⟨(ρ_ f).inv ≫ (f ◁ bicategorical_coherence.hom (𝟙 b) g)⟩

@[simps]
instance tensor_right' (f : a ⟶ b) (g : b ⟶ b) [lift_hom f] [lift_hom g]
  [bicategorical_coherence g (𝟙 b)] :
  bicategorical_coherence (f ≫ g) f :=
⟨(f ◁ bicategorical_coherence.hom g (𝟙 b)) ≫ (ρ_ f).hom⟩

@[simps]
instance left (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence (𝟙 a ≫ f) g :=
⟨(λ_ f).hom ≫ bicategorical_coherence.hom f g⟩

@[simps]
instance left' (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence f (𝟙 a ≫ g) :=
⟨bicategorical_coherence.hom f g ≫ (λ_ g).inv⟩

@[simps]
instance right (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence (f ≫ 𝟙 b) g :=
⟨(ρ_ f).hom ≫ bicategorical_coherence.hom f g⟩

@[simps]
instance right' (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence f (g ≫ 𝟙 b) :=
⟨bicategorical_coherence.hom f g ≫ (ρ_ g).inv⟩

@[simps]
instance assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] [lift_hom i] [bicategorical_coherence (f ≫ (g ≫ h)) i] :
  bicategorical_coherence ((f ≫ g) ≫ h) i :=
⟨(α_ f g h).hom ≫ bicategorical_coherence.hom (f ≫ (g ≫ h)) i⟩

@[simps]
instance assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] [lift_hom i] [bicategorical_coherence i (f ≫ (g ≫ h))] :
  bicategorical_coherence i ((f ≫ g) ≫ h) :=
⟨bicategorical_coherence.hom i (f ≫ (g ≫ h)) ≫ (α_ f g h).inv⟩

end bicategorical_coherence

/-- Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators. -/
def bicategorical_iso (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  f ≅ g :=
as_iso (bicategorical_coherence.hom f g)

/-- Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategorical_comp {f g h i : a ⟶ b} [lift_hom g] [lift_hom h]
  [bicategorical_coherence g h] (η : f ⟶ g) (θ : h ⟶ i) : f ⟶ i :=
η ≫ bicategorical_coherence.hom g h ≫ θ

localized "infixr (name := bicategorical_comp) ` ⊗≫ `:80 :=
  category_theory.bicategory.bicategorical_comp" in bicategory -- type as \ot \gg

/-- Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategorical_iso_comp {f g h i : a ⟶ b} [lift_hom g] [lift_hom h]
  [bicategorical_coherence g h] (η : f ≅ g) (θ : h ≅ i) : f ≅ i :=
η ≪≫ as_iso (bicategorical_coherence.hom g h) ≪≫ θ

localized "infixr (name := bicategorical_iso_comp) ` ≪⊗≫ `:80 :=
  category_theory.bicategory.bicategorical_iso_comp" in bicategory -- type as \ot \gg

example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {h' : a ⟶ d}
  (η : f' ⟶ f ≫ (g ≫ h)) (θ : (f ≫ g) ≫ h ⟶ h') : f' ⟶ h' := η ⊗≫ θ

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `η ⊗≫ 𝟙 _`
example {f' : a ⟶ d } {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} (η : f' ⟶ (f ≫ g) ≫ h) :
  f' ⟶ f ≫ (g ≫ h) := η ⊗≫ 𝟙 _

@[simp] lemma bicategorical_comp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
  η ⊗≫ θ = η ≫ θ :=
by { dsimp [bicategorical_comp], simp, }

end category_theory.bicategory

open category_theory.bicategory

namespace tactic

setup_tactic_parser

/-- Coherence tactic for bicategories. -/
meta def bicategorical_coherence : tactic unit :=
focus1 $
do
  o ← get_options, set_options $ o.set_nat `class.instance_max_depth 128,
  try `[dsimp],
  `(%%lhs = %%rhs) ← target,
  to_expr  ``((free_bicategory.lift (prefunctor.id _)).map₂ (lift_hom₂.lift %%lhs) =
    (free_bicategory.lift (prefunctor.id _)).map₂ (lift_hom₂.lift %%rhs))
    >>= tactic.change,
  congr

namespace bicategory

/-- Simp lemmas for rewriting a 2-morphism into a normal form. -/
meta def whisker_simps : tactic unit :=
`[simp only [
    category_theory.category.assoc,
    category_theory.bicategory.comp_whisker_left,
    category_theory.bicategory.id_whisker_left,
    category_theory.bicategory.whisker_right_comp,
    category_theory.bicategory.whisker_right_id,
    category_theory.bicategory.whisker_left_comp,
    category_theory.bicategory.whisker_left_id,
    category_theory.bicategory.comp_whisker_right,
    category_theory.bicategory.id_whisker_right,
    category_theory.bicategory.whisker_assoc]]

namespace coherence

/--
Auxiliary simp lemma for the `coherence` tactic:
this move brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_lift_hom₂]` only left associates
-- bicategorical structural morphisms.
@[nolint unused_arguments]
lemma assoc_lift_hom₂ {f g h i : a ⟶ b} [lift_hom f] [lift_hom g] [lift_hom h]
  (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i) [lift_hom₂ η] [lift_hom₂ θ] :
  η ≫ (θ ≫ ι) = (η ≫ θ) ≫ ι :=
(category.assoc _ _ _).symm

end coherence

end bicategory

end tactic
