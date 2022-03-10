import category_theory.bicategory.coherence

universes w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace category_theory
open category bicategory free_bicategory
open_locale bicategory

variables {B : Type u} [bicategory.{w v} B]
variables {a b c d e : B} {f : a ⟶ b}

lemma left_unitor_free_lift :
  (free_bicategory.lift (prefunctor.id B)).map₂ (λ_ (of.map f)).hom = (λ_ f).hom :=
rfl

lemma right_unitor_free_lift :
  (free_bicategory.lift (prefunctor.id B)).map₂ (ρ_ (of.map f)).hom = (ρ_ f).hom :=
rfl



def associator_free_lift (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
--  (of.map f ≫ of.map g) ≫ of.map h ⟶ of.map f ≫ of.map g ≫ of.map h :=
  (f ≫ g) ≫ h ⟶ f ≫ g ≫ h :=
  by apply (free_bicategory.lift (prefunctor.id B)).map₂ (α_ (of.map f) (of.map g) (of.map h)).hom

def associator_inv_free_lift (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
--  (of.map f ≫ of.map g) ≫ of.map h ⟶ of.map f ≫ of.map g ≫ of.map h :=
  f ≫ g ≫ h ⟶ (f ≫ g) ≫ h :=
  by apply (free_bicategory.lift (prefunctor.id B)).map₂ (α_ (of.map f) (of.map g) (of.map h)).inv


lemma associator_free_lift_def (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (associator_free_lift f g h) =
    (α_ f g h).hom :=
rfl

lemma associator_inv_free_lift_def (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (associator_inv_free_lift f g h) =
    (α_ f g h).inv :=
rfl

lemma free_bicategory.unitors_equal (a : free_bicategory B) :
  (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom :=
subsingleton.elim _ _

example : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom :=
by apply congr_arg
  (λ η, (free_bicategory.lift (prefunctor.id B)).map₂ η)
  (free_bicategory.unitors_equal (of.obj a))

lemma free_bicategory.pentagon {a b c d e : free_bicategory B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (((α_ f g h).inv ▷ i) ≫ (α_ (_ ≫ _) _ _).hom ≫ (α_ _ _ (_ ≫ _)).hom) =
  ((α_ _ (_ ≫ _) _).hom ≫ (_ ◁ (α_ _ _ _).hom)) :=
subsingleton.elim _ _

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  ((α_ f g h).inv ▷ i) ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom =
    (α_ f (g ≫ h) i).hom ≫ (f ◁ (α_ g h i).hom) :=
by apply congr_arg
  (λ η, (free_bicategory.lift (prefunctor.id B)).map₂ η)
  (free_bicategory.pentagon (of.map f) (of.map g) (of.map h) (of.map i))


end category_theory
