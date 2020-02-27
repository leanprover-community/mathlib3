import category_theory.types
import category_theory.core
import category_theory.concrete_category
import category_theory.elements
import category_theory.functorial

universes w₁ v₁ v₂ u₁ u₂

open category_theory

set_option pp.universes true

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]

section
include 𝒞 𝒟

class iso_functorial (f : C → D) :=
(map : Π {X Y : C}, (X ≅ Y) → (f X ≅ f Y))
(map_id'   : ∀ (X : C), map (iso.refl X) = iso.refl (f X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z), map (f ≪≫ g) = (map f) ≪≫ (map g) . obviously)

restate_axiom iso_functorial.map_id'
attribute [simp] iso_functorial.map_id
restate_axiom iso_functorial.map_comp'
attribute [simp] iso_functorial.map_comp

@[simp] lemma iso_functorial.map_id_core (f : C → D) [iso_functorial.{v₁ v₂} f] (X : core C) :
  iso_functorial.map.{v₁} f (𝟙 X) = iso.refl _ :=
iso_functorial.map_id.{v₁ v₂} f (of_core X)
@[simp] lemma iso_functorial.map_comp_core (f : C → D) [iso_functorial.{v₁ v₂} f]
  (X Y Z : core C) (g : X ⟶ Y) (h : Y ⟶ Z) :
  iso_functorial.map.{v₁} f (g ≫ h) = iso_functorial.map.{v₁} f g ≪≫ iso_functorial.map.{v₁} f h :=
iso_functorial.map_comp.{v₁ v₂} f g h

def as_core_functor (f : C → D) [I : iso_functorial.{v₁ v₂} f] : core C ⥤ D :=
{ obj := λ X, f (of_core X),
  map := λ X Y g, iso.hom (iso_functorial.map.{v₁} f g) }

@[simp] lemma as_core_functor_obj  (f : C → D) [iso_functorial.{v₁ v₂} f] (X : core C) :
  (as_core_functor f).obj X = f (of_core X) := rfl

instance functor_obj_iso_functorial (F : C ⥤ D) : iso_functorial.{v₁ v₂} F.obj :=
{ map := λ X Y f, F.map_iso f }

-- TODO specialise some universe variables?
instance iso_functorial_elements_1 (F : C ⥤ Type w₁) (g : C → D) [iso_functorial.{v₁ v₂} g] :
  iso_functorial.{v₁ v₂} (λ (X : F.elements), g (X.1)) :=
{ map := λ X Y f,  iso_functorial.map.{v₁ v₂} g (of_element_iso f) }

omit 𝒟
instance (p : C → Prop) : subsingleton (functorial.{v₁ 0} (plift ∘ p)) :=
⟨by { rintros ⟨a⟩ ⟨b⟩, congr, ext, apply proof_irrel_heq, apply proof_irrel_heq, }⟩

end
