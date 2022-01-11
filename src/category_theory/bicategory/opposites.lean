import category_theory.bicategory.functor

universes w₁ w₂ v₁ v₂ u₁ u₂

open category_theory.bicategory opposite

namespace category_theory

section

variables (B : Type u₁) [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]

variables {B}
def quiver_hom_opposite (a b : Bᵒᵖ) : quiver.{w₁+1} (a ⟶ b) :=
{ hom := λ f g : a ⟶ b, f.unop ⟶ g.unop }

end

section
variables
{B : Type u₁} [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
{C : Type u₂} [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)]
(F : prepseudofunctor B C)

@[simps]
protected def prepseudofunctor.op :
@prepseudofunctor Bᵒᵖ _ (category_theory.quiver_hom_opposite) Cᵒᵖ _ (category_theory.quiver_hom_opposite) :=
{ obj := λ a, op (F.obj (unop a)),
  map := λ a b f, (F.map f.unop).op,
  map₂ := λ a b f g η, F.map₂ η }

end

section bicategory

variables {B : Type u₁} [bicategory.{w₁ v₁} B]

@[simps]
instance bicategory.opposite : bicategory.{w₁ v₁} Bᵒᵖ :=
{ hom := λ a b, unop b ⟶ unop a,
  comp := λ a b c f g, g ≫ f,
  id   := λ a, 𝟙 (a.unop),
  hom_category := λ a b, bicategory.hom_category (unop b) (unop a),
  whisker_left :=  λ a b c f g h η, bicategory.whisker_right η f,
  whisker_right := λ _ _ _ _ _ η h, bicategory.whisker_left h η,
  associator := λ _ _ _ _ f g h, (bicategory.associator h g f).symm,
  associator_naturality_left' := by { intros, apply associator_inv_naturality_right },
  associator_naturality_middle' := by { intros, apply associator_inv_naturality_middle },
  associator_naturality_right' := by { intros, apply associator_inv_naturality_left },
  left_unitor := λ _ _ f, right_unitor f,
  left_unitor_naturality' := by { intros, apply right_unitor_naturality },
  right_unitor := λ _ _ f, left_unitor f,
  right_unitor_naturality' := by { intros, apply left_unitor_naturality },
  pentagon' := by { intros, apply pentagon_inv },
  triangle' := by { intros, dsimp, apply triangle_assoc_comp_right } }

instance : quiver.{v₁+1} Bᵒᵖ := ⟨bicategory.to_category_struct.to_quiver.hom⟩

end bicategory

section oplax_functor
variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
(F : oplax_functor B C)

@[simps]
protected def oplax_functor.op : oplax_functor Bᵒᵖ Cᵒᵖ :=
{ obj := λ a, op (F.obj (unop a)),
  map := λ a b f, F.map f,
  map₂ := λ a b f g η, F.map₂ η,
  map_id := λ a,  F.map_id (unop a),
  map_comp := λ a b c f g, F.map_comp g f,
  map_comp_naturality_left' := by
  { intros, erw F.map_comp_naturality_right, refl },
  map_comp_naturality_right' := by
  { intros, erw F.map_comp_naturality_left, refl },
  map₂_id' := by { intros, apply F.map₂_id },
  map₂_comp' := by { intros, apply F.map₂_comp },
  map₂_associator' := by { intros, dsimp, apply F.map₂_associator_inv },
  map₂_left_unitor' := by { intros, apply F.map₂_right_unitor },
  map₂_right_unitor' := by { intros, apply F.map₂_left_unitor } }

end oplax_functor

section pseudofunctor

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
(F : pseudofunctor B C)

@[simps]
protected def pseudofunctor.op : pseudofunctor Bᵒᵖ Cᵒᵖ :=
{ map_id_iso := λ a, F.map_id_iso (unop a),
  map_comp_iso := λ a b c f g, F.map_comp_iso g f,
  .. oplax_functor.op (F.to_oplax_functor) }

end pseudofunctor

end category_theory
