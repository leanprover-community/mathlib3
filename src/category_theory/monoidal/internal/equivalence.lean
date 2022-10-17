import category_theory.monoidal.category
import category_theory.monoidal.coherence
import tactic.apply_fun

namespace category_theory

namespace monoidal_category

universes u₁ u₂ v₁ v₂

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]
variables {D : Type u₂} [category.{v₂} D]
variable (α : C ≌ D)

namespace of_equivalence

instance tensor_hom_is_iso {a a' b b' : C} (f : a ⟶ a') (g : b ⟶ b')
  [is_iso f] [is_iso g] :
  is_iso (f ⊗ g) :=
⟨⟨inv f ⊗ inv g, by rw [←tensor_comp, is_iso.hom_inv_id, is_iso.hom_inv_id, tensor_id],
  by rw [←tensor_comp, is_iso.inv_hom_id, is_iso.inv_hom_id, tensor_id]⟩⟩

lemma tensor_hom_is_iso.inv_eq {a a' b b' : C} (f : a ⟶ a') (g : b ⟶ b')
  [is_iso f] [is_iso g] :
  inv (f ⊗ g) = inv f ⊗ inv g :=
begin
  ext, rw [←tensor_comp, is_iso.hom_inv_id, is_iso.hom_inv_id, tensor_id],
end

def tensor_obj' (a b : D) : D := α.functor.obj $ α.inverse.obj a ⊗ α.inverse.obj b

lemma tensor_obj'_def (a b : D) :
  tensor_obj' α a b = α.functor.obj (α.inverse.obj a ⊗ α.inverse.obj b) := rfl

def tensor_hom' {X₁ X₂ Y₁ Y₂ : D} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
  tensor_obj' α X₁ Y₁ ⟶ tensor_obj' α X₂ Y₂ :=
α.functor.map $ α.inverse.map f ⊗ α.inverse.map g

lemma tensor_hom'_def {X₁ X₂ Y₁ Y₂ : D} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
  tensor_hom' α f g = α.functor.map (α.inverse.map f ⊗ α.inverse.map g) :=
rfl

lemma tensor_id' {a b : D} : tensor_hom' α (𝟙 a) (𝟙 b) = 𝟙 _ :=
begin
  rw [tensor_hom'_def, α.inverse.map_id, α.inverse.map_id, tensor_id, α.functor.map_id],
  refl,
end

lemma tensor_comp' {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : D}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
  tensor_hom' α (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom' α f₁ f₂ ≫ tensor_hom' α g₁ g₂ :=
begin
  rw [tensor_hom'_def, α.inverse.map_comp, α.inverse.map_comp, tensor_comp, α.functor.map_comp],
  refl,
end

def tensor_unit' : D := α.functor.obj $ 𝟙_ C
lemma tensor_unit'_def : tensor_unit' α = α.functor.obj (𝟙_ C) := rfl

@[simps] def associator' (a b c : D) :
  tensor_obj' α (tensor_obj' α a b) c ≅ tensor_obj' α a (tensor_obj' α b c) :=
{ hom := α.functor.map $ (tensor_hom (α.unit_iso.inv.app _) (𝟙 _)) ≫
    (α_ (α.inverse.obj a) (α.inverse.obj b) (α.inverse.obj c)).hom ≫
    tensor_hom (𝟙 _) (α.unit_iso.hom.app _),
  inv := α.functor.map $ tensor_hom (𝟙 _) (α.unit_iso.inv.app _) ≫
    (α_ (α.inverse.obj a) (α.inverse.obj b) (α.inverse.obj c)).inv ≫
    tensor_hom (α.unit_iso.hom.app _) (𝟙 _),
  hom_inv_id' :=
  begin
    simp only [←functor.map_comp, category.assoc],
    apply_fun α.inverse.map using α.inverse.map_injective,
    change (α.functor ⋙ α.inverse).map _ = _,
    simp only [functor.comp_map, functor.map_comp, equivalence.inv_fun_map, category.assoc,
      iso.hom_inv_id_app_assoc],
    erw [←category.assoc (tensor_hom _ _), ←category.assoc (tensor_hom _ _), ←tensor_comp,
      category.id_comp, iso.hom_inv_id_app, category.assoc, ←category.assoc (α_ _ _ _).hom,
      tensor_id, category.comp_id, ←category.assoc (α_ _ _ _).hom, iso.hom_inv_id,
      category.id_comp, ←category.assoc (tensor_hom _ _), ←tensor_comp, iso.inv_hom_id_app,
      category.comp_id, tensor_id, category.id_comp, iso.inv_hom_id_app, α.inverse.map_id],
    refl,
  end,
  inv_hom_id' := begin
    simp only [←functor.map_comp, category.assoc],
    apply_fun α.inverse.map using α.inverse.map_injective,
    change (α.functor ⋙ α.inverse).map _ = _,
    simp only [functor.comp_map, functor.map_comp, equivalence.inv_fun_map, category.assoc,
      iso.hom_inv_id_app_assoc, α.inverse.map_id],
    erw [←category.assoc (tensor_hom _ _), ←category.assoc (tensor_hom _ _), ←tensor_comp,
      category.id_comp, iso.hom_inv_id_app, tensor_id, category.id_comp,
      category.assoc, ←category.assoc (α_ _ _ _).inv,  iso.inv_hom_id, category.id_comp,
      ←category.assoc (tensor_hom _ _), ←tensor_comp, iso.inv_hom_id_app,
      category.comp_id, tensor_id, category.id_comp, iso.inv_hom_id_app, α.inverse.map_id],
    refl,
  end }

lemma associator'_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : D}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  tensor_hom' α (tensor_hom' α f₁ f₂) f₃ ≫ (associator' α Y₁ Y₂ Y₃).hom =
  (associator' α X₁ X₂ X₃).hom ≫ tensor_hom' α f₁ (tensor_hom' α f₂ f₃) :=
begin
  simp only [tensor_hom', associator', ←α.functor.map_comp],
  apply_fun α.inverse.map using α.inverse.map_injective,
  simp only [equivalence.inv_fun_map, functor.map_comp, category.assoc, iso.hom_inv_id_app_assoc,
    nat_iso.cancel_nat_iso_inv_left],
  simp only [←category.assoc],
  congr' 1,
  simp only [category.assoc],
  rw [←category.assoc (tensor_hom _ _), ←tensor_comp, ←category.assoc (tensor_hom _ _),
    ←tensor_comp, category.id_comp, ←category.assoc (α.unit_iso.hom.app _), iso.hom_inv_id_app,
    ←category.assoc (tensor_hom _ _), category.id_comp, category.comp_id],
  simp only [category.assoc],
  erw [iso.hom_inv_id_app, category.comp_id],
  haveI i1 : is_iso (𝟙 (α.inverse.obj Y₁) ⊗ α.unit_iso.hom.app (α.inverse.obj Y₂ ⊗ α.inverse.obj Y₃)),
  { apply of_equivalence.tensor_hom_is_iso, },
  have eq1 : inv (𝟙 (α.inverse.obj Y₁) ⊗ α.unit_iso.hom.app (α.inverse.obj Y₂ ⊗ α.inverse.obj Y₃))
    = 𝟙 _ ⊗ α.unit_iso.inv.app (α.inverse.obj Y₂ ⊗ α.inverse.obj Y₃),
  { rw tensor_hom_is_iso.inv_eq,
    congr'; ext, rw category.id_comp, rw iso.hom_inv_id_app, },
  symmetry,
  simp only [←category.assoc],
  erw [←category_theory.is_iso.comp_inv_eq, eq1, category.assoc, ←tensor_comp,
    category.comp_id, category.assoc, category.assoc, iso.hom_inv_id_app, category.comp_id,
    ←associator_naturality, ←category.assoc, ←tensor_comp, category.id_comp],
end

@[simps] def left_unitor' (a : D) :
  tensor_obj' α (tensor_unit' α) a ≅ a :=
{ hom := α.functor.map (tensor_hom (α.unit_iso.inv.app _) (𝟙 _)) ≫
    α.functor.map (left_unitor (α.inverse.obj a)).hom ≫ (α.counit_iso.app a).hom,
  inv := α.counit_iso.inv.app _ ≫ α.functor.map (left_unitor (α.inverse.obj a)).inv ≫
    α.functor.map (tensor_hom (α.unit_iso.app _).hom (𝟙 _)),
  hom_inv_id' :=
  begin
    simp only [iso.app_hom, category.assoc, iso.hom_inv_id_app_assoc, ←α.functor.map_comp],
    erw [←category.assoc (λ_ (α.inverse.obj a)).hom, iso.hom_inv_id, category.id_comp, ←tensor_comp,
      category.id_comp, iso.inv_hom_id_app, tensor_id, α.functor.map_id],
    refl,
  end,
  inv_hom_id' :=
  begin
    simp only [iso.app_hom, category.assoc],
    erw [←category.assoc _ _ (α.counit_iso.hom.app a), ←category.assoc _ _ (α.counit_iso.hom.app a),
      ←category.assoc _ _ (α.counit_iso.hom.app a), ←category.assoc _ _ (α.counit_iso.hom.app a),
      ←α.functor.map_comp, ←α.functor.map_comp,  ←α.functor.map_comp,
      ←category.assoc _ _ (λ_ (α.inverse.obj a)).hom, ←tensor_comp, category.id_comp,
      iso.hom_inv_id_app, tensor_id, category.id_comp, iso.inv_hom_id, α.functor.map_id,
      category.comp_id, iso.inv_hom_id_app],
    refl,
  end }

lemma left_unitor'_naturality {X Y : D} (f : X ⟶ Y) :
  tensor_hom' α (𝟙 (tensor_unit' α)) f ≫ (left_unitor' α Y).hom = (left_unitor' α X).hom ≫ f :=
begin
  simp only [tensor_hom', functor.map_id, left_unitor'_hom, iso.app_hom, category.assoc],
  erw [←category.assoc _ _ (α.counit_iso.hom.app Y), ←category.assoc _ _ (α.counit_iso.hom.app Y),
    ←α.functor.map_comp, ←α.functor.map_comp, ←category.assoc, ←tensor_comp, category.comp_id,
    category.id_comp, ←category.assoc, ←α.functor.map_comp],
  apply_fun α.inverse.map using α.inverse.map_injective,
  simp only [functor.map_comp, category.assoc, equivalence.inv_fun_map,
    equivalence.unit_inverse_comp, category.comp_id, iso.hom_inv_id_app_assoc,
    nat_iso.cancel_nat_iso_inv_left],
  erw [←category.assoc _ _ (α.inverse.map f), α.unit_inverse_comp, category.id_comp,
    ←left_unitor_naturality (α.inverse.map f), ←category.assoc, ←tensor_comp, category.id_comp,
    category.comp_id],
end

end of_equivalence

def of_equivalence : monoidal_category D :=
{ tensor_obj := of_equivalence.tensor_obj' α,
  tensor_hom := λ _ _ _ _, of_equivalence.tensor_hom' α,
  tensor_id' := λ _ _, of_equivalence.tensor_id' α,
  tensor_comp' := λ X₁ X₂ Y₁ Y₂ Z₁ Z₂, of_equivalence.tensor_comp' α,
  tensor_unit := of_equivalence.tensor_unit' α,
  associator := of_equivalence.associator' α,
  associator_naturality' := λ _ _ _ _ _ _, of_equivalence.associator'_naturality α,
  left_unitor := of_equivalence.left_unitor' α,
  left_unitor_naturality' := λ _ _, of_equivalence.left_unitor'_naturality α,
  right_unitor := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry }

end monoidal_category

end category_theory
