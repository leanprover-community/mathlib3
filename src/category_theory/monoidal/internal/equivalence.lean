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

@[simps] def right_unitor' (a : D) :
  tensor_obj' α a (tensor_unit' α) ≅ a :=
{ hom := α.functor.map (𝟙 _ ⊗ α.unit_iso.inv.app _) ≫
    α.functor.map (right_unitor (α.inverse.obj a)).hom ≫
    α.counit.app _,
  inv := α.counit_iso.inv.app _ ≫ α.functor.map (right_unitor (α.inverse.obj a)).inv ≫
    α.functor.map (𝟙 _ ⊗ α.unit.app _),
  hom_inv_id' :=
  begin
    erw [←α.functor.map_comp, ←category.assoc, ←category.assoc, ←α.functor.map_comp, category.assoc,
      category.assoc, ←category.assoc (α.counit.app _), iso.hom_inv_id_app, category.id_comp,
      ←α.functor.map_comp, category.assoc, ←category.assoc (ρ_ (α.inverse.obj a)).hom,
      iso.hom_inv_id, category.id_comp, ←tensor_comp, category.id_comp, iso.inv_hom_id_app,
      tensor_id, α.functor.map_id],
    refl,
  end,
  inv_hom_id' :=
  begin
    erw [←α.functor.map_comp, ←category.assoc _ _ (α.counit.app a), ←α.functor.map_comp,
      ←category.assoc _ _ (α.counit.app a), category.assoc (α.counit_iso.inv.app a),
      ←α.functor.map_comp, category.assoc (ρ_ (α.inverse.obj a)).inv,
      ←category.assoc _ _ (ρ_ (α.inverse.obj a)).hom, ←tensor_comp, category.id_comp,
      iso.hom_inv_id_app, tensor_id, category.id_comp, iso.inv_hom_id, α.functor.map_id,
      category.comp_id, iso.inv_hom_id_app],
    refl,
  end }

lemma right_unitor'_naturality {X Y : D} (f : X ⟶ Y) :
  tensor_hom' α f (𝟙 (tensor_unit' α)) ≫ (right_unitor' α Y).hom = (right_unitor' α X).hom ≫ f :=
begin
  simp only [tensor_hom', functor.map_id, right_unitor'_hom, category.assoc],
  rw [←category.assoc _ _ (α.counit.app Y), ←α.functor.map_comp,
    ←category.assoc _ _ (α.counit.app Y), ←α.functor.map_comp,
    ←category.assoc (tensor_hom _ _), ←tensor_comp, category.id_comp, category.comp_id,
    ←category.assoc, ←α.functor.map_comp],
  apply_fun α.inverse.map using α.inverse.map_injective,
  simp only [functor.map_comp, category.assoc, equivalence.inv_fun_map,
    equivalence.unit_inverse_comp, category.comp_id, iso.hom_inv_id_app_assoc,
    nat_iso.cancel_nat_iso_inv_left],
  erw [←category.assoc _ _ (α.inverse.map f), equivalence.unit_inverse_comp, category.id_comp,
    ←right_unitor_naturality, ←category.assoc, ←tensor_comp, category.id_comp, category.comp_id],
  refl,
end

lemma pentagon'_aux01 (W X Y Z : D) :
  (((α_ (α.inverse.obj (tensor_obj' α W X)) (α.inverse.obj Y) (α.inverse.obj Z)).hom ≫
        (𝟙 (α.inverse.obj (tensor_obj' α W X)) ⊗
           α.unit_iso.hom.app (α.inverse.obj Y ⊗ α.inverse.obj Z))) ≫
     (α.unit_iso.inv.app (α.inverse.obj W ⊗ α.inverse.obj X) ⊗
        𝟙 (α.inverse.obj (tensor_obj' α Y Z)))) ≫
  (α_ (α.inverse.obj W) (α.inverse.obj X) (α.inverse.obj (tensor_obj' α Y Z))).hom =
  (tensor_hom (tensor_hom (α.unit_iso.inv.app _) (𝟙 _)) (𝟙 _)) ≫
    ((α_ _ _ _).hom ≫ (α_ _ _ _).hom)
    ≫ (tensor_hom (𝟙 _) (tensor_hom (𝟙 _) (α.unit.app _)))  :=
begin
  simp only [category.assoc, associator_conjugation, tensor_id, iso.inv_hom_id_assoc,
    iso.cancel_iso_hom_left],
  simp only [←category.assoc],
  symmetry,
  erw ←category_theory.is_iso.comp_inv_eq,
  simp only [category.assoc, is_iso.iso.inv_hom],
  erw [←associator_conjugation, ←tensor_comp, ←tensor_comp, category.id_comp, category.id_comp,
    category.comp_id, tensor_id, category.comp_id],
end

lemma pentagon'_aux02 (W X Y Z : D) :
  𝟙 (α.inverse.obj W) ⊗
  α.unit.app (α.inverse.obj X ⊗ (𝟭 C).obj (α.inverse.obj Y ⊗ α.inverse.obj Z)) ≫
    (α.functor ⋙ α.inverse).map (𝟙 (α.inverse.obj X) ⊗
      α.unit.app (α.inverse.obj Y ⊗ α.inverse.obj Z)) =
  𝟙 (α.inverse.obj W) ⊗
  (𝟙 (α.inverse.obj X) ⊗ α.unit.app (α.inverse.obj Y ⊗ α.inverse.obj Z)) ≫
    α.unit_iso.hom.app (α.inverse.obj X ⊗ α.inverse.obj (tensor_obj' α Y Z)) :=
begin
  congr' 1,
  simp only [functor.comp_map, equivalence.inv_fun_map, iso.hom_inv_id_app_assoc],
  congr' 1,
end

lemma pentagon'_aux0 (W X Y Z : D) :
  ((α.unit_iso.inv.app (α.inverse.obj (tensor_obj' α W X) ⊗ α.inverse.obj Y) ⊗
      𝟙 (α.inverse.obj Z)) ≫
    (α_ (α.inverse.obj (tensor_obj' α W X)) (α.inverse.obj Y) (α.inverse.obj Z)).hom ≫
      (𝟙 (α.inverse.obj (tensor_obj' α W X)) ⊗
         α.unit_iso.hom.app (α.inverse.obj Y ⊗ α.inverse.obj Z))) ≫
    (α.unit_iso.inv.app (α.inverse.obj W ⊗ α.inverse.obj X) ⊗
      𝟙 (α.inverse.obj (tensor_obj' α Y Z))) ≫
    (α_ (α.inverse.obj W) (α.inverse.obj X) (α.inverse.obj (tensor_obj' α Y Z))).hom ≫
      (𝟙 (α.inverse.obj W) ⊗ α.unit_iso.hom.app _) =
  ((α.unit_iso.inv.app _ ≫ (α.unit_iso.inv.app _ ⊗ 𝟙 (α.inverse.obj Y))) ⊗ (𝟙 _)) ≫
    ((α_ (α.inverse.obj W ⊗ α.inverse.obj X) (α.inverse.obj Y) (α.inverse.obj Z)).hom ≫
      (α_ (α.inverse.obj W) (α.inverse.obj X) (α.inverse.obj Y ⊗ α.inverse.obj Z)).hom) ≫
  ((𝟙 (α.inverse.obj W)) ⊗ (α.unit.app _ ≫
    ((α.functor ⋙ α.inverse).map (𝟙 (α.inverse.obj X) ⊗ α.unit.app _)))) :=
begin
  simp only [category.assoc],
  rw [←category.assoc (α_ _ _ _).hom, ←category.assoc ((α_ _ _ _).hom ≫ _),
    ←category.assoc (((α_ _ _ _).hom ≫ _) ≫ _)],
  rw [pentagon'_aux01],
  simp only [category.assoc, ←tensor_comp, category.id_comp],
  rw [pentagon'_aux02],
  simp only [←category.assoc],
  congr' 3,
  simp only [associator_conjugation, tensor_id, comp_tensor_id],
  congr' 1,
end

lemma pentagon'_aux10 (W X Y Z : D) :
  ((α_ (α.inverse.obj W) (α.inverse.obj (tensor_obj' α X Y)) (α.inverse.obj Z)).hom ≫
     (𝟙 (α.inverse.obj W) ⊗ α.unit_iso.hom.app _)) ≫
  (α.inverse.map (𝟙 W) ⊗
     α.unit_inv.app (α.inverse.obj (tensor_obj' α X Y) ⊗ α.inverse.obj Z) ≫
       (α.unit_iso.inv.app (α.inverse.obj X ⊗ α.inverse.obj Y) ⊗ 𝟙 (α.inverse.obj Z)) ≫
         (α_ (α.inverse.obj X) (α.inverse.obj Y) (α.inverse.obj Z)).hom ≫
           (𝟙 (α.inverse.obj X) ⊗ α.unit_iso.hom.app (α.inverse.obj Y ⊗ α.inverse.obj Z)) ≫
             α.unit.app (α.inverse.obj X ⊗ α.inverse.obj (tensor_obj' α Y Z))) =
  (((tensor_hom (𝟙 _) (α.unit_iso.inv.app _)) ≫ (α_ _ _ _).inv) ⊗ 𝟙 _) ≫

  (((α_ (α.inverse.obj W) (α.inverse.obj X) (α.inverse.obj Y)).hom ⊗ 𝟙 (α.inverse.obj Z)) ≫
  (α_ (α.inverse.obj W) (α.inverse.obj X ⊗ α.inverse.obj Y) (α.inverse.obj Z)).hom ≫
    (𝟙 (α.inverse.obj W) ⊗ (α_ (α.inverse.obj X) (α.inverse.obj Y) (α.inverse.obj Z)).hom)) ≫

  (tensor_hom (𝟙 _) (α.unit.app _ ≫ (α.functor ⋙ α.inverse).map (𝟙 _ ⊗ α.unit.app _))) :=
begin
  simp only [functor.map_id, id_tensor_comp, category.assoc, comp_tensor_id, associator_conjugation,
    functor.comp_map, equivalence.inv_fun_map, iso.hom_inv_id_app_assoc, inv_hom_id_tensor_assoc,
    tensor_id, category.id_comp],
  congr' 1,
  simp only [←category.assoc, ←tensor_comp, category.id_comp, iso.hom_inv_id_app],
  erw [category.assoc _ _ (α_ _ _ _).hom, iso.inv_hom_id, category.comp_id, ←tensor_comp,
    category.id_comp],
  simp only [category.assoc],
  congr',
end

lemma pentagon'_aux1 (W X Y Z : D) :
  (α.unit_inv.app (α.inverse.obj (tensor_obj' α W X) ⊗ α.inverse.obj Y) ≫
       ((α.unit_iso.inv.app (α.inverse.obj W ⊗ α.inverse.obj X) ⊗ 𝟙 (α.inverse.obj Y)) ≫
            (α_ (α.inverse.obj W) (α.inverse.obj X) (α.inverse.obj Y)).hom ≫
              (𝟙 (α.inverse.obj W) ⊗ α.unit_iso.hom.app (α.inverse.obj X ⊗ α.inverse.obj Y))) ≫
         α.unit.app (α.inverse.obj W ⊗ α.inverse.obj (tensor_obj' α X Y)) ⊗
     α.inverse.map (𝟙 Z)) ≫
  ((α.unit_iso.inv.app (α.inverse.obj W ⊗ α.inverse.obj (tensor_obj' α X Y)) ⊗ 𝟙 (α.inverse.obj Z))
    ≫ (α_ (α.inverse.obj W) (α.inverse.obj (tensor_obj' α X Y)) (α.inverse.obj Z)).hom ≫
        (𝟙 (α.inverse.obj W) ⊗
          α.unit_iso.hom.app (α.inverse.obj (tensor_obj' α X Y) ⊗ α.inverse.obj Z))) ≫
    (α.inverse.map (𝟙 W) ⊗
       α.unit_inv.app (α.inverse.obj (tensor_obj' α X Y) ⊗ α.inverse.obj Z) ≫
         ((α.unit_iso.inv.app (α.inverse.obj X ⊗ α.inverse.obj Y) ⊗ 𝟙 (α.inverse.obj Z)) ≫
              (α_ (α.inverse.obj X) (α.inverse.obj Y) (α.inverse.obj Z)).hom ≫
                (𝟙 (α.inverse.obj X) ⊗ α.unit_iso.hom.app (α.inverse.obj Y ⊗ α.inverse.obj Z))) ≫
           α.unit.app (α.inverse.obj X ⊗ α.inverse.obj (tensor_obj' α Y Z))) =
  ((α.unit_iso.inv.app _ ≫ (α.unit_iso.inv.app _ ⊗ 𝟙 (α.inverse.obj Y))) ⊗ (𝟙 _)) ≫

  (((α_ (α.inverse.obj W) (α.inverse.obj X) (α.inverse.obj Y)).hom ⊗ 𝟙 (α.inverse.obj Z)) ≫
  (α_ (α.inverse.obj W) (α.inverse.obj X ⊗ α.inverse.obj Y) (α.inverse.obj Z)).hom ≫
    (𝟙 (α.inverse.obj W) ⊗ (α_ (α.inverse.obj X) (α.inverse.obj Y) (α.inverse.obj Z)).hom)) ≫

  ((𝟙 (α.inverse.obj W)) ⊗ (α.unit.app _ ≫ ((α.functor ⋙ α.inverse).map
    (𝟙 (α.inverse.obj X) ⊗ α.unit.app _)))) :=
begin
  simp only [category.assoc],
  erw [←category.assoc (α_ (α.inverse.obj W) (α.inverse.obj (tensor_obj' α X Y))
    (α.inverse.obj Z)).hom, pentagon'_aux10],
  conv_rhs { rw [←category.assoc (tensor_hom (α_ _ _ _).hom _), ←category.assoc (tensor_hom (α_ _ _ _).hom _ ≫ _)], },
  simp only [←category.assoc],
  congr' 4,
  simp only [category.assoc],
  rw [←tensor_comp, ←tensor_comp,
    category.comp_id, category.comp_id, α.inverse.map_id],
  congr' 1,
  simp only [category.assoc],
  rw [iso.hom_inv_id_app_assoc, ←category.assoc (tensor_hom _ _), ←category.assoc (tensor_hom _ _),
    ←tensor_comp, category.comp_id, iso.hom_inv_id_app, tensor_id, category.id_comp],
  simp only [category.assoc, iso.hom_inv_id, category.comp_id],
  congr,
end

lemma pentagon' (W X Y Z : D) :
  tensor_hom' α (associator' α W X Y).hom (𝟙 Z) ≫ (associator' α W (tensor_obj' α X Y) Z).hom ≫
    tensor_hom' α (𝟙 W) (associator' α X Y Z).hom =
  (associator' α (tensor_obj' α W X) Y Z).hom ≫ (associator' α W X (tensor_obj' α Y Z)).hom :=
begin
  conv_rhs { rw [associator'_hom, associator'_hom, ←α.functor.map_comp] },
  rw [pentagon'_aux0, ←pentagon],
  conv_lhs { simp only [associator'_hom, tensor_hom'_def, ←α.functor.map_comp,
    equivalence.inv_fun_map] },
  rw [pentagon'_aux1],
end

lemma triangle'_aux1 (X Y : D) :
  (α.unit_iso.inv.app _ ⊗ 𝟙 (α.inverse.obj Y)) ≫
  (α_ (α.inverse.obj X) (α.inverse.obj (tensor_unit' α)) (α.inverse.obj Y)).hom ≫
    (𝟙 (α.inverse.obj X) ⊗
       (α.unit_iso.inv.app (𝟙_ C) ⊗ 𝟙 (α.inverse.obj Y)) ≫ (λ_ (α.inverse.obj Y)).hom) =
  (α.unit_iso.inv.app _ ≫
    ((tensor_hom (𝟙 (α.inverse.obj _)) (α.unit_iso.inv.app _)) ≫
    (ρ_ (α.inverse.obj X)).hom)) ⊗ 𝟙 _ :=
begin
  simp only [id_tensor_comp, comp_tensor_id, associator_conjugation, category.assoc],
  rw [←tensor_comp, category.id_comp],
  congr' 3,
  erw [←triangle, ←category.assoc (α_ _ _ _).inv, iso.inv_hom_id,
    category.id_comp, ←tensor_comp, category.id_comp],
end

lemma triangle'_aux2 (X Y : D) :
  (𝟙 (α.inverse.obj X) ⊗ α.unit_iso.inv.app (𝟙_ C) ⊗ 𝟙 (α.inverse.obj Y)) ≫
  (α_ (α.inverse.obj X) ((𝟭 C).obj (𝟙_ C)) (α.inverse.obj Y)).inv ≫
    ((ρ_ (α.inverse.obj X)).hom ⊗ 𝟙 (α.inverse.obj Y)) =
  𝟙 _ ⊗ ((tensor_hom (α.unit_iso.inv.app _) (𝟙 _)) ≫ (λ_ _).hom) :=
begin
  simp only [id_tensor_comp],
  erw [←tensor_comp, category.id_comp, ←triangle, ←category.assoc (α_ _ _ _).inv,
    iso.inv_hom_id, category.id_comp, ←tensor_comp, category.id_comp],
end

lemma triangle' (X Y : D) :
  (associator' α X (tensor_unit' α) Y).hom ≫ tensor_hom' α (𝟙 X) (left_unitor' α Y).hom =
  tensor_hom' α (right_unitor' α X).hom (𝟙 Y) :=
begin
  simp only [associator'_hom, functor.map_comp, left_unitor'_hom, iso.app_hom, category.assoc,
    right_unitor'_hom, tensor_hom', functor.map_id, equivalence.inv_fun_map,
    equivalence.unit_inverse_comp, category.comp_id, iso.hom_inv_id_app_assoc,
    id_tensor_comp, comp_tensor_id, associator_conjugation],
  simp only [←α.functor.map_comp, ←tensor_comp, category.id_comp],
  simp only [←category.assoc (α.unit_iso.hom.app _), iso.hom_inv_id_app],
  rw [category.id_comp],
  rw [triangle'_aux1, triangle'_aux2],
  congr' 1,
  simp only [comp_tensor_id, associator_conjugation, category.assoc, id_tensor_comp],
  erw [←triangle, ←category.assoc (α_ _ _ _).inv, iso.inv_hom_id, category.id_comp, ←tensor_comp,
    category.id_comp],
  congr' 1,
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
  right_unitor := of_equivalence.right_unitor' α,
  right_unitor_naturality' := λ _ _, of_equivalence.right_unitor'_naturality α,
  pentagon' := of_equivalence.pentagon' α,
  triangle' := of_equivalence.triangle' α }

end monoidal_category

end category_theory
