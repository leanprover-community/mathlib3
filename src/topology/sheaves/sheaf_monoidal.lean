import topology.sheaves.presheaf_monoidal
import topology.sheaves.sheaf_condition.unique_gluing

noncomputable theory

namespace Top.sheaf

open Top Top.presheaf topological_space
open category_theory category_theory.monoidal_category category_theory.limits

universe u

variables {X : Top.{u}}

alias presheaf.monoidal.ihom_obj ← presheaf.ihom_obj

lemma restrict_is_sheaf {F : Top.presheaf AddCommGroup.{u} X} (hF : is_sheaf F) (U : opens X) :
  is_sheaf (F.restrict U) :=
sorry

lemma ihom_obj_is_sheaf_of_is_sheaf {F G : Top.presheaf AddCommGroup.{u} X}
  (hF : is_sheaf F) (hG : is_sheaf G) : is_sheaf (presheaf.ihom_obj F G) :=
sorry -- probably harder


instance : monoidal_category ((opens X)ᵒᵖ ⥤ AddCommGroup.{u}) :=
presheaf.monoidal.monoidal_presheaf_AddCommGroup

instance : preserves_limits (category_theory.forget AddCommGroup.{u}) :=
AddCommGroup.forget_preserves_limits.{u u}

instance (U : opens X) : preserves_colimits_of_shape ((opens.grothendieck_topology X).cover U)ᵒᵖ
  (category_theory.forget AddCommGroup.{u}) :=
begin
  haveI := AddCommGroup.filtered_colimits.forget_preserves_filtered_colimits.{u},
  apply_instance
end

@[simps] def sheaf_iso_mk {F G : sheaf AddCommGroup.{u} X} (ι : F.val ≅ G.val) : F ≅ G :=
{ hom := ⟨ι.hom⟩,
  inv := ⟨ι.inv⟩,
  hom_inv_id' := Sheaf.hom.ext _ _ $ ι.hom_inv_id,
  inv_hom_id' := Sheaf.hom.ext _ _ $ ι.inv_hom_id }

@[simps] def presheaf_to_Sheaf_map_iso {F G : Top.presheaf AddCommGroup.{u} X} (ι : F ≅ G) :
  (presheaf_to_Sheaf _ _).obj F ≅ (presheaf_to_Sheaf _ _).obj G :=
sheaf_iso_mk
{ hom := ((presheaf_to_Sheaf _ _).map ι.hom).val,
  inv := ((presheaf_to_Sheaf _ _).map ι.inv).val,
  hom_inv_id' :=
  begin
    ext U x,
    change ((presheaf_to_Sheaf _ _).map ι.hom ≫ (presheaf_to_Sheaf _ _).map _).val.app U x = x,
    rw [←(presheaf_to_Sheaf _ _).map_comp, ι.hom_inv_id, (presheaf_to_Sheaf _ _).map_id],
    refl,
  end,
  inv_hom_id' :=
  begin
    ext U x,
    change ((presheaf_to_Sheaf _ _).map ι.inv ≫ (presheaf_to_Sheaf _ _).map _).val.app U x = x,
    rw [←(presheaf_to_Sheaf _ _).map_comp, ι.inv_hom_id, (presheaf_to_Sheaf _ _).map_id],
    refl,
  end, }

namespace constructions

@[simps] def tensor_obj' (F G : sheaf AddCommGroup.{u} X) : sheaf AddCommGroup.{u} X :=
(presheaf_to_Sheaf _ _).obj $ F.val ⊗ G.val

local infixr (name := tensor_obj') `⊙`:50 := tensor_obj'

@[simps] def tensor_obj'_swap (F G : sheaf AddCommGroup.{u} X) :
  F ⊙ G ≅ G ⊙ F :=
presheaf_to_Sheaf_map_iso $ nat_iso.of_components (λ U,
{ hom := (tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (F.val.obj U) _ _ $
    AddCommGroup.monoidal.curry $ 𝟙 _).to_add_monoid_hom,
  inv := (tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (G.val.obj U) _ _ $
    AddCommGroup.monoidal.curry $ 𝟙 _).to_add_monoid_hom,
  hom_inv_id' :=
  begin
    ext x,
    induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero] },
    { simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
        AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.to_fun_eq_coe,
        AddCommGroup.monoidal.curry_apply_apply, id_apply] },
    { rw [map_add, ha, hb, map_add] },
  end,
  inv_hom_id' :=
  begin
    ext x,
    induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero] },
    { simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
        AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.to_fun_eq_coe,
        AddCommGroup.monoidal.curry_apply_apply, id_apply] },
    { rw [map_add, ha, hb, map_add] },
  end }) $ λ U V inc,
begin
  ext x,
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero] },
  { simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
      AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.to_fun_eq_coe,
      AddCommGroup.monoidal.curry_apply_apply, id_apply, monoidal.tensor_obj_map,
      AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
      AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul], },
  { rw [map_add, ha, hb, map_add] },
end

open category_theory.grothendieck_topology

@[simps] def tensor_hom' {X₁ Y₁ X₂ Y₂ : sheaf AddCommGroup.{u} X}
  (α : X₁ ⟶ Y₁) (β : X₂ ⟶ Y₂) : (X₁ ⊙ X₂ ⟶ Y₁ ⊙ Y₂) :=
⟨sheafify_map _ $ α.val ⊗ β.val⟩

local infixr (name := tensor_hom') `⊙`:81 := tensor_hom'

lemma tensor_id' (F G : sheaf AddCommGroup.{u} X) : (𝟙 F) ⊙ (𝟙 G) = 𝟙 (tensor_obj' F G) :=
Sheaf.hom.ext _ _ $ by simpa

lemma tensor_comp' {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : sheaf AddCommGroup.{u} X}
  (α₁ : X₁ ⟶ Y₁) (α₂ : X₂ ⟶ Y₂) (β₁ : Y₁ ⟶ Z₁) (β₂ : Y₂ ⟶ Z₂) :
  (α₁ ≫ β₁) ⊙ (α₂ ≫ β₂) = α₁ ⊙ α₂ ≫ β₁ ⊙ β₂ :=
Sheaf.hom.ext _ _ $ by simp

@[simps] def tensor_unit' : sheaf AddCommGroup.{u} X :=
(presheaf_to_Sheaf _ AddCommGroup).obj (𝟙_ _)

@[simps] def tensor_left' (F : sheaf AddCommGroup.{u} X) :
  sheaf AddCommGroup.{u} X ⥤ sheaf AddCommGroup.{u} X :=
{ obj := λ G, tensor_obj' F G,
  map := λ _ _ α, tensor_hom' (𝟙 F) α,
  map_id' := λ G, Sheaf.hom.ext _ _ $ by simpa,
  map_comp' := λ _ _ _ α β, Sheaf.hom.ext _ _ $ by simp }

@[simps] def ihom_obj' (F G : sheaf AddCommGroup.{u} X) : sheaf AddCommGroup.{u} X :=
{ val := presheaf.monoidal.ihom_obj F.val G.val,
  cond := ihom_obj_is_sheaf_of_is_sheaf F.cond G.cond }

local notation `⟦` F, G `⟧` := ihom_obj' F G

@[simps] def ihom' (F : sheaf AddCommGroup.{u} X) :
  sheaf AddCommGroup.{u} X ⥤ sheaf AddCommGroup.{u} X :=
{ obj := ihom_obj' F,
  map := λ G₁ G₂ α, ⟨presheaf.monoidal.ihom_map _ _ _ α.val⟩,
  map_id' := λ G,
  begin
    ext U x y z,
    simp only [Sheaf.category_theory.category_id_val, presheaf.monoidal.ihom_map_app_2,
      presheaf.monoidal.ihom_map_app_apply_app, presheaf.monoidal.ihom_map'_app_apply,
      nat_trans.id_app, id_apply],
    simp only [←comp_apply, category.assoc, ←G.val.map_comp],
    congr' 1,
    convert category.comp_id _,
    convert G.val.map_id _,
  end,
  map_comp' := λ G₁ G₂ G₃ α β,
  begin
    ext U x y z,
    simp only [Sheaf.category_theory.category_comp_val, presheaf.monoidal.ihom_map_app_2,
      presheaf.monoidal.ihom_map_app_apply_app, presheaf.monoidal.ihom_map'_app_apply,
      nat_trans.comp_app, comp_apply],
    simp only [←comp_apply, category.assoc],
    rw [←category.assoc (G₂.val.map _), ←G₂.val.map_comp],
    congr' 4,
    erw ←β.val.naturality,
    rw [←category.assoc, ←G₂.val.map_comp],
    refl,
  end }

namespace tensor_left'_ihom'_adj

variables (F : sheaf AddCommGroup.{u} X)

local notation (name := local_adj) `adj` :=
  adjunction.comp (presheaf.monoidal.tensor_ihom_adj F.val)
    (sheafification_adjunction (opens.grothendieck_topology X) _)

@[simps] def hom_equiv'.from_tensor (G₁ G₂ : sheaf AddCommGroup X) (α : (tensor_left' F).obj G₁ ⟶ G₂) :
  G₁ ⟶ ⟦F, G₂⟧ :=
Sheaf.hom.mk $ (adj .hom_equiv _ G₂ α)

@[simps] def hom_equiv'.to_tensor (G₁ G₂ : sheaf AddCommGroup X) (α : G₁ ⟶ ⟦F, G₂⟧) :
  (tensor_left' F).obj G₁ ⟶ G₂ :=
Sheaf.hom.mk $ sheafify_lift _
  (((presheaf.monoidal.tensor_ihom_adj F.val).hom_equiv G₁.val G₂.val).symm α.val) G₂.cond

lemma hom_equiv'.left_inv_aux (G₁ G₂ : sheaf AddCommGroup X)
  (α : (tensor_left' F).obj G₁ ⟶ G₂) (U : (opens X)ᵒᵖ)
  (x : (F.val ⊗ G₁.val).obj U) :
  (((opens.grothendieck_topology X).to_sheafify (F.val ⊗ G₁.val) ≫ α.val).app U) x =
  (((((monoidal.tensor_ihom_adj F.val).hom_equiv G₁.val G₂.val).symm)
      (hom_equiv'.from_tensor F G₁ G₂ α).val).app U) x:=
begin
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero] },
  { simp only [nat_trans.comp_app, comp_apply, monoidal.tensor_ihom_adj_hom_equiv,
      hom_equiv'.from_tensor_val, adjunction.hom_equiv_unit, functor.comp_map,
      monoidal.ihom_map_2, monoidal.tensor_ihom_adj.hom_equiv'_symm_apply,
      monoidal.tensor_ihom_adj.hom_equiv'.to_tensor_app, linear_map.coe_mk,
      monoidal.tensor_ihom_adj.hom_equiv'.to_tensor_app_apply_apply, restrict_top_apply,
      monoidal.ihom_map_app_2, category.assoc, tensor_product.lift.tmul,
      AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.to_fun_eq_coe,
      AddCommGroup.monoidal.curry_apply_apply, AddCommGroup.monoidal.uncurry'_apply,
      restrict_top_add_monoid_hom_apply, Sheaf_to_presheaf_map, adjunction.comp,
      equiv.trans_apply, monoidal.tensor_ihom_adj.hom_equiv'_apply,
      monoidal.tensor_ihom_adj.hom_equiv'.from_tensor_app_apply_2,
      monoidal.tensor_ihom_adj.hom_equiv'.from_tensor_app_apply_app,
      sheafification_adjunction_unit_app],
    simp only [←comp_apply, category.assoc],
    erw ←α.val.naturality,
    simp only [comp_apply],
    congr' 1,
    simp only [←comp_apply],
    erw ←((opens.grothendieck_topology X).to_sheafify (F.val ⊗ G₁.val)).naturality,
    congr' 1,
    simp only [monoidal.tensor_obj_map, AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
      AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
      AddCommGroup.to_int_linear_map_apply],
    simp only [←comp_apply, ←category_theory.functor.map_comp],
    congr' 1; symmetry; convert id_apply _; convert category_theory.functor.map_id _ _; congr, },
  { rw [map_add, ha, hb, map_add] }
end

@[simps] def hom_equiv' (G₁ G₂ : sheaf AddCommGroup X) :
  ((tensor_left' F).obj G₁ ⟶ G₂) ≃ (G₁ ⟶ (ihom' F).obj G₂) :=
{ to_fun := hom_equiv'.from_tensor _ _ _,
  inv_fun := hom_equiv'.to_tensor _ _ _,
  left_inv := λ α,
  begin
    ext1,
    change sheafify_lift _ _ _ = _,
    refine (sheafify_lift_unique _ _ _ _ _).symm,
    ext U x,
    apply hom_equiv'.left_inv_aux,
  end,
  right_inv := λ α,
  begin
    ext U x : 4,
    dsimp,
    simp only [adjunction.comp, equiv.trans_apply, presheaf.monoidal.tensor_ihom_adj,
      presheaf.monoidal.tensor_ihom_adj.hom_equiv'_apply,
      presheaf.monoidal.tensor_ihom_adj.hom_equiv'.from_tensor_app_apply_2],
    ext V y : 3,
    simp only [presheaf.monoidal.tensor_ihom_adj.hom_equiv'.from_tensor_app_apply_app,
      AddCommGroup.monoidal.curry_apply_apply, adjunction.hom_equiv_unit,
      sheafification_adjunction_unit_app, Sheaf_to_presheaf_map, hom_equiv'.to_tensor_val,
      to_sheafify_sheafify_lift, presheaf.monoidal.tensor_ihom_adj_hom_equiv,
      presheaf.monoidal.tensor_ihom_adj.hom_equiv'_symm_apply],
    dsimp,
    simp only [tensor_product.lift.tmul, AddCommGroup.to_int_linear_map₂_apply_apply,
      add_monoid_hom.to_fun_eq_coe, AddCommGroup.monoidal.curry_apply_apply,
      AddCommGroup.monoidal.uncurry'_apply, linear_map.coe_mk, comp_apply,
      restrict_top_add_monoid_hom_apply, restrict_top_apply],
    simp only [←comp_apply],
    erw [α.val.naturality],
    dsimp,
    simp only [comp_apply, monoidal.ihom_obj_map_apply, quiver.hom.unop_op,
      restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply],
    simp only [←comp_apply, ←F.val.map_comp],
    simp only [category.assoc, ←G₂.val.map_comp],
    erw [←(α.val.app _ _).naturality],
    swap,
    { change _ ⟶ opposite.op V.unop,
      refine quiver.hom.op (hom_of_le _),
      intros x hx,
      refine ⟨⟨_, ⟨x, hx, rfl⟩⟩, ⟨⟩, _⟩,
      ext, refl, },
    erw [←category.assoc, ←F.val.map_comp, F.val.map_id, category.id_comp],
  end }

end tensor_left'_ihom'_adj

@[simps] def tensor_left'_ihom'_adj (F : sheaf AddCommGroup.{u} X) : tensor_left' F ⊣ ihom' F :=
{ hom_equiv := tensor_left'_ihom'_adj.hom_equiv' F,
  unit := sorry,
  counit := sorry,
  hom_equiv_unit' := sorry,
  hom_equiv_counit' := sorry }

end constructions

end Top.sheaf
