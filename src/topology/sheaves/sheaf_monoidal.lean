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

def sheaf_restrict (F : sheaf AddCommGroup.{u} X) (U : opens X) :
  sheaf AddCommGroup.{u} (Top.of U) := ⟨_, restrict_is_sheaf F.cond U⟩

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

@[simps] def presheaf_to_Sheaf_iso {F G : Top.presheaf AddCommGroup.{u} X} (ι : F ≅ G) :
  (presheaf_to_Sheaf (opens.grothendieck_topology X) AddCommGroup.{u}).obj F ≅
  (presheaf_to_Sheaf (opens.grothendieck_topology X) AddCommGroup.{u}).obj G :=
sheaf_iso_mk
{ hom := grothendieck_topology.sheafify_map _ ι.hom,
  inv := grothendieck_topology.sheafify_map _ ι.inv,
  hom_inv_id' := by simpa only [←grothendieck_topology.sheafify_map_comp, ι.hom_inv_id, grothendieck_topology.sheafify_map_id,
    Sheaf.category_theory.category_id_val],
  inv_hom_id' := by simpa only [←grothendieck_topology.sheafify_map_comp, ι.inv_hom_id, grothendieck_topology.sheafify_map_id,
    Sheaf.category_theory.category_id_val], }

@[simps] def presheaf_tensor_obj_swap (F G : Top.presheaf AddCommGroup.{u} X) :
  F ⊗ G ≅ G ⊗ F :=
nat_iso.of_components (λ U,
{ hom := (tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (F.obj U) _ _ $
    AddCommGroup.monoidal.curry $ 𝟙 _).to_add_monoid_hom,
  inv := (tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (G.obj U) _ _ $
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

open category_theory.grothendieck_topology

@[simps] def sheafify_restrict_to_restrict_sheafify (F : Top.presheaf AddCommGroup.{u} X) (U : opens X) :
  (opens.grothendieck_topology U).sheafify (restrict F U) ⟶ restrict (sheafify _ F) U :=
sheafify_lift _ ((restrict_functor U).map $ to_sheafify _ _)
  (restrict_is_sheaf (sheafify_is_sheaf _ F) U)

instance sheafify_restrict_to_restrict_shefify_is_iso
  (F : Top.presheaf AddCommGroup.{u} X) (U : opens X) :
  is_iso $ sheafify_restrict_to_restrict_sheafify F U :=
sorry

def restrict_sheafify_to_sheafify_restrict (F : Top.presheaf AddCommGroup.{u} X) (U : opens X) :
  restrict ((opens.grothendieck_topology X).sheafify F) U ⟶
  sheafify _ (restrict F U) :=
inv (sheafify_restrict_to_restrict_sheafify F U)

namespace constructions

@[simps] def tensor_obj' (F G : sheaf AddCommGroup.{u} X) : sheaf AddCommGroup.{u} X :=
(presheaf_to_Sheaf _ _).obj $ F.val ⊗ G.val

local infixr (name := tensor_obj') `⊙`:50 := tensor_obj'

@[simps] def tensor_obj'_swap (F G : sheaf AddCommGroup.{u} X) :
  F ⊙ G ≅ G ⊙ F :=
presheaf_to_Sheaf_map_iso $ presheaf_tensor_obj_swap F.val G.val

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

example : true := ⟨⟩

@[simps] def unit'_app (G : sheaf AddCommGroup.{u} X) :
  G.hom $ (tensor_left' F ⋙ ihom' F).obj G := Sheaf.hom.mk $ adj .unit.app G.val

lemma unit'_naturality (G₁ G₂ : sheaf AddCommGroup X)
  (α : G₁ ⟶ G₂) :
  α ≫ unit'_app F G₂ = unit'_app F G₁ ≫ (tensor_left' F ⋙ ihom' F).map α :=
begin
  ext1,
  simp only [Sheaf.category_theory.category_comp_val, unit'_app_val],
  erw ←nat_trans.naturality,
  congr,
end

@[simps] def unit' : 𝟭 (sheaf AddCommGroup.{u} X) ⟶ tensor_left' F ⋙ ihom' F :=
{ app := unit'_app F,
  naturality' := unit'_naturality F }

@[simps] def counit' : ihom' F ⋙ tensor_left' F ⟶ 𝟭 (sheaf AddCommGroup.{u} X) :=
adj .counit

lemma hom_equiv_unit' (G₁ G₂ : sheaf AddCommGroup X)
  (α : (tensor_left' F).obj G₁ ⟶ G₂) :
  hom_equiv' F G₁ G₂ α = (unit' F).app G₁ ≫ (ihom' F).map α :=
begin
  ext1,
  simp only [hom_equiv'_apply, unit'_app_2, Sheaf.category_theory.category_comp_val, unit'_app_val,
    hom_equiv'.from_tensor_val, adjunction.hom_equiv_unit, functor.comp_map, Sheaf_to_presheaf_map,
    monoidal.ihom_map_2, ihom'_map_val],
  congr' 1,
end

lemma hom_equiv_counit'_aux (G₁ G₂ : sheaf AddCommGroup.{u} X)
  (α : G₁ ⟶ (ihom' F).obj G₂) (U : (opens ↥X)ᵒᵖ)
  (x : (F.val ⊗ G₁.val).obj U) :
  ((opens.grothendieck_topology X).to_sheafify (F.val ⊗ G₁.val) ≫
    (opens.grothendieck_topology X).sheafify_map (𝟙 F.val ⊗ α.val) ≫
    ((tensor_left'_ihom'_adj.counit' F).app G₂).val).app U x =
  (monoidal.tensor_ihom_adj.hom_equiv'.to_tensor F.val G₁.val G₂.val α.val).app U x :=
begin
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero] },
  { rw [nat_trans.comp_app, nat_trans.comp_app, comp_apply, comp_apply, counit'_app_val_app_apply,
      ←comp_apply, ←nat_trans.comp_app, sheafify_map_sheafify_lift, category.comp_id,
      ←comp_apply, ←nat_trans.comp_app, sheafify_map_sheafify_lift, ←comp_apply,
      ←nat_trans.comp_app, to_sheafify_sheafify_lift, nat_trans.comp_app, comp_apply,
      presheaf.monoidal.tensor_ihom_adj.counit'_app_app,
      presheaf.monoidal.tensor_ihom_adj.counit'_app_sections_apply],
    erw tensor_product.lift.tmul,
    rw [AddCommGroup.to_int_linear_map_apply, nat_trans.id_app, id_apply,
      AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.to_fun_eq_coe,
      add_monoid_hom.coe_mk, add_monoid_hom.coe_mk, AddCommGroup.to_int_linear_map_apply,
      presheaf.monoidal.tensor_ihom_adj.hom_equiv'.to_tensor_app,
      presheaf.monoidal.tensor_ihom_adj.hom_equiv'.to_tensor_app_apply_apply,
      tensor_product.lift.tmul, AddCommGroup.to_int_linear_map₂_apply_apply,
      add_monoid_hom.to_fun_eq_coe, AddCommGroup.monoidal.curry_apply_apply,
      AddCommGroup.monoidal.uncurry'_apply, tensor_product.lift.tmul,
      linear_map.coe_mk, linear_map.coe_mk, comp_apply, restrict_top_add_monoid_hom_apply,
      restrict_top_apply],
    },
  { rw [map_add, ha, hb, map_add] },
end

end tensor_left'_ihom'_adj

@[simps] def tensor_left'_ihom'_adj (F : sheaf AddCommGroup.{u} X) : tensor_left' F ⊣ ihom' F :=
{ hom_equiv := tensor_left'_ihom'_adj.hom_equiv' F,
  unit := tensor_left'_ihom'_adj.unit' F,
  counit := tensor_left'_ihom'_adj.counit' F,
  hom_equiv_unit' := tensor_left'_ihom'_adj.hom_equiv_unit' F,
  hom_equiv_counit' := λ G₁ G₂ α,
  begin
    ext1,
    simp only [tensor_left'_ihom'_adj.hom_equiv'_symm_apply,
      tensor_left'_ihom'_adj.hom_equiv'.to_tensor_val,
      monoidal.tensor_ihom_adj_hom_equiv, monoidal.tensor_ihom_adj.hom_equiv'_symm_apply,
      tensor_left'_map, Sheaf.category_theory.category_comp_val, tensor_hom'_val,
      Sheaf.category_theory.category_id_val],
    refine (sheafify_lift_unique _ _ _ _ _).symm,
    ext U x : 3,
    apply tensor_left'_ihom'_adj.hom_equiv_counit'_aux,
  end }

@[simps] def curry {F G H : sheaf AddCommGroup.{u} X} (f : tensor_obj' F G ⟶ H) : G ⟶ ⟦F, H⟧ :=
(tensor_left'_ihom'_adj F).hom_equiv _ _ f

def curry' {F G H : sheaf AddCommGroup.{u} X} (f : tensor_obj' F G ⟶ H) : F ⟶ ⟦G, H⟧ :=
curry $ (tensor_obj'_swap G F).hom ≫ f

@[simps] def uncurry {F G H : sheaf AddCommGroup.{u} X} (f : G ⟶ ⟦F, H⟧) : tensor_obj' F G ⟶ H :=
((tensor_left'_ihom'_adj F).hom_equiv _ _).symm f

@[simps] def uncurry' {F G H : sheaf AddCommGroup.{u} X} (f : F ⟶ ⟦G, H⟧) : tensor_obj' F G ⟶ H :=
uncurry $ curry' $ uncurry f

lemma uncurry'_val_app_apply2 {F G H : sheaf AddCommGroup.{u} X} (f : F ⟶ ⟦G, H⟧) (U : (opens X)ᵒᵖ)
  (x : (tensor_obj' F G).val.obj U) :
  (uncurry' f).val.app U x =
  (uncurry f).val.app U ((tensor_obj'_swap F G).hom.val.app U x) :=
sorry

namespace associator_right

variables (F G H : sheaf AddCommGroup.{u} X)

local attribute [instance] AddCommGroup.monoidal.tensor_monoidal_category

@[simps] def aux0_app_aux {U : (opens X)ᵒᵖ} (x : F.val.obj U) (y : G.val.obj U) :
  restrict H.val U.unop ⟶
  restrict ((opens.grothendieck_topology X).sheafify ((F.val ⊗ G.val) ⊗ H.val)) U.unop := (
{ app := λ V, (
  { to_fun := λ z,
      (F.val.map (hom_of_le $ by { rintros _ ⟨x, _, rfl⟩, exact x.2 } :
          (emb.open_embedding U.unop).is_open_map.functor.obj V.unop ⟶ U.unop).op x ⊗ₜ
      G.val.map (hom_of_le $ by { rintros _ ⟨x, _, rfl⟩, exact x.2 } :
          (emb.open_embedding U.unop).is_open_map.functor.obj V.unop ⟶ U.unop).op y) ⊗ₜ z,
    map_zero' := by rw [tensor_product.tmul_zero],
    map_add' := λ _ _, by rw [tensor_product.tmul_add] } : H.val.obj ((emb.open_embedding U.unop).is_open_map.functor.op.obj V) ⟶
      (F.val.obj ((emb.open_embedding U.unop).is_open_map.functor.op.obj V) ⊗
        G.val.obj ((emb.open_embedding U.unop).is_open_map.functor.op.obj V)) ⊗
      H.val.obj ((emb.open_embedding U.unop).is_open_map.functor.op.obj V)),
  naturality' := λ V₁ V₂ inc,
  begin
    ext z,
    simp only [comp_apply, restrict_map, add_monoid_hom.coe_mk],
    congr' 2;
    simp only [AddCommGroup.to_int_linear_map_apply, ←comp_apply,
      ←category_theory.functor.map_comp];
    congr,
  end } : restrict H.val U.unop ⟶ restrict ((F.val ⊗ G.val) ⊗ H.val) U.unop) ≫ to_sheafify _ _ ≫
sheafify_restrict_to_restrict_sheafify _ _

@[simps] def aux0_app (U : (opens X)ᵒᵖ) :
  (tensor_obj (F.val.obj U) (G.val.obj U)) ⟶
    AddCommGroup.of (restrict H.val U.unop ⟶
      (restrict ((opens.grothendieck_topology X).sheafify ((F.val ⊗ G.val) ⊗ H.val))) U.unop) :=
(tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (F.val.obj U) _ _ $
({ to_fun := λ x,
  { to_fun := λ y, aux0_app_aux F G H x y,
    map_zero' :=
    begin
      ext V y : 3,
      simp only [aux0_app_aux_app_apply, nat_trans.app_zero, AddCommGroup.zero_apply, map_zero,
        tensor_product.tmul_zero, tensor_product.zero_tmul],
    end,
    map_add' := λ y₁ y₂,
    begin
      ext V z : 3,
      simp only [aux0_app_aux_app_apply, nat_trans.app_add, add_monoid_hom.add_apply, map_add,
        tensor_product.tmul_add, tensor_product.add_tmul],
    end },
  map_zero' :=
  begin
    ext x V y : 4,
    simp only [AddCommGroup.zero_apply, nat_trans.app_zero, add_monoid_hom.coe_mk,
      aux0_app_aux_app_apply, map_zero, tensor_product.tmul_zero, tensor_product.zero_tmul],
  end,
  map_add' := λ x₁ x₂,
  begin
    ext y V z : 4,
    simp only [add_monoid_hom.coe_mk, add_monoid_hom.add_apply, aux0_app_aux_app_apply,
      nat_trans.app_add, tensor_product.tmul_add, tensor_product.add_tmul, map_add],
  end } : F.val.obj U ⟶ AddCommGroup.of (G.val.obj U ⟶ AddCommGroup.of
  (restrict H.val (opposite.unop U) ⟶
    restrict ((opens.grothendieck_topology X).sheafify ((F.val ⊗ G.val) ⊗ H.val)) U.unop)))).to_add_monoid_hom

@[simps] def aux0 : F.val ⊗ G.val ⟶ presheaf.monoidal.ihom_obj H.val
  ((opens.grothendieck_topology X).sheafify ((F.val ⊗ G.val) ⊗ H.val)) :=
{ app := aux0_app F G H,
  naturality' := λ U V inc,
  begin
    ext z : 1,
    induction z using tensor_product.induction_on with x y x y hx hy,
    { simp only [map_zero] },
    { simp only [comp_apply, aux0_app_apply, monoidal.tensor_obj_map,
        AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,  tensor_product.map_tmul,
        AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
        AddCommGroup.to_int_linear_map_apply, tensor_product.lift.tmul, add_monoid_hom.coe_mk,
        AddCommGroup.to_int_linear_map₂_apply_apply, monoidal.ihom_obj_map_apply],
      ext W z : 3,
      simp only [aux0_app_aux, nat_trans.comp_app, restrict_subset_sections_map_app,
        comp_apply, add_monoid_hom.coe_mk, sheafify_restrict_to_restrict_sheafify],
      conv_lhs { rw [←comp_apply, ←nat_trans.comp_app, to_sheafify_sheafify_lift] },
      conv_rhs { rw [to_sheafify_sheafify_lift] },
      conv_rhs { rw [restrict_subset_sections_map.app_apply, nat_trans.comp_app, comp_apply,
        add_monoid_hom.coe_mk] },
      change _ = ((opens.grothendieck_topology X).sheafify ((F.val ⊗ G.val) ⊗ H.val)).map _ _,
      conv_rhs { rw [restrict_functor_map_app, ←comp_apply] },
      erw ←((opens.grothendieck_topology X).to_sheafify ((F.val ⊗ G.val) ⊗ H.val)).naturality,
      rw [comp_apply],
      simp only [restrict_functor_map_app, monoidal.tensor_obj_map,
        AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
        AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
        AddCommGroup.to_int_linear_map_apply],
      congr' 1,
      simp only [←comp_apply, ←F.val.map_comp, ←G.val.map_comp, ←H.val.map_comp],
      congr' 1,
      convert_to z = H.val.map (𝟙 _) _,
      rw [H.val.map_id, id_apply], },
    { rw [map_add, hx, hy, map_add] },
  end }

example : true := ⟨⟩

def to_sheafify_once :
  tensor_obj' (tensor_obj' F G) H ⟶ (presheaf_to_Sheaf _ _).obj ((F.val ⊗ G.val) ⊗ H.val) :=
uncurry' $ ((sheafification_adjunction _ _).hom_equiv _ _).symm $ by exact aux0 F G H

lemma to_sheafify_once_def :
  to_sheafify_once F G H = uncurry' (((sheafification_adjunction _ _).hom_equiv _ _).symm $
    by exact aux0 F G H) := rfl

@[simps] def from_sheafify_once :
  (presheaf_to_Sheaf _ _).obj ((F.val ⊗ G.val) ⊗ H.val) ⟶ tensor_obj' (tensor_obj' F G) H :=
(presheaf_to_Sheaf _ _).map $ (to_sheafify _ _) ⊗ 𝟙 _

lemma from_sheafify_once_def :
  from_sheafify_once F G H = ((presheaf_to_Sheaf _ _).map $ (to_sheafify _ _) ⊗ 𝟙 _) := rfl

@[simps] def iso_sheafify_once :
  tensor_obj' (tensor_obj' F G) H ≅ (presheaf_to_Sheaf _ _).obj ((F.val ⊗ G.val) ⊗ H.val) :=
-- sheaf_iso_mk
{ hom := to_sheafify_once F G H,
  inv := from_sheafify_once F G H,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end associator_right

namespace associator_left

variables (F G H : sheaf AddCommGroup.{u} X)

local attribute [instance] AddCommGroup.monoidal.tensor_monoidal_category

@[simps] def aux0_app_aux (U : (opens X)ᵒᵖ) (x : G.val.obj U) (y : H.val.obj U) :
  restrict F.val (opposite.unop U) ⟶
  restrict (F.val ⊗ G.val ⊗ H.val) (opposite.unop U) :=
{ app := λ V,
  { to_fun := λ z, z ⊗ₜ (G.val.map (hom_of_le $ λ _ hx, by { rcases hx with ⟨y, hy, rfl⟩, exact y.2 } :
      (emb.open_embedding U.unop).is_open_map.functor.obj V.unop ⟶ U.unop).op x ⊗ₜ H.val.map
      (hom_of_le $ λ _ hx, by { rcases hx with ⟨y, hy, rfl⟩, exact y.2 } :
      (emb.open_embedding U.unop).is_open_map.functor.obj V.unop ⟶ U.unop).op y),
    map_zero' := tensor_product.zero_tmul _ _,
    map_add' := λ _ _, tensor_product.add_tmul _ _ _ },
  naturality' := λ U V inc,
  begin
    ext1 z,
    simp only [restrict_map, comp_apply, add_monoid_hom.coe_mk, monoidal.tensor_obj_map,
      AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
      AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
      AddCommGroup.to_int_linear_map_apply],
    congr' 2;
    rw [←comp_apply, ←category_theory.functor.map_comp];
    congr,
  end }

def aux0_app (U : (opens X)ᵒᵖ) :
  G.val.obj U ⊗ H.val.obj U ⟶
  AddCommGroup.of (restrict F.val U.unop ⟶
    restrict ((opens.grothendieck_topology X).sheafify (F.val ⊗ G.val ⊗ H.val)) U.unop) :=
(tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (G.val.obj U) _ _
{ to_fun := λ x, ({ to_fun := λ y, ((aux0_app_aux F G H U x y : restrict F.val (opposite.unop U) ⟶ restrict (F.val ⊗ G.val ⊗ H.val) (opposite.unop U)) ≫ to_sheafify _ _ ≫ sheafify_restrict_to_restrict_sheafify _ _:
    restrict F.val (opposite.unop U) ⟶
    restrict ((opens.grothendieck_topology X).sheafify (F.val ⊗ G.val ⊗ H.val)) (opposite.unop U)),
    map_zero' :=
    begin
      ext V y : 3,
      simp only [nat_trans.app_zero, AddCommGroup.zero_apply, comp_apply, nat_trans.comp_app,
        aux0_app_aux_app_apply, sheafify_restrict_to_restrict_sheafify_app_apply],
      simp only [map_zero, tensor_product.tmul_zero],
    end,
    map_add' := λ y₁ y₂,
    begin
      ext V z : 3,
      simp only [nat_trans.app_add, add_monoid_hom.add_apply, nat_trans.comp_app, comp_apply,
        map_add, aux0_app_aux_app_apply, tensor_product.tmul_add, tensor_product.add_tmul],
    end } : H.val.obj U ⟶
    AddCommGroup.of
      (restrict F.val (opposite.unop U) ⟶
      restrict ((opens.grothendieck_topology ↥X).sheafify (F.val ⊗ G.val ⊗ H.val)) (opposite.unop U))),
  map_zero' :=
  begin
    ext x V y : 4,
    simp only [AddCommGroup.zero_apply, nat_trans.app_zero, add_monoid_hom.coe_mk, comp_apply,
      aux0_app_aux_app_apply, nat_trans.comp_app, map_zero, tensor_product.tmul_zero,
      tensor_product.zero_tmul],
  end,
  map_add' := λ x₁ x₂,
  begin
    ext V y z : 4,
    simp only [add_monoid_hom.add_apply, add_monoid_hom.coe_mk, nat_trans.comp_app,
      nat_trans.app_add, comp_apply, aux0_app_aux_app_apply, map_add, tensor_product.add_tmul,
      tensor_product.tmul_add],
  end }).to_add_monoid_hom

def aux0 :
  G.val ⊗ H.val ⟶
  presheaf.monoidal.ihom_obj F.val
    ((opens.grothendieck_topology X).sheafify (F.val ⊗ G.val ⊗ H.val)) :=
{ app := aux0_app F G H,
  naturality' := λ U V inc,
  begin
    ext z : 1,
    induction z using tensor_product.induction_on with x y x y hx hy,
    { simp only [map_zero] },
    { simp only [comp_apply, aux0_app, monoidal.tensor_obj_map, linear_map.to_add_monoid_hom_coe,
        AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,  tensor_product.map_tmul,
        AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
        AddCommGroup.to_int_linear_map_apply, tensor_product.lift.tmul, add_monoid_hom.coe_mk,
        AddCommGroup.to_int_linear_map₂_apply_apply, monoidal.ihom_obj_map_apply],
      ext W z : 3,
      simp only [aux0_app_aux_app_apply, nat_trans.comp_app, restrict_subset_sections_map_app,
        comp_apply, add_monoid_hom.coe_mk, sheafify_restrict_to_restrict_sheafify],
      conv_lhs { rw [←comp_apply, ←nat_trans.comp_app, to_sheafify_sheafify_lift,
        restrict_functor_map_app] },
      conv_rhs { rw [to_sheafify_sheafify_lift] },
      conv_rhs { rw [restrict_subset_sections_map.app_apply, nat_trans.comp_app, comp_apply,
        restrict_subset_sections, aux0_app_aux_app_apply, restrict_functor_map_app, ←comp_apply],
        dsimp only, },
      rw [←nat_trans.naturality, comp_apply],
      congr' 1,
      simp only [monoidal.tensor_obj_map, AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
        AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
        AddCommGroup.to_int_linear_map_apply],
      simp only [←comp_apply, ←category_theory.functor.map_comp],
      congr' 1,
      convert_to z = F.val.map (𝟙 _) _,
      rw [F.val.map_id, id_apply], },
    { rw [map_add, hx, hy, map_add] },
  end }

def to_sheafify_once :
  tensor_obj' F (tensor_obj' G H) ⟶
  (presheaf_to_Sheaf _ _).obj (F.val ⊗ G.val ⊗ H.val) :=
uncurry $ ((sheafification_adjunction _ _).hom_equiv _ _).symm $ by exact aux0 F G H

def from_sheafify_once :
  (presheaf_to_Sheaf _ _).obj (F.val ⊗ G.val ⊗ H.val) ⟶
  tensor_obj' F (tensor_obj' G H) :=
(presheaf_to_Sheaf _ _).map $ 𝟙 _ ⊗ to_sheafify _ _

@[simps] def iso_sheafify_once :
  tensor_obj' F (tensor_obj' G H) ≅ (presheaf_to_Sheaf _ _).obj (F.val ⊗ (G.val ⊗ H.val)) :=
{ hom := to_sheafify_once F G H,
  inv := from_sheafify_once F G H,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end associator_left

def associator' (F G H : sheaf AddCommGroup.{u} X) :
  (tensor_obj' (tensor_obj' F G) H) ≅ (tensor_obj' F (tensor_obj' G H)) :=
(associator_right.iso_sheafify_once F G H).trans $
  (presheaf_to_Sheaf_iso (α_ _ _ _)).trans $
    (associator_left.iso_sheafify_once F G H).symm

end constructions

instance : monoidal_category (sheaf AddCommGroup.{u} X) :=
{ tensor_obj := constructions.tensor_obj',
  tensor_hom := λ _ _ _ _, constructions.tensor_hom',
  tensor_unit := constructions.tensor_unit',
  associator := constructions.associator',
  left_unitor := _,
  right_unitor := _,

  tensor_id' := constructions.tensor_id',
  tensor_comp' := λ _ _ _ _ _ _, constructions.tensor_comp',

  associator_naturality' := sorry,
  left_unitor_naturality' := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry }

end Top.sheaf
