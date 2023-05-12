import category_theory.monoidal.internal.functor_category
import algebra.category.Group.monoidal
import algebra.category.Group.limits
import algebra.category.Group.filtered_colimits
import category_theory.functor.equivalence
import category_theory.closed.functor_category
import category_theory.preadditive.functor_category
import topology.sheaves.sheaf
import category_theory.sites.sheafification

noncomputable theory

open category_theory category_theory.monoidal category_theory.limits

namespace Top.presheaf

namespace monoidal


universes w u₁ v₁
variables {C : Type u₁} [category.{v₁} C]

local attribute [instance] AddCommGroup.monoidal.tensor_monoidal_category

@[simps] def Mon_presheaf_Ab_equiv_presheaf_ring :
  Mon_ (Cᵒᵖ ⥤ AddCommGroup.{w}) ≌ (Cᵒᵖ ⥤ Ring.{w}) :=
(Mon_functor_category_equivalence Cᵒᵖ AddCommGroup).trans $
  category_theory.functor.equivalence_of_target_equivalence _ _ _ $
    AddCommGroup.monoidal.Mon_equiv_Ring

end monoidal

section

universe u

variables {X : Top.{u}}

open topological_space Top opposite

@[simps] def emb (U : opens X) : Top.of U ⟶ X :=
{ to_fun := (coe : U → X),
  continuous_to_fun := continuous_subtype_val }

def emb.to_global_subset {U : opens X} (V : opens (Top.of U)) : opens X :=
⟨subtype.val '' V.1, (is_open.open_embedding_subtype_coe U.2).is_open_map _ V.2⟩

def emb.of_subset {U V : opens X} (inc : U ⟶ V) (W : opens (Top.of U)) : opens (Top.of V) :=
{ val := (λ p, ⟨p.1, le_of_hom inc p.2⟩ : U → V) '' W.1,
  property := let ⟨O, hO1, hO2⟩ := is_open_induced_iff.mp W.2 in
    is_open_induced_iff.mpr ⟨subtype.val '' W.1,
    begin
      apply_fun set.image subtype.val at hO2,
      rw ←hO2,
      apply (is_open.open_embedding_subtype_coe U.2).is_open_map,
      apply is_open.preimage,
      continuity,
    end, begin
      ext ⟨x, hx⟩, split,
      { rintros ⟨p, hp1, hp2⟩,
        rw set.mem_image,
        refine ⟨p, hp1, subtype.ext_iff_val.mpr hp2⟩, },
      { rintros ⟨p, hp1, hp2⟩,
        rw [←hp2, set.mem_preimage, set.mem_image],
        refine ⟨p, hp1, rfl⟩, },
    end⟩ }

def emb.of_subset_hom {U V : opens X} (inc : U ⟶ V) {W₁ W₂ : opens (Top.of U)} (i : W₁ ⟶ W₂) :
  emb.of_subset inc W₁ ⟶ emb.of_subset inc W₂ :=
hom_of_le $ λ _ ⟨q, hq1, hq2⟩, ⟨q, le_of_hom i hq1, hq2⟩

def emb.of_subset_id (U : opens X) (W : opens (Top.of U)) :
  emb.of_subset (𝟙 U) W = W :=
begin
  ext x, split,
  { rintros ⟨p, hp, rfl⟩, dsimp, erw opens.mem_coe at hp, convert hp, ext, refl, },
  { intros h, rw opens.mem_coe at h, refine ⟨x, h, _⟩, ext, refl, },
end

def emb.of_subset_comp {U V W : opens X} (iUV : U ⟶ V) (iVW : V ⟶ W) (W : opens (Top.of U)) :
  emb.of_subset (iUV ≫ iVW) W = emb.of_subset iVW (emb.of_subset iUV W) :=
begin
  ext x, split,
  { rintros ⟨p, hp, rfl⟩, exact ⟨⟨p, le_of_hom iUV p.2⟩, ⟨p, hp, rfl⟩, rfl⟩, },
  { rintros ⟨p, ⟨q, hq, rfl⟩, rfl⟩, exact ⟨q, hq, rfl⟩, },
end

lemma emb.open_embedding (U : opens X) : open_embedding (emb U) :=
is_open.open_embedding_subtype_coe U.2

@[simps] def restrict (F : presheaf AddCommGroup.{u} X) (U : opens X) : presheaf AddCommGroup (Top.of U) :=
(emb.open_embedding U).is_open_map.functor.op ⋙ F

@[simps] def restrict_top {F G : presheaf AddCommGroup.{u} X} {U : opens X}
  (α : restrict F U ⟶ restrict G U) : F.obj (op U) ⟶ G.obj (op U) :=
F.map (hom_of_le $ by { rintros _ ⟨x, hx, rfl⟩, exact x.2 } :
  (emb.open_embedding U).is_open_map.functor.obj ⊤ ⟶ U).op ≫ α.app (op ⊤) ≫
  G.map (hom_of_le $ λ x hx, ⟨⟨x, hx⟩, ⟨⟩, rfl⟩ :
    U ⟶ (emb.open_embedding U).is_open_map.functor.obj ⊤).op

@[simps] def restrict_functor (U : opens X) : presheaf AddCommGroup.{u} X ⥤ presheaf AddCommGroup (Top.of U) :=
{ obj := λ F, restrict F U,
  map := λ F G α,
  { app := λ V, α.app _,
    naturality' := λ V W inc,
    begin
      ext x,
      erw [restrict_map, α.naturality, restrict_map, comp_apply],
    end },
  map_id' := λ F,
  begin
    ext U x,
    simp only [nat_trans.id_app, id_apply],
  end,
  map_comp' := λ F G H α β,
  begin
    ext U x,
    simp only [nat_trans.comp_app],
  end }

@[reducible] def restrict_subset_sections (F : presheaf AddCommGroup.{u} X) {U V : opens X} (inc : U ⟶ V)
  (W : opens (Top.of U)) :
  (restrict F U).obj (op W) ≅ (restrict F V).obj (op $ emb.of_subset inc W) :=
{ hom := F.map (quiver.hom.op $ hom_of_le
    begin
      rintros p ⟨⟨q, hq1⟩, ⟨x, hx1, hx2⟩, rfl⟩,
      dsimp only at hx2,
      refine ⟨x, hx1, _⟩,
      rw ←hx2,
      refl,
    end : op ((emb.open_embedding U).is_open_map.functor.obj W) ⟶
      op ((emb.open_embedding V).is_open_map.functor.obj (emb.of_subset inc W))),
  inv := F.map (quiver.hom.op $ hom_of_le
    begin
      rintros p ⟨q, hq, rfl⟩,
      refine ⟨⟨q.1, le_of_hom inc q.2⟩, ⟨q, hq, rfl⟩, rfl⟩,
    end : op ((emb.open_embedding V).is_open_map.functor.obj (emb.of_subset inc W)) ⟶
      op ((emb.open_embedding U).is_open_map.functor.obj W)),
  hom_inv_id' := by { rw [←F.map_comp, ←op_comp], convert F.map_id _ },
  inv_hom_id' := by { rw [←F.map_comp, ←op_comp], convert F.map_id _ } }

@[simps] def restrict_subset_sections_map.app {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V)
  (α : restrict F V ⟶ restrict G V) (W : opens (Top.of U)):
  (restrict F U).obj (op W) ⟶ (restrict G U).obj (op W) :=
{ to_fun := λ s, (restrict_subset_sections G inc W).inv $ α.app _ $
      (restrict_subset_sections F inc W).hom s,
  map_zero' := by rw [map_zero, map_zero, map_zero],
  map_add' := λ x y, by rw [map_add, map_add, map_add] }

lemma restrict_subset_sections_map.naturality {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V)
  (α : restrict F V ⟶ restrict G V)
  (W₁ W₂ : (opens (Top.of U)))
  (i : W₁ ⟶ W₂) :
  (restrict F U).map i.op ≫ restrict_subset_sections_map.app inc α W₁ =
    restrict_subset_sections_map.app inc α W₂ ≫ (restrict G U).map i.op :=
begin
  ext x,
  simp only [restrict_map, quiver.hom.unop_op, restrict_subset_sections_map.app, comp_apply,
    add_monoid_hom.coe_mk],
  simp only [←comp_apply],
  simp only [←comp_apply, ←F.map_comp, ←op_comp],
  generalize_proofs h1 h2 h3 h4 h5 h6,
  rw [show hom_of_le h3 ≫ h1.functor.map i = h2.functor.map (emb.of_subset_hom inc i) ≫
    hom_of_le h5, from rfl, op_comp, F.map_comp, category.assoc _ _ (α.app _)],
  have := α.naturality (emb.of_subset_hom inc i).op,
  dsimp at this,
  erw this,
  simp only [category.assoc],
  congr' 3,
  rw [←G.map_comp, ←G.map_comp, ←op_comp, ←op_comp],
  congr' 1,
end

@[simps] def restrict_subset_sections_map {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V)
  (α : restrict F V ⟶ restrict G V) :
  restrict F U ⟶ restrict G U :=
{ app := λ W, restrict_subset_sections_map.app inc α W.unop,
  naturality' := λ W₁ W₂ i, restrict_subset_sections_map.naturality inc α _ _ i.unop }

instance (F G : presheaf AddCommGroup.{u} X) (U : opens X) :
  add_comm_group (restrict F U ⟶ restrict G U) :=
begin
  haveI i1 : preadditive (presheaf AddCommGroup (Top.of U)) :=
    category_theory.functor_category_preadditive,
  exactI i1.1 (restrict F U) (restrict G U),
end

lemma restrict_top_zero {F G : presheaf AddCommGroup.{u} X} {U : opens X} :
  restrict_top (0 : restrict F U ⟶ restrict G U) = 0 :=
begin
  ext,
  simp only [restrict_top_apply, nat_trans.app_zero, AddCommGroup.monoidal.ihom_obj'_str_zero_apply,
    map_zero],
end

lemma restrict_top_add {F G : presheaf AddCommGroup.{u} X} {U : opens X}
  (α β : restrict F U ⟶ restrict G U) :
  restrict_top (α + β) = restrict_top α + restrict_top β :=
begin
  ext,
  simp only [restrict_top_apply, nat_trans.app_add, AddCommGroup.monoidal.ihom_obj'_str_add_apply,
    map_add],
end

@[simps] def restrict_top_add_monoid_hom (F G : presheaf AddCommGroup.{u} X) (U : opens X) :
  AddCommGroup.of (restrict F U ⟶ restrict G U) ⟶ AddCommGroup.of (F.obj (op U) ⟶ G.obj (op U)) :=
{ to_fun := restrict_top,
  map_zero' := restrict_top_zero,
  map_add' := restrict_top_add }

lemma restrict_subset_sections_map_zero {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V) :
  restrict_subset_sections_map inc (0 : restrict F V ⟶ restrict G V) = 0 :=
by { ext, simp }

lemma restrict_subset_sections_map_add {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V) (α β : restrict F V ⟶ restrict G V) :
  restrict_subset_sections_map inc (α + β) = restrict_subset_sections_map inc α +
  restrict_subset_sections_map inc β :=
by { ext, simp }

lemma restrict_subset_sections_map_id {F G : presheaf AddCommGroup.{u} X} (U : opens X)
  (α : restrict F U ⟶ restrict G U) : restrict_subset_sections_map (𝟙 U) α = α :=
begin
  ext W x,
  simp only [restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply],
  erw [←comp_apply, ←comp_apply, ←α.naturality],
  swap,
  { refine eq_to_hom _,
    rw emb.of_subset_id U W.unop,
    refl, },
  dsimp,
  rw [←category.assoc, ←F.map_comp, ←op_comp],
  congr' 1,
  convert category.id_comp _,
  convert F.map_id _,
end

lemma restrict_subset_sections_map_comp {F G : presheaf AddCommGroup.{u} X} {U V W : opens X}
  (iUV : U ⟶ V) (iVW : V ⟶ W) (α : restrict F W ⟶ restrict G W) :
  restrict_subset_sections_map (iUV ≫ iVW) α =
  restrict_subset_sections_map iUV (restrict_subset_sections_map iVW α) :=
begin
  ext O x,
  simp only [restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply],
  simp only [←comp_apply, category.assoc, ←G.map_comp, ←op_comp],
  rw [←category.assoc _ _ (α.app _ ≫ _), ←F.map_comp, ←op_comp],
  congr' 1,
  change _ = _ ≫ α.app (op (emb.of_subset iVW (emb.of_subset iUV _))) ≫ _,
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8 h9,
  rw [show α.app (op (emb.of_subset iVW (emb.of_subset iUV O.unop))) =
    F.map ((emb.open_embedding W).is_open_map.functor.op.map (eq_to_hom _)) ≫
      α.app (op (emb.of_subset (iUV ≫ iVW) O.unop)) ≫
      G.map ((emb.open_embedding W).is_open_map.functor.op.map (eq_to_hom _)),
    from _, category.assoc, category.assoc, ←G.map_comp, ←category.assoc (F.map _) (F.map _),
    ←F.map_comp],
  congr' 1,
  { rw emb.of_subset_comp, },
  { rw emb.of_subset_comp, },
  { erw [←category.assoc, α.naturality, category.assoc, ←G.map_comp],
    symmetry,
    convert category.comp_id _,
    convert G.map_id _, },
end

namespace monoidal

@[simps] def ihom_obj (F G : presheaf AddCommGroup.{u} X) : presheaf AddCommGroup.{u} X :=
{ obj := λ U, AddCommGroup.of (restrict F U.unop ⟶ restrict G U.unop),
  map := λ U V inc,
  { to_fun := λ α, restrict_subset_sections_map inc.unop α,
    map_zero' := restrict_subset_sections_map_zero inc.unop,
    map_add' := λ α β, restrict_subset_sections_map_add inc.unop α β },
  map_id' := λ U,
  begin
    ext1,
    rw [add_monoid_hom.coe_mk, unop_id, restrict_subset_sections_map_id, id_apply],
  end,
  map_comp' := λ U V W iUV iVW,
  begin
    ext1 α,
    rw [add_monoid_hom.coe_mk, comp_apply, add_monoid_hom.coe_mk, add_monoid_hom.coe_mk],
    convert restrict_subset_sections_map_comp iVW.unop iUV.unop α,
  end }

@[simps] def ihom_map' (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂)
  (U : opens X) (f : restrict F U ⟶ restrict G₁ U) :
  restrict F U ⟶ restrict G₂ U :=
f ≫ (restrict_subset_sections_map (𝟙 U) ((restrict_functor U).map γ))

lemma ihom_map'_zero (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) (U : opens X) :
  ihom_map' F G₁ G₂ γ U 0 = 0 :=
begin
  ext, simp,
end

lemma ihom_map'_add (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) (U : opens X)
  (α β : restrict F U ⟶ restrict G₁ U) :
  ihom_map' F G₁ G₂ γ U (α + β) = ihom_map' F G₁ G₂ γ U α + ihom_map' F _ _ γ U β :=
begin
  ext, simp,
end

lemma ihom_map'_naturality (F G₁ G₂ : presheaf AddCommGroup.{u} X)
  (γ : G₁ ⟶ G₂) (U : opens X) (α : restrict F U ⟶ restrict G₁ U)
  {W₁ W₂ : opens (Top.of U)} (inc : W₁ ⟶ W₂) :
  (restrict F U).map inc.op ≫ (ihom_map' F G₁ G₂ γ U α).app (op W₁) =
  (ihom_map' F G₁ G₂ γ U α).app (op W₂) ≫ (restrict G₂ U).map inc.op :=
begin
  ext x,
  simp only [restrict_map, quiver.hom.unop_op, comp_apply, ihom_map'_app_apply],
  simp only [←comp_apply, category.assoc, ←G₂.map_comp],
  erw [←γ.naturality, ←γ.naturality, ←category.assoc (G₁.map _), ←G₁.map_comp, ←op_comp,
    ←category.assoc (α.app _), ←α.naturality (𝟙 _), ←category.assoc, ←category.assoc,
    ←F.map_comp, ←op_comp, α.naturality inc.op, ←category.assoc (G₁.map _), ←G₁.map_comp,
    ←op_comp, category.assoc],
end

@[simps] def ihom_map_app (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) (U : opens X) :
  (ihom_obj F G₁).obj (op U) ⟶ (ihom_obj F G₂).obj (op U) :=
{ to_fun := λ α,
  { app := λ W, (ihom_map' F G₁ G₂ γ U α).app W,
    naturality' := λ W₁ W₂ inc,
    begin
      convert ihom_map'_naturality F G₁ G₂ γ U α inc.unop,
    end },
  map_zero' :=
  begin
    ext W x,
    simp_rw ihom_map'_zero F G₁ G₂ γ U,
  end,
  map_add' := λ _ _,
  begin
    ext W x,
    simp_rw ihom_map'_add F G₁ G₂ γ U,
    rw [nat_trans.app_add, nat_trans.app_add],
  end }

lemma ihom_map_naturality (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂)
  {U V : opens X} (iUV : U ⟶ V) :
  (ihom_obj F G₁).map iUV.op ≫ ihom_map_app F G₁ G₂ γ U =
  ihom_map_app F G₁ G₂ γ V ≫ (ihom_obj F G₂).map iUV.op :=
begin
  ext f W x,
  simp only [comp_apply, ihom_obj_map_apply, quiver.hom.unop_op, ihom_map_app_apply_app,
    ihom_map'_app_apply, restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply],
  simp only [←comp_apply, category.assoc],
  rw [←γ.naturality, ←category.assoc (G₁.map _), ←G₁.map_comp, ←category.assoc (G₁.map _),
    ←G₁.map_comp, ←op_comp, ←op_comp, ←G₂.map_comp, ←op_comp, ←γ.naturality,
    ←category.assoc (G₁.map _), ←G₁.map_comp, ←op_comp],
  congr' 1,
end

@[simps] def ihom_map (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) :
  ihom_obj F G₁ ⟶ ihom_obj F G₂ :=
{ app := λ U, ihom_map_app F G₁ G₂ γ U.unop,
  naturality' := λ U V iUV, by convert ihom_map_naturality F G₁ G₂ γ iUV.unop }

lemma ihom_map_id (F G : presheaf AddCommGroup.{u} X) :
  ihom_map F G G (𝟙 G) = 𝟙 _ :=
begin
  ext f U W x,
  simp only [ihom_map_app_2, ihom_map_app_apply_app, ihom_map'_app_apply, nat_trans.id_app,
    id_apply],
  simp only [←comp_apply, category.assoc, ←G.map_comp, ←op_comp],
  congr' 1,
  convert category.comp_id _,
  convert G.map_id _,
end

lemma ihom_map_comp (F G₁ G₂ G₃ : presheaf AddCommGroup.{u} X) (g₁₂ : G₁ ⟶ G₂) (g₂₃ : G₂ ⟶ G₃) :
  ihom_map F _ _ (g₁₂ ≫ g₂₃) = ihom_map F _ _ g₁₂ ≫ ihom_map F _ _ g₂₃ :=
begin
  ext f U W x,
  simp only [ihom_map_app_2, ihom_map_app_apply_app, ihom_map'_app_apply, nat_trans.comp_app,
    comp_apply],
  simp only [←comp_apply, category.assoc],
  congr' 3,
  rw [←g₂₃.naturality, ←category.assoc (G₂.map _), ←G₂.map_comp, ←category.assoc (G₂.map _),
    ←G₂.map_comp],
  congr,
end

@[simps] def ihom (F : presheaf AddCommGroup.{u} X) :
  presheaf AddCommGroup.{u} X ⥤ presheaf AddCommGroup.{u} X :=
{ obj := ihom_obj F,
  map := ihom_map F,
  map_id' := ihom_map_id F,
  map_comp' := λ _ _ _, ihom_map_comp F _ _ _ }

local attribute [instance] AddCommGroup.monoidal.tensor_monoidal_category

instance monoidal_presheaf_AddCommGroup : monoidal_category (presheaf AddCommGroup.{u} X) :=
category_theory.monoidal.functor_category_monoidal

open category_theory.monoidal_category

namespace tensor_ihom_adj

@[simps] def hom_equiv'.from_tensor_app_apply (F G₁ G₂ : presheaf AddCommGroup.{u} X)
  (f : F ⊗ G₁ ⟶ G₂) (U : (opens X)ᵒᵖ) (s : G₁.obj U) :
  F.restrict U.unop ⟶ G₂.restrict U.unop :=
{ app := λ W, let O := (emb.open_embedding U.unop).is_open_map.functor.obj W.unop in
    AddCommGroup.monoidal.curry (f.app (op O)) $
      G₁.map ((hom_of_le $ by { rintros _ ⟨p, hp, rfl⟩, exact p.2 }).op : op (unop U) ⟶ op O) s,
  naturality' := λ W₁ W₂ inc,
  begin
    simp only [restrict_map],
    generalize_proofs h1 h2 h3,
    ext t,
    simp only [comp_apply, AddCommGroup.monoidal.curry_apply_apply],
    erw ←fun_like.congr_fun (f.naturality (_ : op (h1.functor.obj (unop W₁)) ⟶
      op (h1.functor.obj (unop W₂)))) (t ⊗ₜ (G₁.map (hom_of_le h3).op) s),
    simp only [tensor_obj_map, AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
      comp_apply, AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
      tensor_product.map_tmul, AddCommGroup.to_int_linear_map_apply],
    congr' 2,
    rw [←comp_apply, ←G₁.map_comp, ←op_comp],
    congr,
  end }

@[simps] def hom_equiv'.from_tensor (F G₁ G₂ : presheaf AddCommGroup.{u} X)
  (f : F ⊗ G₁ ⟶ G₂) : (G₁ ⟶ (ihom F).obj G₂) :=
{ app := λ U,
  { to_fun := hom_equiv'.from_tensor_app_apply F G₁ G₂ f U,
    map_zero' := by { ext W s, simp only [hom_equiv'.from_tensor_app_apply_app, map_zero,
      nat_trans.app_zero], },
    map_add' := λ s t, by { ext W x, simp only [hom_equiv'.from_tensor_app_apply_app, map_add,
      nat_trans.app_add], } },
  naturality' := λ U V inc,
  begin
    ext s W x,
    simp only [hom_equiv'.from_tensor_app_apply_app, comp_apply, add_monoid_hom.coe_mk,
      AddCommGroup.monoidal.curry_apply_apply],
    dsimp only [ihom, ihom_obj],
    simp only [add_monoid_hom.coe_mk, restrict_subset_sections_map_app,
      restrict_subset_sections_map.app_apply, hom_equiv'.from_tensor_app_apply_app,
      AddCommGroup.monoidal.curry_apply_apply],
    erw [←comp_apply, ←G₁.map_comp, ←comp_apply, ←f.naturality],
    simp only [functor.map_comp, comp_apply, tensor_obj_map, tensor_product.map_tmul,
      AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
      AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
      AddCommGroup.to_int_linear_map_apply],
    congr' 2,
    { rw [←comp_apply, ←F.map_comp, ←op_comp],
      symmetry,
      convert id_apply _,
      convert F.map_id _, },
    { simp only [←comp_apply, ←G₁.map_comp],
      congr, },
  end }

@[simps] def hom_equiv'.to_tensor_app_apply {F G₁ G₂ : presheaf AddCommGroup.{u} X}
  (f : G₁ ⟶ (ihom F).obj G₂) (U : (opens X)ᵒᵖ) : (F ⊗ G₁).obj U ⟶ G₂.obj U :=
(tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (F.obj U) (G₁.obj U) (G₂.obj U) $
  AddCommGroup.monoidal.curry $ AddCommGroup.monoidal.uncurry' $ f.app U ≫
    restrict_top_add_monoid_hom F G₂ U.unop).to_add_monoid_hom

lemma hom_equiv'.to_tensor_naturality_tmul
  {F G₁ G₂ : presheaf AddCommGroup.{u} X} (f : G₁ ⟶ (ihom F).obj G₂)
  {U V : (opens X)ᵒᵖ} (inc : U ⟶ V) (a : (F.obj U)) (b : (G₁.obj U)) :
  ((F ⊗ G₁).map inc ≫ hom_equiv'.to_tensor_app_apply f V)
      (a ⊗ₜ[ℤ] b) =
  (hom_equiv'.to_tensor_app_apply f U ≫ G₂.map inc)
    (a ⊗ₜ[ℤ] b) :=
begin
  simp only [comp_apply, tensor_obj_map, AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
    AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
    AddCommGroup.to_int_linear_map_apply, hom_equiv'.to_tensor_app_apply,
    linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
    AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.to_fun_eq_coe,
    AddCommGroup.monoidal.curry_apply_apply, AddCommGroup.monoidal.uncurry'_apply,
    linear_map.coe_mk, restrict_top_add_monoid_hom_apply, restrict_top_apply],
  simp only [←comp_apply, ←category.assoc, ←F.map_comp],
  simp only [category.assoc, ←G₁.map_comp],
  rw [f.naturality, comp_apply (f.app U)],
  dsimp,
  simp only [restrict_subset_sections_map.app_apply, comp_apply],
  simp only [←comp_apply, ←category.assoc, ←F.map_comp],
  simp only [category.assoc, ←G₂.map_comp],
  have eq1 := fun_like.congr_fun (whisker_eq (F.map _)
    (eq_whisker (@nat_trans.naturality _ _ _ _ _ _ (f.app U b)
        (op ⊤) (op (emb.of_subset inc.unop ⊤)) (hom_of_le le_top).op)
      (G₂.map _))) a,
  dsimp at eq1,
  simp only [←category.assoc, ←F.map_comp] at eq1,
  simp only [category.assoc, ←G₂.map_comp] at eq1,
  convert eq1,
end

@[simps] def hom_equiv'.to_tensor (F G₁ G₂ : presheaf AddCommGroup.{u} X)
  (f : G₁ ⟶ (ihom F).obj G₂) : F ⊗ G₁ ⟶ G₂ :=
{ app := hom_equiv'.to_tensor_app_apply f,
  naturality' := λ U V inc,
  begin
    ext x,
    induction x using tensor_product.induction_on with a b a b iha ihb,
    { simp only [map_zero], },
    { apply hom_equiv'.to_tensor_naturality_tmul, },
    { rw [map_add, iha, ihb, map_add], },
  end }

lemma hom_equiv'.left_inv (F G₁ G₂ : presheaf AddCommGroup.{u} X) (f : F ⊗ G₁ ⟶ G₂) :
  (hom_equiv'.to_tensor F G₁ G₂) (hom_equiv'.from_tensor F G₁ G₂ f) = f :=
begin
  ext U x,
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero] },
  { simp only [tensor_product.lift.tmul, linear_map.coe_mk, comp_apply, hom_equiv'.to_tensor_app,
      hom_equiv'.from_tensor_app_apply_2, restrict_top_add_monoid_hom_apply,
      hom_equiv'.to_tensor_app_apply_apply, AddCommGroup.to_int_linear_map₂_apply_apply,
      add_monoid_hom.to_fun_eq_coe, AddCommGroup.monoidal.curry_apply_apply,
      AddCommGroup.monoidal.uncurry'_apply, restrict_top_apply,
      hom_equiv'.from_tensor_app_apply_app],
    simp only [←comp_apply, f.naturality],
    rw [comp_apply],
    generalize_proofs h1 h2 h3,
    apply_fun G₂.map ((hom_of_le _).op : op U.unop ⟶ op (h1.functor.obj ⊤)),
    work_on_goal 3 { rintros _ ⟨x, hx, rfl⟩, exact x.2 },
    work_on_goal 3 { rintros _ ⟨x, hx, rfl⟩, exact x.2 },
    work_on_goal 2
    { rw function.injective_iff_has_left_inverse,
      refine ⟨G₂.map (hom_of_le _).op, _⟩,
      { apply h2, },
      { intros x,
        rw [←comp_apply, ←G₂.map_comp, ←op_comp],
        convert id_apply _,
        convert G₂.map_id _, }, },
    erw [←comp_apply (f.app U), ←fun_like.congr_fun (f.naturality _) (a ⊗ₜ b)],
    simp only [←comp_apply, category.assoc, ←G₂.map_comp],
    rw [show G₂.map (_ ≫ _) = 𝟙 _, from _, category.comp_id],
    work_on_goal 2 { convert G₂.map_id _, },
    simp only [tensor_obj_map, AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
      comp_apply, AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
      tensor_product.map_tmul, AddCommGroup.to_int_linear_map_apply],
    congr, },
  { rw [map_add, ha, hb, map_add] }
end

lemma hom_equiv'.right_inv (F G₁ G₂ : presheaf AddCommGroup.{u} X) (f : G₁ ⟶ (ihom F).obj G₂) :
 hom_equiv'.from_tensor F G₁ G₂ (hom_equiv'.to_tensor F G₁ G₂ f) = f :=
begin
  ext U x W y,
  simp only [tensor_product.lift.tmul, linear_map.coe_mk, comp_apply,
    restrict_top_add_monoid_hom_apply, hom_equiv'.from_tensor_app_apply_2,
    hom_equiv'.from_tensor_app_apply_app, hom_equiv'.to_tensor_app,
    AddCommGroup.monoidal.curry_apply_apply, hom_equiv'.to_tensor_app_apply_apply,
    AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.to_fun_eq_coe,
    AddCommGroup.monoidal.uncurry'_apply, restrict_top_apply],
  rw [←comp_apply (G₁.map _), f.naturality],
  dsimp,
  simp only [comp_apply, ihom_obj_map_apply, quiver.hom.unop_op, restrict_subset_sections_map_app,
    restrict_subset_sections_map.app_apply],
  simp only [←comp_apply, ←F.map_comp],
  simp only [category.assoc, ←G₂.map_comp, ←op_comp],
  erw ←(f.app U x).naturality,
  work_on_goal 2
  { change _ ⟶ op W.unop,
    refine (hom_of_le _).op,
    intros p hp,
    refine ⟨⟨p.1, p, hp, rfl⟩, ⟨⟩, _⟩,
    ext, refl, },
  erw [←category.assoc, ←F.map_comp, id],
  congr' 1,
  convert category.id_comp _,
  convert F.map_id _,
end

@[simps] def hom_equiv' (F G₁ G₂ : presheaf AddCommGroup.{u} X) :
  (F ⊗ G₁ ⟶ G₂) ≃ (G₁ ⟶ (ihom F).obj G₂) :=
{ to_fun := hom_equiv'.from_tensor _ _ _,
  inv_fun := hom_equiv'.to_tensor _ _ _,
  left_inv := hom_equiv'.left_inv _ _ _,
  right_inv := hom_equiv'.right_inv _ _ _ }

@[simps] def unit'_app_sections (F G : presheaf AddCommGroup.{u} X) (U : (opens X)ᵒᵖ) :
  G.obj U ⟶ AddCommGroup.of (restrict F (unop U) ⟶ restrict (F ⊗ G) U.unop) :=
{ to_fun := λ x,
  { app := λ W,
    { to_fun := λ y, y ⊗ₜ G.map
        ((hom_of_le $ by { rintros _ ⟨⟨_, h⟩, -, rfl⟩, exact h, } :
          ((emb.open_embedding U.unop).is_open_map.functor.obj W.unop) ⟶ U.unop).op) x,
      map_zero' := tensor_product.zero_tmul _ _,
      map_add' := λ a b, tensor_product.add_tmul _ _ _ },
    naturality' := λ W₁ W₂ inc,
    begin
      ext y,
      simp only [restrict_map, comp_apply, add_monoid_hom.coe_mk, tensor_obj_map,
        AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
        AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
        AddCommGroup.to_int_linear_map_apply],
      rw [←comp_apply (G.map _), ←G.map_comp, ←op_comp],
      congr,
    end },
  map_zero' :=
  begin
    ext,
    simp only [add_monoid_hom.coe_mk, map_zero, tensor_product.tmul_zero, nat_trans.app_zero,
      AddCommGroup.monoidal.ihom_obj'_str_zero_apply],
  end,
  map_add' := λ a b,
  begin
    ext,
    simpa only [add_monoid_hom.coe_mk, map_add, nat_trans.app_add,
      AddCommGroup.monoidal.ihom_obj'_str_add_apply] using tensor_product.tmul_add _ _ _,
  end }

lemma unit'_app_sections_naturality (F G : presheaf AddCommGroup.{u} X)
  ⦃U V : (opens X)ᵒᵖ⦄ (inc : U ⟶ V) :
  G.map inc ≫ unit'_app_sections F G V =
  unit'_app_sections F G U ≫ ((tensor_left F ⋙ ihom F).obj G).map inc :=
begin
  ext x y z,
  dsimp,
  simp only [comp_apply, unit'_app_sections_apply_app_apply, ihom_obj_map_apply,
    restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply, tensor_obj_map,
    AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
    AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
    AddCommGroup.to_int_linear_map_apply],
  rw [←comp_apply, ←comp_apply, ←F.map_comp, ←comp_apply, ←G.map_comp, ←G.map_comp],
  congr' 1,
  convert_to z = (F.map (𝟙 _)) z,
  rw [F.map_id, id_apply],
end


@[simps] def unit' (F : presheaf AddCommGroup.{u} X) :
  𝟭 (presheaf AddCommGroup.{u} X) ⟶ tensor_left F ⋙ ihom F :=
{ app := λ G,
  { app := λ U, unit'_app_sections F G U, naturality' := unit'_app_sections_naturality F G },
  naturality' := λ G₁ G₂ α,
  begin
    ext U x y z,
    dsimp,
    simp only [functor.id_map, nat_trans.comp_app, comp_apply, unit'_app_sections_apply_app_apply,
      functor.comp_map, tensor_left_map, ihom_map_2, ihom_map_app_2, ihom_map_app_apply_app,
      ihom_map'_app_apply, tensor_hom_app, nat_trans.id_app, tensor_obj_map,
      AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom, tensor_product.map_tmul,
      AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
      AddCommGroup.to_int_linear_map_apply, id_apply],
    simp only [←comp_apply, ←F.map_comp, ←G₁.map_comp],
    rw [α.naturality, category.assoc, ←G₂.map_comp],
    congr' 1,
    convert_to z = (F.map (𝟙 _)) z,
    rw [F.map_id, id_apply],
  end }

@[simps] def counit'_app_sections (F G : presheaf AddCommGroup.{u} X) (U : (opens X)ᵒᵖ) :
  (F ⊗ ihom_obj F G).obj U ⟶ G.obj U :=
(tensor_product.lift $ @AddCommGroup.to_int_linear_map₂ (F.obj U) _ _ $
{ to_fun := λ x,
  { to_fun := λ (α : (ihom_obj F G).obj U), restrict_top α x,
    map_zero' := by rw [restrict_top_zero, add_monoid_hom.zero_apply],
    map_add' := λ α β, by rw [restrict_top_add, add_monoid_hom.add_apply] },
  map_zero' := by { ext, rw [add_monoid_hom.coe_mk, map_zero, add_monoid_hom.zero_apply] },
  map_add' :=  λ _ _, by { ext, simp only [add_monoid_hom.add_apply, add_monoid_hom.coe_mk,
    map_add] } }).to_add_monoid_hom

lemma counit'_app_sections_naturality (F G : presheaf AddCommGroup.{u} X)
  (U V : (opens X)ᵒᵖ) (inc : U ⟶ V) :
  ((ihom F ⋙ tensor_left F).obj G).map inc ≫ counit'_app_sections F G V =
  counit'_app_sections F G U ≫ G.map inc :=
begin
  ext x,
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero] },
  { dsimp,
    simp only [comp_apply, AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
      tensor_product.map_tmul, AddCommGroup.to_int_linear_map_apply, ihom_obj_map_apply,
      counit'_app_sections_apply, tensor_product.lift.tmul,
      AddCommGroup.to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk],
    simp only [←comp_apply, category.assoc, ←G.map_comp],
    simp only [←category.assoc, ←F.map_comp],
    dsimp,
    simp only [comp_apply, restrict_subset_sections_map.app_apply],
    simp only [←comp_apply, category.assoc, ←G.map_comp],
    simp only [←category.assoc, ←F.map_comp],
    simp only [category.assoc],
    generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8,
    have eq1 := fun_like.congr_fun (whisker_eq (F.map _)
      (eq_whisker (@nat_trans.naturality _ _ _ _ _ _ b
          (op ⊤) (op (emb.of_subset inc.unop ⊤)) (hom_of_le le_top).op)
        (G.map _))) a,
    dsimp at eq1,
    simp only [←category.assoc, ←F.map_comp] at eq1,
    simp only [category.assoc, ←G.map_comp] at eq1,
    convert eq1, },
  { simp only [map_add, ha, hb] }
end

@[simps] def counit' (F : presheaf AddCommGroup.{u} X) :
  ihom F ⋙ tensor_left F ⟶ 𝟭 (presheaf AddCommGroup.{u} X) :=
{ app := λ G,
  { app := counit'_app_sections F G, naturality' := counit'_app_sections_naturality F G },
  naturality' := λ G₁ G₂ α,
  begin
    ext U s,
    induction s using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero] },
    { simp only [functor.comp_map, ihom_map_2, tensor_left_map, nat_trans.comp_app, tensor_hom_app,
        nat_trans.id_app, ihom_map_app_2, AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom,
        comp_apply, AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
        tensor_product.map_tmul, AddCommGroup.to_int_linear_map_apply, id_apply,
        counit'_app_sections_apply, tensor_product.lift.tmul, add_monoid_hom.coe_mk,
        AddCommGroup.to_int_linear_map₂_apply_apply, functor.id_map],
      rw [ihom_map_app_apply_app, ihom_map'_app_apply],
      simp only [←comp_apply, category.assoc, ←G₂.map_comp],
      rw [←α.naturality, ←category.assoc (G₁.map _), ←G₁.map_comp],
      congr },
    { simp only [map_add, ha, hb] }
  end }

lemma hom_equiv_unit (F G₁ G₂ : presheaf AddCommGroup.{u} X) (α : (tensor_left F).obj G₁ ⟶ G₂) :
  (tensor_ihom_adj.hom_equiv' F G₁ G₂) α = (tensor_ihom_adj.unit' F).app G₁ ≫ (ihom F).map α :=
begin
  ext U x y z,
  dsimp,
  simp only [comp_apply, ihom_map_app_apply_app, ihom_map'_app_apply, tensor_obj_map,
    AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom, unit'_app_sections_apply_app_apply,
    AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
    AddCommGroup.to_int_linear_map_apply],
  simp only [←comp_apply],
  rw [←α.naturality],
  dsimp,
  simp only [comp_apply, AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply,
    tensor_product.map_tmul, AddCommGroup.to_int_linear_map_apply],
  congr' 2,
  { rw [←comp_apply, ←F.map_comp],
    convert_to z = F.map (𝟙 _) z,
    rw [F.map_id, id_apply], },
  { rw [←comp_apply, ←comp_apply, ←G₁.map_comp, ←G₁.map_comp],
    congr },
end

lemma hom_equiv_counit (F G₁ G₂ : presheaf AddCommGroup.{u} X) (α : G₁ ⟶ (ihom F).obj G₂) :
  ((tensor_ihom_adj.hom_equiv' F G₁ G₂).symm) α =
  (tensor_left F).map α ≫ (tensor_ihom_adj.counit' F).app G₂ :=
begin
  ext U x,
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero] },
  { simp only [hom_equiv'_symm_apply, hom_equiv'.to_tensor_app,
      hom_equiv'.to_tensor_app_apply_apply, tensor_product.lift.tmul,
      AddCommGroup.to_int_linear_map₂_apply_apply, tensor_hom_app,
      add_monoid_hom.to_fun_eq_coe, AddCommGroup.monoidal.curry_apply_apply,
      AddCommGroup.monoidal.uncurry'_apply, linear_map.coe_mk, nat_trans.comp_app,
      comp_apply, restrict_top_add_monoid_hom_apply, restrict_top_apply, tensor_left_map],
    simp only [counit'_app_app, nat_trans.id_app, tensor_product.map_tmul,
      AddCommGroup.monoidal.tensor_monoidal_category_tensor_hom, counit'_app_sections_apply,
      AddCommGroup.monoidal.tensor_monoidal_category.tensor_hom'_apply, add_monoid_hom.coe_mk,
      AddCommGroup.to_int_linear_map_apply, id_apply, tensor_product.lift.tmul,
      AddCommGroup.to_int_linear_map₂_apply_apply], },
  { rw [map_add, ha, hb, map_add] },
end

end tensor_ihom_adj

@[simps] def tensor_ihom_adj (F : presheaf AddCommGroup.{u} X) : tensor_left F ⊣ ihom F :=
{ hom_equiv := tensor_ihom_adj.hom_equiv' _,
  unit := tensor_ihom_adj.unit' _,
  counit := tensor_ihom_adj.counit' _,
  hom_equiv_unit' := tensor_ihom_adj.hom_equiv_unit _,
  hom_equiv_counit' := tensor_ihom_adj.hom_equiv_counit _ }

def monoidal_closed_presheaf_AddCommGroup : monoidal_closed (presheaf AddCommGroup.{u} X) :=
{ closed' := λ F, { is_adj :=
  ⟨ihom F, tensor_ihom_adj F⟩ } }

end monoidal

namespace presheaf_of_module

open Top topological_space

local attribute [instance] monoidal.monoidal_closed_presheaf_AddCommGroup
local attribute [instance] monoidal.monoidal_presheaf_AddCommGroup

variables (R : Mon_ (presheaf AddCommGroup.{u} X)) (M : Mod R)

instance Mon_sections_ring (U : (opens X)ᵒᵖ) : ring (R.X.obj U) :=
((monoidal.Mon_presheaf_Ab_equiv_presheaf_ring.functor.obj R).obj U).str

instance has_smul_Mon_sections_Mod_sections (U : (opens X)ᵒᵖ) : has_smul (R.X.obj U) (M.X.obj U) :=
{ smul := λ r x, M.act.app U (r ⊗ₜ x) }

instance mul_action_Mon_sections_Mod_sections (U : (opens X)ᵒᵖ) :
  mul_action (R.X.obj U) (M.X.obj U) :=
{ one_smul := λ x,
  begin
    convert fun_like.congr_fun (nat_trans.congr_app M.one_act U) ((ulift.up 1 : ulift ℤ) ⊗ₜ x),
    simp only [left_unitor_hom_app, AddCommGroup.monoidal.tensor_monoidal_category_left_unitor,
      AddCommGroup.monoidal.tensor_monoidal_category.left_unitor'_hom_apply,
      tensor_product.lift.tmul, linear_map.coe_mk, one_zsmul],
  end,
  mul_smul := λ r s x, fun_like.congr_fun (nat_trans.congr_app M.assoc U) ((r ⊗ₜ s) ⊗ₜ x),
  ..presheaf_of_module.has_smul_Mon_sections_Mod_sections R M U }

instance distrib_mul_action_Mon_sections_Mod_sections (U : (opens X)ᵒᵖ) :
  distrib_mul_action (R.X.obj U) (M.X.obj U) :=
{ smul_zero := λ r, show M.act.app U _ = _, by rw [tensor_product.tmul_zero, map_zero],
  smul_add := λ r x y, show M.act.app U _ = M.act.app U _ + M.act.app U _,
    by rw [tensor_product.tmul_add, map_add],
  ..presheaf_of_module.mul_action_Mon_sections_Mod_sections R M U }

instance module_Mon_sections_Mod_sections (U : (opens X)ᵒᵖ) : module (R.X.obj U) (M.X.obj U) :=
{ add_smul := λ r s x, show M.act.app U _ = M.act.app U _ + M.act.app U _,
    by rw [tensor_product.add_tmul, map_add],
  zero_smul := λ x, show M.act.app U _ = 0, by rw [tensor_product.zero_tmul, map_zero],
  ..presheaf_of_module.distrib_mul_action_Mon_sections_Mod_sections R M U }

lemma sections_smul_restriction {U V : (opens X)ᵒᵖ} (inc : U ⟶ V) (r : R.X.obj U) (m : M.X.obj U) :
  M.X.map inc (r • m) = R.X.map inc r • M.X.map inc m :=
eq.symm $ fun_like.congr_fun (M.act.naturality inc) $ r ⊗ₜ m

@[simps] def forget_to_presheaf_AddCommGroup : Mod R ⥤ presheaf AddCommGroup X :=
{ obj := Mod.X,
  map := λ _ _ f, f.hom,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

structure sheaf_of_module (R : Mon_ (presheaf AddCommGroup.{u} X)) :=
(val : Mod R)
(cond : is_sheaf val.X)

end presheaf_of_module

end

end Top.presheaf
