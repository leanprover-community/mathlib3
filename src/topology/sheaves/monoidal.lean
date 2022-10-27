import category_theory.monoidal.internal.functor_category
import algebra.category.Group.monoidal
import category_theory.functor.equivalence
import category_theory.sites.sheafification
import category_theory.closed.functor_category
import category_theory.preadditive.functor_category
import topology.sheaves.presheaf

noncomputable theory

open category_theory category_theory.monoidal category_theory.limits

section Ab

namespace presheaf

namespace monoidal

section

universes w u₁ v₁
variables {C : Type u₁} [category.{v₁} C]


local attribute [instance] AddCommGroup.monoidal.tensor_monoidal_category

@[simps] def Mon_presheaf_Ab_equiv_presheaf_ring :
  Mon_ (Cᵒᵖ ⥤ AddCommGroup.{w}) ≌ (Cᵒᵖ ⥤ Ring.{w}) :=
(Mon_functor_category_equivalence Cᵒᵖ AddCommGroup).trans $
  category_theory.functor.equivalence_of_target_equivalence _ _ _ $
    AddCommGroup.monoidal.Mon_equiv_Ring

end

section

universes u v

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

@[simps] def restrict (F : presheaf AddCommGroup X) (U : opens X) : presheaf AddCommGroup (Top.of U) :=
(emb.open_embedding U).is_open_map.functor.op ⋙ F

@[simps] def restrict_functor (U : opens X) : presheaf AddCommGroup X ⥤ presheaf AddCommGroup (Top.of U) :=
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

@[reducible] def restrict_subset_sections (F : presheaf AddCommGroup X) {U V : opens X} (inc : U ⟶ V)
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

@[simps] def restrict_subset_sections_map.app {F G : presheaf AddCommGroup X}
  {U V : opens X} (inc : U ⟶ V)
  (α : restrict F V ⟶ restrict G V) (W : opens (Top.of U)):
  (restrict F U).obj (op W) ⟶ (restrict G U).obj (op W) :=
{ to_fun := λ s, (restrict_subset_sections G inc W).inv $ α.app _ $
      (restrict_subset_sections F inc W).hom s,
  map_zero' := by rw [map_zero, map_zero, map_zero],
  map_add' := λ x y, by rw [map_add, map_add, map_add] }

lemma restrict_subset_sections_map.naturality {F G : presheaf AddCommGroup X}
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

@[simps] def restrict_subset_sections_map {F G : presheaf AddCommGroup X}
  {U V : opens X} (inc : U ⟶ V)
  (α : restrict F V ⟶ restrict G V) :
  restrict F U ⟶ restrict G U :=
{ app := λ W, restrict_subset_sections_map.app inc α W.unop,
  naturality' := λ W₁ W₂ i, restrict_subset_sections_map.naturality inc α _ _ i.unop }

instance (F G : presheaf AddCommGroup X) (U : opens X) :
  add_comm_group (restrict F U ⟶ restrict G U) :=
begin
  haveI i1 : preadditive (presheaf AddCommGroup (Top.of U)) :=
    category_theory.functor_category_preadditive,
  exactI i1.1 (restrict F U) (restrict G U),
end

lemma restrict_subset_sections_map_zero {F G : presheaf AddCommGroup X}
  {U V : opens X} (inc : U ⟶ V) :
  restrict_subset_sections_map inc (0 : restrict F V ⟶ restrict G V) = 0 :=
by { ext, simp }

lemma restrict_subset_sections_map_add {F G : presheaf AddCommGroup X}
  {U V : opens X} (inc : U ⟶ V) (α β : restrict F V ⟶ restrict G V) :
  restrict_subset_sections_map inc (α + β) = restrict_subset_sections_map inc α +
  restrict_subset_sections_map inc β :=
by { ext, simp }

lemma restrict_subset_sections_map_id {F G : presheaf AddCommGroup X} (U : opens X)
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

lemma restrict_subset_sections_map_comp {F G : presheaf AddCommGroup X} {U V W : opens X}
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

@[simps] def ihom_obj (F G : presheaf AddCommGroup X) : presheaf AddCommGroup X :=
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

@[simps] def ihom_map' (F G₁ G₂ : presheaf AddCommGroup X) (γ : G₁ ⟶ G₂)
  (U : opens X) (f : restrict F U ⟶ restrict G₁ U) :
  restrict F U ⟶ restrict G₂ U :=
f ≫ (restrict_subset_sections_map (𝟙 U) ((restrict_functor U).map γ))

lemma ihom_map'_zero (F G₁ G₂ : presheaf AddCommGroup X) (γ : G₁ ⟶ G₂) (U : opens X) :
  ihom_map' F G₁ G₂ γ U 0 = 0 :=
begin
  ext, simp,
end

lemma ihom_map'_add (F G₁ G₂ : presheaf AddCommGroup X) (γ : G₁ ⟶ G₂) (U : opens X)
  (α β : restrict F U ⟶ restrict G₁ U) :
  ihom_map' F G₁ G₂ γ U (α + β) = ihom_map' F G₁ G₂ γ U α + ihom_map' F _ _ γ U β :=
begin
  ext, simp,
end

lemma ihom_map'_naturality (F G₁ G₂ : presheaf AddCommGroup X)
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

@[simps] def ihom_map_app (F G₁ G₂ : presheaf AddCommGroup X) (γ : G₁ ⟶ G₂) (U : opens X) :
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

lemma ihom_map_naturality (F G₁ G₂ : presheaf AddCommGroup X) (γ : G₁ ⟶ G₂)
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

@[simps] def ihom_map (F G₁ G₂ : presheaf AddCommGroup X) (γ : G₁ ⟶ G₂) :
  ihom_obj F G₁ ⟶ ihom_obj F G₂ :=
{ app := λ U, ihom_map_app F G₁ G₂ γ U.unop,
  naturality' := λ U V iUV, by convert ihom_map_naturality F G₁ G₂ γ iUV.unop }

lemma ihom_map_id (F G : presheaf AddCommGroup X) :
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

lemma ihom_map_comp (F G₁ G₂ G₃ : presheaf AddCommGroup X) (g₁₂ : G₁ ⟶ G₂) (g₂₃ : G₂ ⟶ G₃) :
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

@[simps] def ihom (F : presheaf AddCommGroup X) :
  presheaf AddCommGroup X ⥤ presheaf AddCommGroup X :=
{ obj := ihom_obj F,
  map := ihom_map F,
  map_id' := ihom_map_id F,
  map_comp' := λ _ _ _, ihom_map_comp F _ _ _ }

local attribute [instance] AddCommGroup.monoidal.tensor_monoidal_category

instance : monoidal_category (presheaf AddCommGroup X) :=
category_theory.monoidal.functor_category_monoidal

open category_theory.monoidal_category

@[simps] def tensor_ihom_adj (F : presheaf AddCommGroup X) : tensor_left F ⊣ ihom F :=
{ hom_equiv := λ G₁ G₂, _,
  unit := _,
  counit := _,
  hom_equiv_unit' := _,
  hom_equiv_counit' := _ }

instance : monoidal_closed (presheaf AddCommGroup X) :=
{ closed' := λ F, { is_adj :=
  ⟨ihom F, _⟩ } }

end

end monoidal


end presheaf

end Ab

#exit

namespace Sheaf

section AddCommGroup


end AddCommGroup

-- need sheafification
universes w v u
variables {C : Type u} [category.{v} C] {J : grothendieck_topology C}
variables {D : Type w} [category.{max v u} D]

def iso.mk (X Y : Sheaf J D) (α : X.val ≅ Y.val) : X ≅ Y :=
{ hom := ⟨α.hom⟩,
  inv := ⟨α.inv⟩,
  hom_inv_id' := Sheaf.hom.ext _ _ α.hom_inv_id',
  inv_hom_id' := Sheaf.hom.ext _ _ α.inv_hom_id' }

variables
  [monoidal_category D] [monoidal_closed D]

namespace ihom

open category_theory.functor

def ihom_obj'_val (X Y : Sheaf J D) : Cᵒᵖ ⥤ D :=
{ obj := λ c, begin
    haveI : monoidal_closed (Cᵒᵖ ⥤ D),
    have := @category_theory.functor.monoidal_closed D Cᵒᵖ,
  end,
  map := _,
  map_id' := _,
  map_comp' := _ }

end ihom

variables
  [concrete_category.{max v u} D]
  [preserves_limits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
  [reflects_isomorphisms (forget D)]


namespace monoidal

@[simps] def tensor_obj' (X Y : Sheaf J D) : Sheaf J D :=
(presheaf_to_Sheaf J D).obj (X.val ⊗ Y.val : Cᵒᵖ ⥤ D)

@[simps] def tensor_hom' {X X' Y Y' : Sheaf J D} (f : X ⟶ X') (g : Y ⟶ Y') :
  tensor_obj' X Y ⟶ tensor_obj' X' Y' :=
(presheaf_to_Sheaf J D).map (f.val ⊗ g.val)

@[simps] def tensor_unit' : Sheaf J D :=
(presheaf_to_Sheaf J D).obj
{ obj := λ c, 𝟙_ D,
  map := λ a b f, 𝟙 _,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, (category.comp_id _).symm }

instance : monoidal_category (Sheaf J D) :=
{ -- data
  tensor_obj := tensor_obj',
  tensor_hom := λ _ _ _ _, tensor_hom',
  tensor_unit := tensor_unit',
  associator := _,
  left_unitor := _,
  right_unitor := _,


  tensor_id' := _,
  tensor_comp' := _,

  associator_naturality' := _,

  left_unitor_naturality' := _,
  right_unitor_naturality' := _,

  pentagon' := _,
  triangle' := _ }

end monoidal

end Sheaf
