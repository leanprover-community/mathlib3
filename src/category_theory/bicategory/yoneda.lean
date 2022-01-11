-- /-
-- Copyright (c) 2021 Yuma Mizuno. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Yuma Mizuno
-- -/
-- import category_theory.bicategory.equivalence
-- import category_theory.bicategory.opposites
-- import category_theory.bicategory.natural_transformation
-- import category_theory.category.Cat

-- open opposite

-- namespace category_theory

-- universes w v u

-- open bicategory category
-- open_locale bicategory

-- namespace bicategory

-- section

-- variables {B : Type u} [bicategory.{w v} B] (a b c d : B)

-- /--
-- Left composition of 1-morphisms as a functor.
-- -/
-- @[simps]
-- def lcomp : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c) :=
-- { obj := λ f,
--   { obj := λ g, f ≫ g,
--     map := λ g h η, f ◁ η },
--   map := λ f g η, { app := λ h, η ▷ h } }

-- -- @[simp]
-- -- lemma lcomp_obj (f : a ⟶ b) :
-- --   (lcomp a b c).obj f =
-- --   { obj := λ g, f ≫ g,
-- --     map := λ g h η, f ◁ η } := rfl

-- /--
-- Right composition of 1-morphisms as a functor.
-- -/
-- @[simps]
-- def rcomp : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) :=
-- { obj := λ f,
--   { obj := λ g, g ≫ f,
--     map := λ g h η, η ▷ f },
--   map := λ f g η, { app := λ h, h ◁ η } }

-- variables {a b c d}

-- /--
-- Left component of an associator as a natural isomorphism.
-- -/
-- @[simps]
-- def associator_nat_iso_left (a) (g : b ⟶ c) (h : c ⟶ d) :
--   (rcomp a _ _).obj g ⋙ (rcomp a _ _).obj h
--   ≅ (rcomp a _ _).obj (g ≫ h) :=
-- nat_iso.of_components
--   (λ f, α_ f g h)
--   (by { intros, apply associator_naturality_left })

-- /--
-- Middle component of an associator as a natural isomorphism.
-- -/
-- @[simps]
-- def associator_nat_iso_middle (f : a ⟶ b) (h : c ⟶ d) :
--   (lcomp _ _ _).obj f ⋙ (rcomp _ _ _).obj h
--   ≅ (rcomp _ _ _).obj h ⋙ (lcomp _ _ _).obj f :=
-- nat_iso.of_components
--   (λ g, α_ f g h)
--   (by { intros, apply associator_naturality_middle })

-- /--
-- Right component of an associator as a natural isomorphism.
-- -/
-- @[simps]
-- def associator_nat_iso_right (d) (f : a ⟶ b) (g : b ⟶ c) :
--   (lcomp _ _ d).obj (f ≫ g)
--   ≅ (lcomp _ _ d).obj g ⋙ (lcomp _ _ d).obj f :=
-- nat_iso.of_components
--   (λ h, α_ f g h)
--   (by { intros, apply associator_naturality_right })

-- /--
-- Left unitor as a natural isomorphism.
-- -/
-- @[simps]
-- def left_unitor_nat_iso (a b : B) : (lcomp _ _ b).obj (𝟙 a) ≅ 𝟭 (a ⟶ b) :=
-- nat_iso.of_components
--   (λ f, λ_ f)
--   (by { intros, apply left_unitor_naturality })

-- /--
-- Right unitor as a natural isomorphism.
-- -/
-- @[simps]
-- def right_unitor_nat_iso (a b : B) : (rcomp a _ _).obj (𝟙 b) ≅ 𝟭 (a ⟶ b) :=
-- nat_iso.of_components
--   (λ f, ρ_ f)
--   (by { intros, apply right_unitor_naturality })

-- end

-- end bicategory

-- section

-- open bicategory

-- variables {B : Type u} [bicategory.{w v} B]

-- -- local attribute [simp] Cat.bicategory

-- namespace oplax_functor

-- /--
-- The Yoneda embedding at the level of objects.
-- -/
-- @[simps]
-- def yoneda_obj (a : B) : oplax_functor Bᵒᵖ Cat :=
-- { obj := λ s, Cat.of (unop s ⟶ a),
--   map := λ s t f, (lcomp (unop t) (unop s) a).obj f,
--   map₂ := λ s t f g β, (lcomp (unop t) (unop s) a).map β,
--   map_id   := λ s, (left_unitor_nat_iso (unop s) a).hom,
--   map_comp := λ s t r (p : unop t ⟶ unop s) (q : unop r ⟶ unop t), (associator_nat_iso_right a q p).hom,
--   map_comp_naturality_left'  := by { intros, ext, apply associator_naturality_middle },
--   map_comp_naturality_right' := by { intros, ext, apply associator_naturality_left },
--   map₂_id'    := by { intros, ext, apply bicategory.whisker_right_id },
--   map₂_comp'  := by { intros, ext, apply bicategory.whisker_right_comp },
--   map₂_associator'  := by { intros, dsimp, ext, dsimp,
--     simp only [iso.refl_hom, strict.associator_eq_to_iso, nat_trans.id_app, eq_to_iso_refl],
--     erw comp_id, rw pentagon_inv_hom_hom_hom_hom },
--   map₂_left_unitor'   := by { intros, ext, dsimp,
--     simp only [iso.refl_hom, strict.left_unitor_eq_to_iso, triangle_assoc, nat_trans.id_app, eq_to_iso_refl],
--     erw comp_id },
--   map₂_right_unitor'  := by { intros, ext, dsimp,
--     simp only [iso.refl_hom, left_unitor_comp, strict.right_unitor_eq_to_iso, iso.hom_inv_id_assoc, nat_trans.id_app, assoc,
--   eq_to_iso_refl],
--   dsimp,
--   simp only [comp_id],
--   erw Cat.comp_obj,
--   dsimp only [Cat.bicategory],
--   dsimp,
--   rw comp_id } }

-- /--
-- The Yoneda embedding at the level of 1-morphisms.
-- -/
-- @[simps]
-- def yoneda_map {a b : B} (f : a ⟶ b) : (yoneda_obj a) ⟶ (yoneda_obj b) :=
-- { app := λ s, (rcomp (unop s) a b).obj f,
--   naturality := λ (s t : Bᵒᵖ) (p : unop t ⟶ unop s), (associator_nat_iso_middle p f).hom,
--   naturality_naturality' := by { intros, ext, apply associator_naturality_left },
--   naturality_id' := by { intros, ext, dsimp, simp only [left_unitor_comp, iso.hom_inv_id_assoc, comp_id] },
--   naturality_comp' := by { intros, ext, dsimp,
--     simp only [iso.refl_hom, strict.associator_eq_to_iso, iso.refl_inv, nat_trans.id_app, eq_to_iso_refl],
--     dsimp, simp only [id_comp, comp_id],
--     erw id_comp, rw pentagon } }

-- /--
-- The Yoneda embedding at the level of 2-morphisms.
-- -/
-- @[simps]
-- def yoneda_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
--   (yoneda_map f) ⟶ (yoneda_map g) :=
-- { app := λ s,
--   { app := λ h : unop s ⟶ a, h ◁ η,
--     naturality' := by { intros, dsimp, rw whisker_exchange } },
--   naturality' := by { intros, ext, dsimp, apply associator_naturality_right } }

-- @[simps]
-- def yoneda_map_id_aux (a : B) : yoneda_map (𝟙 a) ⟶ 𝟙 (yoneda_obj a) :=
-- oplax_nat_trans.modification.mk
--   (λ s : Bᵒᵖ, (right_unitor_nat_iso (unop s) a).hom)
--   (by { dsimp, intros, ext, dsimp, simp only [right_unitor_comp, comp_id] })

-- @[simps]
-- def yoneda_map_comp_aux (a b c : B) (f : a ⟶ b) (g : b ⟶ c) :
--   yoneda_map (f ≫ g) ⟶ yoneda_map f ≫ yoneda_map g :=
-- oplax_nat_trans.modification.mk
--   (λ s : Bᵒᵖ, (associator_nat_iso_left (unop s) f g).inv)
--   (by { dsimp, intros, ext, dsimp, simp only [id_comp, comp_id], erw pentagon_inv_hom_hom_hom_inv })

-- /--
-- The Yoneda embedding as an oplax functor from `B` into 2-presheaves on `B`.
-- -/
-- @[simps]
-- def yoneda : oplax_functor B (oplax_functor Bᵒᵖ Cat) :=
-- { obj := yoneda_obj,
--   map := λ _ _, yoneda_map,
--   map₂ := λ _ _ _ _, yoneda_map₂,
--   map_id := yoneda_map_id_aux,
--   map_comp := yoneda_map_comp_aux,
--   map_comp_naturality_left'  := by { intros, ext, dsimp, apply associator_inv_naturality_middle },
--   map_comp_naturality_right' := by { intros, ext, dsimp, apply associator_inv_naturality_right },
--   map₂_id'    := by { intros, ext, dsimp, apply bicategory.whisker_left_id },
--   map₂_comp'  := by { intros, ext, dsimp, apply bicategory.whisker_left_comp },
--   map₂_associator'  := by { intros, ext, dsimp, simp only [pentagon_hom_inv_inv_inv_inv, comp_id] },
--   map₂_left_unitor'   := by { intros, ext, dsimp, simp only [triangle_assoc_comp_right, comp_id] },
--   map₂_right_unitor'  := by { intros, ext, dsimp, simp only [right_unitor_comp, iso.inv_hom_id_assoc, comp_id] } }

-- end oplax_functor

-- namespace pseudofunctor

-- /--
-- The Yoneda embedding at the level of objects.
-- -/
-- @[simps]
-- def yoneda_obj (a : B) : pseudofunctor Bᵒᵖ Cat :=
-- { obj := λ s, Cat.of (unop s ⟶ a),
--   map := λ s t f, (lcomp (unop t) (unop s) a).obj f,
--   map₂ := λ s t f g β, (lcomp (unop t) (unop s) a).map β,
--   map_id   := λ s, (left_unitor_nat_iso (unop s) a).hom,
--   map_id_iso   := λ s, (left_unitor_nat_iso (unop s) a),
--   map_comp := λ s t r (p : unop t ⟶ unop s) (q : unop r ⟶ unop t), (associator_nat_iso_right a q p).hom,
--   map_comp_iso := λ s t r p q, (associator_nat_iso_right a q p),
--   map_comp_naturality_left'  := by { intros, ext, apply associator_naturality_middle },
--   map_comp_naturality_right' := by { intros, ext, apply associator_naturality_left },
--   map₂_id'    := by { intros, ext, apply bicategory.whisker_right_id },
--   map₂_comp'  := by { intros, ext, apply bicategory.whisker_right_comp },
--   map₂_associator'  := by { intros, ext, dsimp, simp only [pentagon_inv_hom_hom_hom_hom, comp_id] },
--   map₂_left_unitor'   := by { intros, ext, dsimp, simp only [triangle_assoc, comp_id] },
--   map₂_right_unitor'  := by { intros, ext, dsimp, simp only [left_unitor_comp, iso.hom_inv_id_assoc, comp_id] } }

-- /--
-- The Yoneda embedding at the level of 1-morphisms.
-- -/
-- @[simps]
-- def yoneda_map {a b : B} (f : a ⟶ b) : (yoneda_obj a) ⟶ (yoneda_obj b) :=
-- { app := λ s, (rcomp (unop s) a b).obj f,
--   naturality := λ (s t : Bᵒᵖ) (p : unop t ⟶ unop s), (associator_nat_iso_middle p f).hom,
--   naturality_iso := λ (s t : Bᵒᵖ) (p : unop t ⟶ unop s), associator_nat_iso_middle p f,
--   naturality_naturality' := by { intros, ext, apply associator_naturality_left },
--   naturality_id' := by { intros, ext, dsimp, simp only [left_unitor_comp, iso.hom_inv_id_assoc, comp_id] },
--   naturality_comp' := by { intros, ext, dsimp, simp only [id_comp, comp_id, pentagon] } }

-- /--
-- The Yoneda embedding at the level of 2-morphisms.
-- -/
-- @[simps]
-- def yoneda_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
--   (yoneda_map f) ⟶ (yoneda_map g) :=
-- { app := λ s,
--   { app := λ h : unop s ⟶ a, h ◁ η,
--     naturality' := by { intros, dsimp, rw whisker_exchange } },
--   naturality' := by { intros, ext, dsimp, apply associator_naturality_right } }

-- @[simps]
-- def yoneda_map_id_aux (a : B) : yoneda_map (𝟙 a) ≅ (𝟙 (yoneda_obj a)) :=
-- pseudonat_trans.modification_iso.of_components
--   (λ s : Bᵒᵖ, (right_unitor_nat_iso (unop s) a))
--   (by { intros, ext, dsimp, simp only [right_unitor_comp, comp_id] })


-- @[simps]
-- def yoneda_map_comp_aux (a b c : B) (f : a ⟶ b) (g : b ⟶ c) :
--   yoneda_map (f ≫ g) ≅ yoneda_map f ≫ yoneda_map g :=
-- pseudonat_trans.modification_iso.of_components
--   (λ s : Bᵒᵖ, (associator_nat_iso_left (unop s) f g).symm)
--   (by { dsimp, intros, ext, dsimp, simp only [pentagon_inv_hom_hom_hom_inv, id_comp, comp_id] })

-- /--
-- The Yoneda embedding as a pseudofunctor from `B` into 2-presheaves on `B`.
-- -/
-- @[simps]
-- def yoneda : pseudofunctor B (pseudofunctor Bᵒᵖ Cat) :=
-- { obj := yoneda_obj,
--   map := λ _ _, yoneda_map,
--   map₂ := λ _ _ _ _, yoneda_map₂,
--   map_id_iso := yoneda_map_id_aux,
--   map_id := λ a, (yoneda_map_id_aux a).hom,
--   map_comp_iso := yoneda_map_comp_aux,
--   map_comp := λ (a b c : B) (f : a ⟶ b) (g : b ⟶ c), (yoneda_map_comp_aux a b c f g).hom,
--   map_comp_naturality_left'  := by { intros, ext, dsimp, apply associator_inv_naturality_middle },
--   map_comp_naturality_right' := by { intros, ext, dsimp, apply associator_inv_naturality_right },
--   map₂_id'    := by { intros, ext, dsimp, apply bicategory.whisker_left_id },
--   map₂_comp'  := by { intros, ext, dsimp, apply bicategory.whisker_left_comp },
--   map₂_associator'  := by { intros, ext, dsimp, simp only [pentagon_hom_inv_inv_inv_inv, comp_id], },
--   map₂_left_unitor'   := by { intros, ext, dsimp, simp only [triangle_assoc_comp_right, comp_id]},
--   map₂_right_unitor'  := by { intros, ext, dsimp, simp only [right_unitor_comp, iso.inv_hom_id_assoc, comp_id] } }

-- end pseudofunctor

-- end

-- section
-- open bicategory pseudofunctor


-- variables
-- universes u₁ u₂ u₃

-- variables {B : Type u} [bicategory.{u u} B] {F : pseudofunctor Bᵒᵖ Cat.{u u}}

-- set_option pp.universes false

-- variables (a : Bᵒᵖ)

-- @[simps]
-- def yoneda_lemma_hom_app_aux (a : Bᵒᵖ) :
--   ((yoneda.op.comp (yoneda_obj F)).obj a) ⟶ (F.obj a) :=
-- { obj := λ σ, (σ.app a).obj (𝟙 (unop a)),
--   map := λ σ τ Γ, (Γ.app a).app (𝟙 (unop a)),
--   map_id' := by { intros, refl },
--   map_comp' := by { intros, refl } }

-- @[simps]
-- def yoneda_lemma_hom_naturality_aux (a b : Bᵒᵖ)
--   (f : a ⟶ b) :
--   (yoneda.op.comp (yoneda_obj F)).to_oplax_functor.map f ≫ yoneda_lemma_hom_app_aux b ≅
--     yoneda_lemma_hom_app_aux a ≫ F.to_oplax_functor.map f :=
-- nat_iso.of_components
--   (λ σ, (σ.app b).map_iso (λ_ f) ≪≫ ((σ.app b).map_iso (ρ_ f)).symm ≪≫
--     (σ.naturality_iso f).app (𝟙 (unop a)))
--   (λ (σ τ : yoneda_obj (unop a) ⟶ F) (Γ : σ ⟶ τ), by
--   { simp only [functor.map_iso_inv, iso.app_hom, iso.symm_hom, functor.map_iso_hom, assoc, iso.trans_hom,
--     pseudonat_trans.naturality_iso_hom],
--     have naturality := congr_app (oplax_nat_trans.modification.naturality Γ f) (𝟙 (unop a)),
--     dsimp only [Cat.bicategory] at ⊢ naturality,
--     rw [←naturality, nat_trans.naturality_assoc, nat_trans.naturality_assoc] })

-- lemma yoneda_lemma_naturality_naturality_aux
--   (a b : Bᵒᵖ)
--   (f g : a ⟶ b)
--   (η : f ⟶ g) :
--   ((yoneda.op.comp (yoneda_obj F)).to_oplax_functor.map₂ η ▷ yoneda_lemma_hom_app_aux b) ≫
--       (yoneda_lemma_hom_naturality_aux a b g).hom =
--     (yoneda_lemma_hom_naturality_aux a b f).hom ≫
--       (whisker_left (yoneda_lemma_hom_app_aux a) (F.to_oplax_functor.map₂ η)) :=
-- begin
--   ext σ, simp only [assoc, nat_trans.comp_app, yoneda_lemma_hom_naturality_aux_hom_app],
--   have naturality := congr_app (σ.to_oplax_nat_trans.naturality_naturality η) (𝟙 (unop a)),
--   dsimp [Cat.bicategory] at *, erw [←naturality],
--   simp only [←functor.map_comp_assoc],
--   rwa [left_unitor_naturality_assoc, right_unitor_inv_naturality]
-- end

-- lemma yoneda_lemma_naturality_id_aux
--   (a : Bᵒᵖ) :
--   (yoneda_lemma_hom_naturality_aux a a (𝟙 a)).hom ≫
--       (yoneda_lemma_hom_app_aux a ◁ F.to_oplax_functor.map_id a) =
--     ((yoneda.op.comp (yoneda_obj F)).to_oplax_functor.map_id a ▷
--          yoneda_lemma_hom_app_aux a) ≫
--       (λ_ (yoneda_lemma_hom_app_aux a)).hom ≫
--         (ρ_ (yoneda_lemma_hom_app_aux a)).inv :=
-- begin
--   ext σ, dsimp only [Cat.bicategory], simp only [functor.right_unitor_inv_app, functor.left_unitor_hom_app, whisker_right_app, whisker_left_app, assoc,
--   yoneda_lemma_hom_app_aux_map, comp_id, nat_trans.comp_app, yoneda_lemma_hom_naturality_aux_hom_app],
--   erw comp_id,
--   have naturality := congr_app (σ.to_oplax_nat_trans.naturality_id a) (𝟙 _),
--   dsimp [Cat.bicategory] at *, simp only [comp_id, unitors_equal] at naturality,
--   rw naturality,
--   simp only [comp_id, ←functor.map_comp, unitors_equal, iso.hom_inv_id_assoc]
-- end

-- set_option profiler false

-- lemma yoneda_lemma_naturality_comp_aux
--   (a b c : Bᵒᵖ)
--   (f : a ⟶ b)
--   (g : b ⟶ c) :
--   (yoneda_lemma_hom_naturality_aux a c (f ≫ g)).hom ≫
--       (yoneda_lemma_hom_app_aux a ◁ F.map_comp f g) =
--     ((yoneda.op.comp (yoneda_obj F)).map_comp f g ▷
--          yoneda_lemma_hom_app_aux c) ≫
--       (α_ ((yoneda.op.comp (yoneda_obj F)).map f)
--            ((yoneda.op.comp (yoneda_obj F)).map g)
--            (yoneda_lemma_hom_app_aux c)).hom ≫
--         ((yoneda.op.comp (yoneda_obj F)).map f ◁
--              (yoneda_lemma_hom_naturality_aux b c g).hom) ≫
--           (α_ ((yoneda.op.comp (yoneda_obj F)).map f)
--                (yoneda_lemma_hom_app_aux b)
--                (F.map g)).inv ≫
--             ((yoneda_lemma_hom_naturality_aux a b f).hom ▷
--                  F.map g) ≫
--               (α_ (yoneda_lemma_hom_app_aux a) (F.map f)
--                  (F.map g)).hom :=
-- begin
--   ext σ, dsimp only [Cat.bicategory], simp only [functor.associator_hom_app, functor.associator_inv_app, whisker_right_app, whisker_left_app, assoc, id_comp,
--   yoneda_lemma_hom_app_aux_map, comp_id, functor.map_comp, nat_trans.comp_app, yoneda_lemma_hom_naturality_aux_hom_app],
--   have naturality := congr_app (σ.to_oplax_nat_trans.naturality_comp f g) (𝟙 _),
--   dsimp [Cat.bicategory] at *, simp only [id_comp, comp_id] at naturality,
--   simp only [left_unitor_comp, assoc, id_comp, functor.map_comp, right_unitor_comp_inv],
--   -- erw [left_unitor_comp_assoc, iso.hom_inv_id_assoc, right_unitor_comp_inv,
--   -- triangle_assoc_comp_right_inv],
--   -- simp only [category_theory.category.assoc, category_theory.functor.map_comp],
--   rw naturality,
--   erw ←nat_trans.naturality_assoc,
--   erw ←nat_trans.naturality_assoc,
--   dsimp,
--   simp only [←functor.map_comp_assoc],
--   simp only [triangle_assoc, inv_hom_whisker_right_assoc, comp_id, iso.inv_hom_id],
-- end

-- variables (F)

-- @[simps]
-- def yoneda_lemma_hom : pseudonat_trans (yoneda.op.comp (yoneda_obj F)) F :=
-- { app := yoneda_lemma_hom_app_aux,
--   naturality_iso := yoneda_lemma_hom_naturality_aux,
--   naturality := λ a b f, (yoneda_lemma_hom_naturality_aux a b f).hom,
--   naturality_iso_hom' := by { intros, refl },
--   naturality_naturality' := yoneda_lemma_naturality_naturality_aux,
--   naturality_id' := yoneda_lemma_naturality_id_aux,
--   naturality_comp' := yoneda_lemma_naturality_comp_aux }

-- variables {F}

-- @[simps]
-- def yoneda_lemma_inv_pseudonat_trans_app_aux
--   {a : Bᵒᵖ}
--   (u : F.to_oplax_functor.obj a)
--   (s : Bᵒᵖ) :
--   (yoneda_obj (unop a)).to_oplax_functor.obj s ⟶ F.to_oplax_functor.obj s :=
-- { obj := λ g : a ⟶ s, (F.map g).obj u,
--   map := λ (g h : a ⟶ s) (β : g ⟶ h), (F.map₂ β).app u,
--   map_id'     := by { intros, simp only [nat_trans.id_app, oplax_functor.map₂_id] },
--   map_comp'   := by { intros, simp only [nat_trans.comp_app, oplax_functor.map₂_comp] } }

-- @[simps]
-- def yoneda_lemma_inv_pseudonat_trans_naturality_aux
--   {a : Bᵒᵖ}
--   (u : F.to_oplax_functor.obj a)
--   {s t : Bᵒᵖ} (p : s ⟶ t) :
--     (yoneda_obj (unop a)).to_oplax_functor.map p ≫ yoneda_lemma_inv_pseudonat_trans_app_aux u t ≅
--       yoneda_lemma_inv_pseudonat_trans_app_aux u s ≫ F.to_oplax_functor.map p :=
--  nat_iso.of_components
--   (λ g : a ⟶ s, ((F.map_comp_iso g p).app u))
--   (λ (g h : a ⟶ s) (β : g ⟶ h), by
--   { dsimp [Cat.bicategory], simp only [map_comp_iso_hom, ←nat_trans.comp_app],
--     erw oplax_functor.map_comp_naturality_left, refl })

-- @[simps]
-- def yoneda_lemma_inv_pseudonat_trans {a : Bᵒᵖ} (u : F.obj a) :
--   pseudonat_trans (yoneda_obj (unop a)) F :=
-- { app := yoneda_lemma_inv_pseudonat_trans_app_aux u,
--   naturality_iso := λ s t, yoneda_lemma_inv_pseudonat_trans_naturality_aux u,
--   -- nat_iso.of_components
--   --   (λ g : a ⟶ s, ((F.map_comp_iso g p).app u).symm)
--   --   (λ (g h : a ⟶ s) (β : g ⟶ h), by
--   --   { dsimp, simp only [←whisker_right_app, ←nat_trans.comp_app],
--   --     rw F.map_comp_inv_naturality_left, refl }),
--   naturality := λ s t p, (yoneda_lemma_inv_pseudonat_trans_naturality_aux u p).hom,
--   naturality_naturality' := λ (s t : Bᵒᵖ) (p q : s ⟶ t) (β : p ⟶ q), by
--   { ext (g : a ⟶ s),
--     dsimp [Cat.bicategory],
--     simp only [yoneda_lemma_inv_pseudonat_trans_naturality_aux_hom_app],
--     simp only [←whisker_left_app, ←nat_trans.comp_app],
--     erw oplax_functor.map_comp_naturality_right, refl },
--   naturality_id' := λ s : Bᵒᵖ, by
--   { ext (g : a ⟶ s),
--     dsimp [Cat.bicategory],
--     simp only [yoneda_lemma_inv_pseudonat_trans_naturality_aux_hom_app],
--     simp only [comp_id],
--     simp only [category.id_comp, ←whisker_left_app, ←nat_trans.comp_app],
--     erw [oplax_functor.map₂_right_unitor],
--     simp only [strict.right_unitor_eq_to_iso, eq_to_hom_app, whisker_left_app, eq_to_hom_refl, eq_to_iso.hom, comp_id,
--       nat_trans.comp_app], refl, },
--   naturality_comp' := λ (s t r : Bᵒᵖ) (p : s ⟶ t) (q : t ⟶ r), by
--   { ext (g : a ⟶ s), dsimp [Cat.bicategory],
--     simp only [yoneda_lemma_inv_pseudonat_trans_naturality_aux_hom_app],
--     simp only [id_comp, comp_id, ←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
--     erw oplax_functor.map₂_associator_inv,
--     simp only [strict.associator_eq_to_iso, iso.refl_inv, whisker_left_app,
--       eq_to_iso_refl], erw comp_id, refl } }

-- @[simps]
-- def yoneda_lemma_inv_modification {a : Bᵒᵖ} {u v : F.obj a} (k : u ⟶ v) :
--   (yoneda_lemma_inv_pseudonat_trans u) ⟶ (yoneda_lemma_inv_pseudonat_trans v) :=
-- { app := λ s : Bᵒᵖ,
--   { app := λ g : a ⟶ s, (F.map g).map k,
--     naturality' := by { intros, dsimp, rw nat_trans.naturality } },
--   naturality' := by { intros, ext, dsimp, rw nat_trans.naturality, refl } }

-- @[simps]
-- def yoneda_lemma_inv_functor (a : Bᵒᵖ) : ↥(F.obj a) ⥤ pseudonat_trans (yoneda_obj (unop a)) F :=
-- { obj := λ u : F.obj a, yoneda_lemma_inv_pseudonat_trans u,
--   map := λ (u v : F.obj a) (k : u ⟶ v), yoneda_lemma_inv_modification k,
--   map_id'     := by { intros, ext, dsimp, rw functor.map_id },
--   map_comp'   := by { intros, ext, dsimp, rw functor.map_comp } }

-- @[simps]
-- def yoneda_lemma_inv_iso {a b : Bᵒᵖ} (f : a ⟶ b) (u : F.obj a) :
--   ((yoneda.op.comp (yoneda_obj F)).map f).obj (yoneda_lemma_inv_pseudonat_trans u) ≅
--     yoneda_lemma_inv_pseudonat_trans ((F.map f).obj u) := by
-- { apply modification_iso.of_components (λ s : Bᵒᵖ, _) _,
--   apply nat_iso.of_components (λ g : b ⟶ s, _) _,
--   apply iso.app (F.map_comp f g).symm u,
--   { intros g h β, dsimp, simp only [←whisker_left_app, ←nat_trans.comp_app],
--     erw F.map_comp_inv_naturality_right, refl },
--   { intros s t p, ext (g : b ⟶ s),
--     dsimp, simp,
--     simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
--     erw [F.map₂_associator_inv_eq_assoc, iso.hom_inv_id_assoc],
--     dsimp, simp only [←functor.map_comp, ←nat_trans.comp_app],
--     erw [iso.hom_inv_id, functor.map_id], simp, refl } }

-- variables (F)

-- section aux
-- variables {a b c : Bᵒᵖ}

-- lemma yoneda_lemma_inv_aux₁ (f : unop b ⟶ unop a) (u : F.obj a)
--   {s : Bᵒᵖ} {g h : unop s ⟶ unop b} (β : g ⟶ h) :
--   (((yoneda_lemma_inv_functor b).obj ((F.map f).obj u)).app s).map β ≫
--       (F.map_comp f h).hom.app u =
--     (F.map_comp f g).hom.app u ≫
--       (((yoneda_lemma_inv_functor a).obj u).app s).map (β ▷ f) :=
-- begin
--   dsimp [yoneda_lemma_inv_functor], simp only [←whisker_left_app, ←nat_trans.comp_app],
--   erw F.map_comp_naturality_right, refl,
-- end

-- lemma yoneda_lemma_inv_aux₂ (f : unop b ⟶ unop a) (u : F.obj a)
--   {s t : Bᵒᵖ} (p : unop t ⟶ unop s) (g : unop s ⟶ unop b) :
-- (F.map_comp f (g ≫ p)).hom.app u ≫
--   ((((yoneda.op.comp (yoneda_obj F)).map f).obj ((yoneda_lemma_inv_functor a).obj u)).naturality p).hom.app g
--   = (((yoneda_lemma_inv_functor b).obj ((F.map f).obj u)).naturality p).hom.app g ≫
--       (F.map p).map ((F.map_comp f g).hom.app u) :=
-- begin
--   dsimp [yoneda_lemma_inv_functor], simp,
--   simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
--   erw [F.map₂_associator_inv_eq_assoc, iso.hom_inv_id_assoc,
--       iso.hom_inv_id, category.comp_id],
--   simp, erw category.id_comp
-- end

-- lemma yoneda_lemma_inv_aux₃ (f : unop b ⟶ unop a) {u v : F.obj a}
--   (k : u ⟶ v) {s : Bᵒᵖ} (g : b ⟶ s) :
-- (((yoneda_lemma_inv_functor b).map ((F.map f).map k)).app s).app g ≫
--   (F.map_comp f g).hom.app v
--   = (F.map_comp f g).hom.app u ≫
--       (((yoneda_lemma_inv_functor a).map k).app s).app (g ≫ f) :=
-- begin
--   erw ←nat_trans.naturality, refl
-- end

-- lemma yoneda_lemma_inv_aux₄ (f g : unop b ⟶ unop a) (β : f ⟶ g) (u : F.obj a)
--   {s : Bᵒᵖ} (h : unop s ⟶ unop b) :
-- (((yoneda_lemma_inv_functor b).map ((F.map₂ β).app u)).app s).app h ≫
--   (F.map_comp g h).hom.app u
--   = (F.map_comp f h).hom.app u ≫
--       (((yoneda_lemma_inv_functor a).obj u).app s).map (h ◁ β) :=
-- begin
--   dsimp [yoneda_lemma_inv_functor],
--   simp only [←whisker_right_app, ←nat_trans.comp_app],
--   erw F.map_comp_naturality_left, refl
-- end

-- lemma yoneda_lemma_inv_aux₅ (u : F.obj a) {s : Bᵒᵖ} (g : unop s ⟶ unop a) :
-- (((yoneda_lemma_inv_functor a).map ((F.map_id a).hom.app u)).app s).app g ≫
--   (F.map_comp (𝟙 a) g).hom.app u
--   = 𝟙 _ ≫ 𝟙 _ ≫
--     ((((yoneda.op.comp (yoneda_obj F)).map_id a).hom.app
--       ((yoneda_lemma_inv_functor a).obj u)).app s).app g :=
-- begin
-- dsimp [yoneda_lemma_inv_functor],simp,
--     simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
--     erw F.map₂_left_unitor_inv_eq,
--     dsimp, erw category.id_comp, refl
-- end

-- lemma yoneda_lemma_inv_aux₆ (f : unop b ⟶ unop a) (g : unop c ⟶ unop b)
--   (u : F.obj a) {s : Bᵒᵖ} (h : unop s ⟶ unop c) :
-- (((yoneda_lemma_inv_functor c).map ((F.map_comp f g).hom.app u)).app s).app h ≫
--   (F.map_comp (f ≫ g) h).hom.app u
-- = 𝟙 _ ≫ (F.map_comp g h).hom.app ((F.map f).obj u) ≫
--     𝟙 _ ≫ (F.map_comp f (g ≫ h)).hom.app u ≫
--       𝟙 _ ≫ ((((yoneda.op.comp (yoneda_obj F)).map_comp f g).hom.app
--                 ((yoneda_lemma_inv_functor a).obj u)).app s).app h :=
-- begin
--   dsimp [yoneda_lemma_inv_functor], simp,
--   simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
--   erw [F.map₂_associator_inv_eq, iso.hom_inv_id_assoc], simp,
--   erw category.id_comp
-- end

-- end aux

-- @[simps]
-- def yoneda_lemma_inv : pseudonat_trans F (yoneda.op.comp (yoneda_obj F)) :=
-- { app := λ a : Bᵒᵖ, yoneda_lemma_inv_functor a,
--   naturality := λ (a b : Bᵒᵖ) (f : a ⟶ b), by
--   { apply nat_iso.of_components (λ u : F.obj a, _) _,
--     apply modification_iso.of_components (λ s : Bᵒᵖ, _) _,
--     apply nat_iso.of_components (λ g : b ⟶ s, _) _,
--     apply iso.app (F.map_comp f g) u,
--     { intros, dsimp only, apply yoneda_lemma_inv_aux₁ },
--     { intros, ext, apply yoneda_lemma_inv_aux₂ },
--     { intros, ext, apply yoneda_lemma_inv_aux₃ } },
--   naturality_naturality' := by { intros, ext, apply yoneda_lemma_inv_aux₄ },
--   naturality_id' := by { intros, ext, apply yoneda_lemma_inv_aux₅ },
--   naturality_comp' := by { intros, ext, apply yoneda_lemma_inv_aux₆ } }

-- section aux
-- variables {a b : Bᵒᵖ} (f : unop b ⟶ unop a)
-- (σ : pseudonat_trans (yoneda_obj (unop a)) F)


-- lemma yoneda_lemma_aux₁ {s : Bᵒᵖ} {g h : unop s ⟶ unop a} (β : g ⟶ h) :
--   (σ.app s).map β ≫ (σ.app s).map (ρ_ h).inv ≫ (σ.naturality h).hom.app (𝟙 (unop a))
--   = ((σ.app s).map (ρ_ g).inv ≫ (σ.naturality g).hom.app (𝟙 (unop a))) ≫
--       ((((yoneda_lemma_inv F).app a).obj (((yoneda_lemma_hom F).app a).obj σ)).app s).map β :=
-- begin
--   dsimp, simp only [←functor.map_comp_assoc],
--   rw right_unitor_inv_naturality,
--   simp,
--   have naturality := nat_trans.congr_app (σ.naturality_naturality β) (𝟙 _),
--   dsimp at naturality,
--   simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app,
--     ←functor.map_comp],
--   erw naturality, refl
-- end

-- lemma yoneda_lemma_aux₂ {s t : Bᵒᵖ} (p : unop t ⟶ unop s) (g : unop s ⟶ unop a) :
-- ((σ.app t).map (ρ_ (p ≫ g)).inv ≫ (σ.naturality (g ≫ p)).hom.app (𝟙 (unop a))) ≫
--   ((((yoneda_lemma_inv F).app a).obj
--     (((yoneda_lemma_hom F).app a).obj σ)).naturality p).hom.app g
-- = (σ.naturality p).hom.app g ≫ (F.map p).map ((σ.app s).map (ρ_ g).inv ≫
--     (σ.naturality g).hom.app (𝟙 (unop a))) :=
-- begin
--   dsimp, simp,
--   have comp := nat_trans.congr_app (σ.naturality_comp g p) (𝟙 (unop a)),
--   have naturality := ((σ.naturality p).hom.naturality _),
--   dsimp at comp naturality, simp at comp,
--   slice_rhs 1 2 { erw ←naturality },
--   slice_lhs 2 3 { erw comp },
--   simp, erw category.comp_id
-- end

-- lemma yoneda_lemma_aux₃ {σ τ : pseudonat_trans (yoneda_obj (unop a)) F}
--   (Φ : σ ⟶ τ) {s : Bᵒᵖ} (g : unop s ⟶ unop a) :
-- (Φ.app s).app g ≫ (τ.app s).map (ρ_ g).inv ≫ (τ.naturality g).hom.app (𝟙 (unop a))
-- = ((σ.app s).map (ρ_ g).inv ≫ (σ.naturality g).hom.app (𝟙 (unop a))) ≫
--     ((((yoneda_lemma_inv F).app a).map (((yoneda_lemma_hom F).app a).map Φ)).app s).app g :=
-- begin
--   dsimp, simp,
--   erw ←nat_trans.naturality_assoc,
--   have naturality := nat_trans.congr_app (Φ.naturality g) (𝟙 _),
--   dsimp at naturality,
--   erw naturality
-- end

-- lemma yoneda_lemma_aux₄ {s : Bᵒᵖ} (g : unop s ⟶ unop b) :
-- ((σ.app s).map ((ρ_ g).inv ▷ f) ≫
--   ((((yoneda.op.comp (yoneda_obj F)).map f).obj σ).naturality g).hom.app (𝟙 (unop b))) ≫ 𝟙 _ ≫
--     ((((yoneda_lemma_inv F).app b).map
--       (((yoneda_lemma_hom F).naturality f).hom.app σ)).app s).app g ≫ 𝟙 _ ≫
--         ((((yoneda_lemma_inv F).naturality f).hom.app
--           (((yoneda_lemma_hom F).app a).obj σ)).app s).app g ≫ 𝟙 _
-- = (𝟙 _ ≫ 𝟙 _) ≫
--     (σ.app s).map (ρ_ (g ≫ f)).inv ≫
--       (σ.naturality (f ≫ g)).hom.app (𝟙 (unop a)) :=
-- begin
--   dsimp, simp,
--   have comp := nat_trans.congr_app (σ.naturality_comp f g) (𝟙 (unop a)),
--   dsimp at comp, simp at comp,
--   erw comp,
--   simp only [←category.assoc], congr' 2, simp only [category.assoc],
--   simp only [←functor.map_comp],
--   erw ←nat_trans.naturality,
--   simp,
--   simp only [←functor.map_comp_assoc],
--   erw triangle_assoc,
--   simp
-- end

-- lemma yoneda_lemma_aux₅ {u v : F.obj a} (k :u ⟶ v) :
-- ((yoneda_lemma_hom F).app a).map (((yoneda_lemma_inv F).app a).map k) ≫ (F.map_id a).inv.app v
-- = (F.map_id a).inv.app u ≫ k :=
-- begin
--   dsimp,
--   simp [nat_trans.naturality]
-- end

-- lemma yoneda_lemma_aux₆ (f : unop b ⟶ unop a) (u : F.obj a) :
-- (F.map_id b).inv.app ((F.map f).obj u) ≫ 𝟙 _ ≫ 𝟙 _
-- = (𝟙 _ ≫
--   ((yoneda_lemma_hom F).app b).map
--     (((yoneda_lemma_inv F).naturality f).hom.app u) ≫ 𝟙 _ ≫
--       ((yoneda_lemma_hom F).naturality f).hom.app
--         (((yoneda_lemma_inv F).app a).obj u) ≫ 𝟙 _) ≫
--           (F.map f).map ((F.map_id a).inv.app u) :=
-- begin
--   dsimp, simp,
--   simp only [←whisker_left_app, ←whisker_right_app, ←nat_trans.comp_app],
--   erw [F.map₂_left_unitor_inv_eq_assoc, F.map₂_right_unitor_eq_assoc,
--       iso.hom_inv_id_assoc, iso.hom_inv_id_assoc, iso.hom_inv_id_assoc],
--   simp, simp only [←functor.map_comp, ←nat_trans.comp_app],
--   erw iso.hom_inv_id,
--   simp,
--   erw category.comp_id
-- end

-- end aux

-- /--
-- The Yoneda lemma. It is an equivalence between `yoneda.op.comp (yoneda_obj F)` and `F` in
-- the bicategory `pseudofunctor Bᵒᵖ Cat`.
-- -/
-- def yoneda_lemma : bicategory.equivalence (yoneda.op.comp (yoneda_obj F)) F :=
-- { hom := yoneda_lemma_hom F,
--   inv := yoneda_lemma_inv F,
--   unit_iso := by
--   { apply modification_iso.of_components (λ a : Bᵒᵖ, _) _,
--     apply nat_iso.of_components (λ σ : pseudonat_trans (yoneda_obj (unop a)) F, _) _,
--     apply modification_iso.of_components (λ s : Bᵒᵖ, _) _,
--     apply nat_iso.of_components (λ g : a ⟶ s, _) _,
--     exact (σ.app s).map_iso (λ_ g).symm ≪≫ (σ.naturality g).app (𝟙 (unop a)),
--     { intros, dsimp only, apply yoneda_lemma_aux₁, },
--     { intros, ext, apply yoneda_lemma_aux₂ },
--     { intros, ext, apply yoneda_lemma_aux₃ },
--     { intros, ext, apply yoneda_lemma_aux₄ } },
--   counit_iso := by
--   { apply modification_iso.of_components (λ a : Bᵒᵖ, _) _,
--     apply nat_iso.of_components (λ u : F.obj a, _) _,
--     exact (F.map_id a).symm.app u,
--     { intros, dsimp only, apply yoneda_lemma_aux₅ },
--     { intros, ext, apply yoneda_lemma_aux₆ } } }

-- end

-- end category_theory
