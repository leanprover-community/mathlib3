import category_theory.adjunction.basic
import category_theory.yoneda

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace category_theory
open category

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]

-- section transfer
-- variables {F H : C ⥤ D} {G K : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : H ⊣ K)

-- include adj₁ adj₂

-- @[simps]
-- def transfer_nat_trans : (F ⟶ H) ≃ (K ⟶ G) :=
-- { to_fun := λ h,
--   { app := λ X, adj₁.unit.app (K.obj X) ≫ G.map (h.app (K.obj X) ≫ adj₂.counit.app X),
--     naturality' := λ X Y f, by { rw [←adj₁.unit_naturality_assoc, ←G.map_comp], simp } },
--   inv_fun := λ h,
--   { app := λ X, F.map (adj₂.unit.app _ ≫ h.app _) ≫ adj₁.counit.app _,
--     naturality' := λ X Y f, by { rw [← F.map_comp_assoc, ← adj₂.unit_naturality_assoc], simp } },
--   left_inv := λ h, by { ext X, dsimp, simp },
--   right_inv := λ h,
--   begin
--     ext X,
--     dsimp,
--     rw [G.map_comp, G.map_comp, assoc, adj₁.unit_naturality_assoc,
--         adj₁.right_triangle_components_assoc, assoc, ←h.naturality,
--         adj₂.right_triangle_components_assoc],
--   end }

-- lemma transfer_nat_trans_comp_swap (f : F ⟶ H) (g : H ⟶ F) (h : g ≫ f = 𝟙 _) :
--   transfer_nat_trans adj₁ adj₂ f ≫ transfer_nat_trans adj₂ adj₁ g = 𝟙 _ :=
-- begin
--   ext X,
--   dsimp,
--   rw [← adj₂.unit_naturality_assoc, ← K.map_comp, g.naturality_assoc, F.map_comp, assoc,
--     adj₁.counit_naturality, adj₁.left_triangle_components_assoc, ← assoc, ← nat_trans.comp_app],
--   simp [h],
-- end

-- lemma transfer_nat_trans_symm_comp_swap (f : K ⟶ G) (g : G ⟶ K) (h : g ≫ f = 𝟙 _) :
--   (transfer_nat_trans adj₁ adj₂).symm f ≫ (transfer_nat_trans adj₂ adj₁).symm g = 𝟙 F :=
-- begin
--   ext X,
--   dsimp,
--   rw [assoc, ← adj₁.counit_naturality_assoc, ← adj₁.counit_naturality, ← F.map_comp_assoc, assoc,
--       ←f.naturality, adj₂.unit_naturality_assoc, ← F.map_comp_assoc, assoc, assoc, assoc,
--       ←f.naturality, adj₂.right_triangle_components_assoc],
--   dsimp,
--   rw [← nat_trans.comp_app],
--   simp [h],
-- end

-- def transfer_nat_trans_is_iso (f : F ⟶ H) [is_iso f] : is_iso (transfer_nat_trans adj₁ adj₂ f) :=
-- { inv := transfer_nat_trans adj₂ adj₁ (inv f),
--   hom_inv_id' := transfer_nat_trans_comp_swap _ _ _ _ (by simp),
--   inv_hom_id' := transfer_nat_trans_comp_swap _ _ _ _ (by simp) }

-- def is_iso_of_transfer_nat_trans_is_iso (f : K ⟶ G) [is_iso f] :
--   is_iso ((transfer_nat_trans adj₁ adj₂).symm f) :=
-- { inv := (transfer_nat_trans adj₂ adj₁).symm (inv f),
--   hom_inv_id' := transfer_nat_trans_symm_comp_swap _ _ _ _ (by simp),
--   inv_hom_id' := transfer_nat_trans_symm_comp_swap _ _ _ _ (by simp) }
-- end transfer

section square

variables {E : Type u₃} {F : Type u₄} [category.{v₃} E] [category.{v₄} F]

--      C ↔ D
--    G ↓   ↓ H
--      E ↔ F

variables {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variables (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

include adj₁ adj₂
-- f ≫ g = h

-- F.map f ≫ F.map g = F.map h
-- F.map (f ≫ g) = F.map f ≫ F.map g
-- rw [← F.map_comp, h, F.map_comp],
-- rw [h_map],

@[simps]
def transfer_nat_trans : (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) :=
{ to_fun := λ h,
  { app := λ X, adj₂.unit.app _ ≫ R₂.map (h.app _ ≫ H.map (adj₁.counit.app _)),
    naturality' := λ X Y f,
    begin
      dsimp,
      rw [assoc, ← R₂.map_comp, assoc, ← H.map_comp, ← adj₁.counit_naturality, H.map_comp,
          ←functor.comp_map L₁, ←h.naturality_assoc],
      simp,
    end },
  inv_fun := λ h,
  { app := λ X, L₂.map (G.map (adj₁.unit.app _) ≫ h.app _) ≫ adj₂.counit.app _,
  naturality' := λ X Y f,
  begin
    dsimp,
    rw [← L₂.map_comp_assoc, ← G.map_comp_assoc, ← adj₁.unit_naturality, G.map_comp_assoc,
        ← functor.comp_map, h.naturality],
    simp,
  end },
  left_inv := λ h,
  begin
    ext X,
    dsimp,
    simp only [L₂.map_comp, assoc, adj₂.counit_naturality, adj₂.left_triangle_components_assoc,
      ←functor.comp_map G L₂, h.naturality_assoc, functor.comp_map L₁, ←H.map_comp,
      adj₁.left_triangle_components],
    dsimp,
    simp, -- See library note [dsimp, simp].
  end,
  right_inv := λ h,
  begin
    ext X,
    dsimp,
    simp [-functor.comp_map, ←functor.comp_map H, functor.comp_map R₁, -nat_trans.naturality,
      ←h.naturality, -functor.map_comp, ←functor.map_comp_assoc G, R₂.map_comp],
  end }

def transfer_nat_trans_equiv [is_equivalence G] [is_equivalence H]
-- def transfer_nat_trans_is_iso (f : G ⋙ L₂ ⟶ L₁ ⋙ H) [is_iso f] :
--   is_iso (transfer_nat_trans adj₁ adj₂ f) :=
-- { inv := transfer_nat_trans _ _ _,
--   hom_inv_id' := sorry,
--   inv_hom_id' := sorry

-- }

-- { inv := transfer_nat_trans adj₂ adj₁ (inv f),
--   hom_inv_id' := transfer_nat_trans_comp_swap _ _ _ _ (by simp),
--   inv_hom_id' := transfer_nat_trans_comp_swap _ _ _ _ (by simp) }

-- @[simps]
-- def left_to_right (h : G ⋙ L₂ ⟶ L₁ ⋙ H) : R₁ ⋙ G ⟶ H ⋙ R₂ :=
-- { app := λ X, adj₂.unit.app _ ≫ R₂.map (h.app _ ≫ H.map (adj₁.counit.app _)),
--   naturality' := λ X Y f,
--   begin
--     dsimp,
--     rw [assoc, ← R₂.map_comp, assoc, ← H.map_comp, ← adj₁.counit_naturality, H.map_comp,
--         ←functor.comp_map L₁, ←h.naturality_assoc],
--     simp,
--   end }

-- @[simps]
-- def right_to_left (h : R₁ ⋙ G ⟶ H ⋙ R₂) : G ⋙ L₂ ⟶ L₁ ⋙ H :=
-- { app := λ X, L₂.map (G.map (adj₁.unit.app _) ≫ h.app _) ≫ adj₂.counit.app _,
--   naturality' := λ X Y f,
--   begin
--     dsimp,
--     rw [← L₂.map_comp_assoc, ← G.map_comp_assoc, ← adj₁.unit_naturality, G.map_comp_assoc,
--         ← functor.comp_map, h.naturality],
--     simp,
--   end }

end square

end category_theory
