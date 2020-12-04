/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.reflexive
import category_theory.adjunction
import category_theory.closed.cartesian
import category_theory.adjunction.lifting
import category_theory.limits.functor_category

universes u₁ v₁

namespace category_theory
open category limits

variables {C : Type u₁} [small_category C]
variables {E : Type v₁} [category.{u₁} E] [has_products E]

@[simps {rhs_md := semireducible}]
def embed : discrete C ⥤ C :=
discrete.functor id

local attribute [instance] has_finite_products_of_has_finite_limits

@[simps]
noncomputable def ran_obj (T : discrete C ⥤ E) : (C ⥤ E) :=
{ obj := λ U, ∏ (λ (V : C), ∏ (λ (f : U ⟶ V), T.obj V)),
  map := λ X Y f, pi.map (λ Z, pi.lift (λ g, pi.π _ (f ≫ g))),
  map_id' := λ X,
  begin
    apply limit.hom_ext (λ Y, _),
    apply limit.hom_ext (λ g, _),
    rw [lim_map_π, discrete.nat_trans_app, id_comp, assoc, limit.lift_π, fan.mk_π_app, id_comp],
  end,
  map_comp' := λ X Y Z f g,
  begin
    apply limit.hom_ext (λ W, _),
    rw [lim_map_π, assoc, lim_map_π, lim_map_π_assoc, discrete.nat_trans_app,
        discrete.nat_trans_app, discrete.nat_trans_app],
    apply limit.hom_ext (λ h, _),
    rw [assoc, limit.lift_π, fan.mk_π_app, assoc, assoc, assoc, limit.lift_π, fan.mk_π_app,
        limit.lift_π, fan.mk_π_app],
  end }

@[simps]
noncomputable def ran_equiv (T : discrete C ⥤ E) (U : C ⥤ E) :
  (((whiskering_left _ _ _).obj embed).obj U ⟶ T) ≃ (U ⟶ ran_obj T) :=
{ to_fun := λ f,
  { app := λ X,
    begin
      apply pi.lift (λ Y, _),
      apply pi.lift (λ g, U.map g ≫ f.app Y),
    end,
    naturality' := λ X Y g,
    begin
      apply limit.hom_ext (λ Z, _),
      apply limit.hom_ext (λ h, _),
      dsimp,
      rw [assoc, assoc, limit.lift_π_assoc, fan.mk_π_app, limit.lift_π, fan.mk_π_app, assoc, assoc,
          lim_map_π_assoc, discrete.nat_trans_app, limit.lift_π, limit.lift_π_assoc, fan.mk_π_app,
          fan.mk_π_app, limit.lift_π, fan.mk_π_app, U.map_comp, assoc],
    end },
  inv_fun := λ f, discrete.nat_trans
  begin
    intro X,
    apply f.app X ≫ pi.π _ X ≫ pi.π _ (𝟙 _),
  end,
  left_inv := λ f,
  begin
    ext,
    dsimp,
    rw [limit.lift_π_assoc, fan.mk_π_app, limit.lift_π, fan.mk_π_app, U.map_id, id_comp],
  end,
  right_inv := λ f,
  begin
    apply nat_trans.ext,
    apply funext,
    intro X,
    apply limit.hom_ext,
    intro Y,
    apply limit.hom_ext,
    intro g,
    dsimp,
    rw [limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, assoc, reassoc_of (f.naturality g),
        ran_obj_map, lim_map_π_assoc, discrete.nat_trans_app, limit.lift_π, fan.mk_π_app, comp_id],
  end }

noncomputable def ran :
  (discrete C ⥤ E) ⥤ (C ⥤ E) :=
begin
  refine adjunction.right_adjoint_of_equiv (λ U T, ran_equiv T U) _,
  intros F' F G f g,
  ext X Y h,
  dsimp,
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, assoc, assoc, limit.lift_π_assoc,
      fan.mk_π_app, limit.lift_π, fan.mk_π_app, f.naturality_assoc],
end

noncomputable def ran_adj :
  (whiskering_left (discrete C) C E).obj embed ⊣ (ran : _ ⥤ _) :=
adjunction.adjunction_of_equiv_right _ _

noncomputable def bottom_map (F : C ⥤ E) : (discrete C ⥤ E) ⥤ (discrete C ⥤ E) :=
prod.functor.obj (embed ⋙ F)

local attribute [instance] has_finite_products_of_has_products

noncomputable def bottom_map_rad (F : C ⥤ E) [cartesian_closed E] :
  is_left_adjoint (prod.functor.obj (embed ⋙ F)) :=
{ right :=
  begin
    apply adjunction.right_adjoint_of_equiv _ _,
    { apply (prod.functor.obj (embed ⋙ F)) },
    { intro G,
      apply discrete.functor _,
      intro j,
      apply G.obj j ^^ F.obj j },
    { intros G₁ G₂,
      refine ⟨_, _, _, _⟩,
      { intro f,
        apply discrete.nat_trans,
        intro j,
        -- let : F.obj j ⨯ G₁.obj j ⟶ G₂.obj j,
        --   exact inv (prod_comparison ((evaluation (discrete C) E).obj j) (embed ⋙ F) G₁) ≫ f.app j,
        apply cartesian_closed.curry _,
        apply inv (prod_comparison ((evaluation (discrete C) E).obj j) _ G₁) ≫ f.app j,
        },
      { intro f,
        apply discrete.nat_trans,
        intro j,
        apply prod_comparison ((evaluation (discrete C) E).obj j) (embed ⋙ F) G₁ ≫ _,
        apply cartesian_closed.uncurry,
        apply f.app _ },
      { intro f,
        ext,
        dsimp,
        simp },
      { intro f,
        ext,
        dsimp,
        simp } },
    intros G G' H f g,
    ext,
    dsimp,
    rw ← curry_natural_left,
    rw curry_injective.eq_iff,
    apply prod_comparison_inv_natural_assoc,
  end,
  adj :=
  begin
    apply adjunction.adjunction_of_equiv_right _ _,
  end }.

noncomputable instance : comonad (ran ⋙ (whiskering_left (discrete C) C E).obj embed) :=
{ ε := ran_adj.counit,
  δ :=
  begin
    exact whisker_right (whisker_left ran ran_adj.unit) ((whiskering_left (discrete C) C E).obj embed),
  end,
  coassoc' := sorry,
  left_counit' := sorry,
  right_counit' := sorry }

def comonadic : comonad.coalgebra (ran ⋙ (whiskering_left (discrete C) C E).obj embed) ≌ (C ⥤ E) :=
begin
  apply equivalence.mk _ _ _ _,

end

end category_theory
