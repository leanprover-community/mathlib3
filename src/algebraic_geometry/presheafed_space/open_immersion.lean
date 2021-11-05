/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.presheafed_space.has_colimits
import category_theory.limits.shapes.binary_products

/-!
# Open immersions of presheafed spaces

We say that a morphism of presheaved spaces `f : X ⟶ Y` is an open immersions if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and `f : 𝒪_Y ⟶ f _* ℱ ` factors through
`of_restrict : Y|ᵤ ⟶ Y` via some isomorphism `X ≅ Y|ᵤ`.

We also proves that the pullback of two presheaved spaces exists, and is also an open immersion.
-/

open topological_space category_theory opposite
open category_theory.limits algebraic_geometry
namespace algebraic_geometry.PresheafedSpace

universes v u

variables {C : Type u} [category.{v} C]

/--
An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, and an isomorphism between the structure sheaves `𝒪ₓ ≅ 𝒪|ᵤ`, such that `f` factors through
`of_restrict : 𝒪|ᵤ ⟶ 𝒪_Y`.
-/
class open_immersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop :=
(base_open : open_embedding f.base)
(c_iso : ∀ U : opens X, is_iso (f.c.app (op (base_open.is_open_map.functor.obj U))))

attribute [instance] open_immersion.c_iso

namespace open_immersion

variables {X Y : PresheafedSpace C} {f : X ⟶ Y} (H : open_immersion f)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbreviation open_functor := H.base_open.is_open_map.functor

local attribute [-simp] eq_to_hom_map eq_to_iso_map

/-- An open immersion `f : X ⟶ Y` induces an isomorphsm `X ≅ Y|_{f(X)}`. -/
@[simps] noncomputable
def iso_restrict : X ≅ Y.restrict H.base_open :=
PresheafedSpace.iso_of_components (iso.refl _)
begin
  symmetry,
  fapply nat_iso.of_components,
  intro U,
  refine as_iso (f.c.app (op (H.open_functor.obj (unop U)))) ≪≫ X.presheaf.map_iso (eq_to_iso _),
  { induction U using opposite.rec,
    cases U,
    dsimp only [is_open_map.functor, functor.op, opens.map],
    congr' 2,
    erw set.preimage_image_eq _ H.base_open.inj,
    refl },
  { intros U V i,
    simp only [category_theory.eq_to_iso.hom, Top.presheaf.pushforward_obj_map, category.assoc,
      functor.op_map, iso.trans_hom, as_iso_hom, functor.map_iso_hom, ←X.presheaf.map_comp],
    erw [f.c.naturality_assoc, ←X.presheaf.map_comp],
    congr }
end

@[simp] lemma iso_restrict_hom_of_restrict : H.iso_restrict.hom ≫ Y.of_restrict _ = f :=
begin
  ext,
  { simp only [comp_c_app, iso_restrict_hom_c_app, nat_trans.comp_app,
      eq_to_hom_refl, of_restrict_c_app, category.assoc, whisker_right_id'],
    erw [category.comp_id, f.c.naturality_assoc, ←X.presheaf.map_comp],
    transitivity f.c.app x ≫ X.presheaf.map (𝟙 _),
    { congr },
    { erw [X.presheaf.map_id, category.comp_id] } },
  { simp }
end

@[simp] lemma iso_restrict_inv_of_restrict : H.iso_restrict.inv ≫ f = Y.of_restrict _ :=
by { rw iso.inv_comp_eq, simp }

instance mono [H : open_immersion f] : mono f :=
by { rw ← H.iso_restrict_hom_of_restrict, apply mono_comp }

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (f : X ⟶ Y) [hf : open_immersion f] (g : Y ⟶ Z)
  [hg : open_immersion g] :
  open_immersion (f ≫ g) :=
{ base_open := hg.base_open.comp hf.base_open,
  c_iso := λ U,
  begin
    generalize_proofs h,
    dsimp only [algebraic_geometry.PresheafedSpace.comp_c_app, unop_op, functor.op, comp_base,
      Top.presheaf.pushforward_obj_obj, opens.map_comp_obj],
    apply_with is_iso.comp_is_iso { instances := ff },
    swap,
    { have : (opens.map g.base).obj (h.functor.obj U) = hf.open_functor.obj U,
      { dsimp only [opens.map, is_open_map.functor, PresheafedSpace.comp_base],
        congr' 1,
        rw [coe_comp, ←set.image_image, set.preimage_image_eq _ hg.base_open.inj] },
      rw this,
      apply_instance },
    { have : h.functor.obj U = hg.open_functor.obj (hf.open_functor.obj U),
      { dsimp only [is_open_map.functor],
        congr' 1,
        rw [comp_base, coe_comp, ←set.image_image],
        congr },
      rw this,
      apply_instance }
  end
}

/-- An isomorphism is an open immersion. -/
instance of_iso {X Y : PresheafedSpace C} (H : X ≅ Y) : open_immersion H.hom :=
{ base_open := (Top.homeo_of_iso ((forget C).map_iso H)).open_embedding,
  c_iso := λ _, infer_instance }

@[priority 100]
instance of_is_iso {X Y : PresheafedSpace C} (f : X ⟶ Y) [is_iso f] : open_immersion f :=
algebraic_geometry.PresheafedSpace.open_immersion.of_iso (as_iso f)

instance of_restrict {X : Top} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
  (hf : open_embedding f) : open_immersion (Y.of_restrict hf) :=
{ base_open := hf,
  c_iso := λ U,
  begin
    dsimp,
    have : (opens.map f).obj (hf.is_open_map.functor.obj U) = U,
    { cases U,
      dsimp only [opens.map, is_open_map.functor],
      congr' 1,
      rw set.preimage_image_eq _ hf.inj,
      refl },
    convert (show is_iso (Y.presheaf.map (𝟙 _)), from infer_instance),
    { apply subsingleton.helim,
      rw this },
    { rw Y.presheaf.map_id,
      apply_instance }
  end }

end open_immersion

open open_immersion

section restrict_pullback
noncomputable theory

-- variables {X Y : Top.{v}} (Z : PresheafedSpace C)
-- variables {f : X ⟶ Z.1} (hf : open_embedding f) {g : Y ⟶ Z.1} (hg : open_embedding g)
-- include hf hg

variables {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : open_immersion f] (g : Y ⟶ Z)

include hf

def pullback_cone : pullback_cone f g :=
begin
  fapply pullback_cone.mk,
  exact Y.restrict (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base),
  refine { base := pullback.fst, c := { app := _, naturality' := _ } },
  -- have := by { },
  dsimp,
  intro U,
  refine X.presheaf.map (eq_to_hom _) ≫
    inv (f.c.app (op (hf.base_open.is_open_map.functor.obj (unop U)))) ≫
    g.c.app (op (hf.base_open.is_open_map.functor.obj (unop U))) ≫ Y.presheaf.map (eq_to_hom _),
  { induction U using opposite.rec,
    simp[opens.map, is_open_map.functor, set.preimage_image_eq _ hf.base_open.inj] },
    induction U using opposite.rec,
    simp[opens.map, is_open_map.functor],
  -- have := ,
  dsimp,
end

-- /--
-- We construct the pullback of two restrictions via restricting along the pullback of the
-- maps of underlying spaces (which is also an open embedding).
-- -/
-- def pullback_cone_of_restrict : pullback_cone (Z.of_restrict hf) (Z.of_restrict hg) :=
-- begin
--   fapply pullback_cone.mk,
--   exact Z.restrict (Top.open_embedding_of_pullback_open_embeddings hf hg),
--   exact (restrict_comp Z _ (Top.fst_open_embedding_of_right_open_embedding f hg) f hf
--     (limit.π (cospan f g) walking_cospan.one) (limit.w _ walking_cospan.hom.inl).symm).hom
--       ≫ PresheafedSpace.of_restrict _ _,
--   exact (restrict_comp Z _ (Top.snd_open_embedding_of_left_open_embedding hf g) g hg
--     (limit.π (cospan f g) walking_cospan.one) (limit.w _ walking_cospan.hom.inr).symm).hom
--       ≫ PresheafedSpace.of_restrict _ _,
--   simp
-- end


-- variable (s : pullback_cone (Z.of_restrict hf) (Z.of_restrict hg))

-- /--
--   (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-- -/
-- def pullback_cone_of_restrict_lift : s.X ⟶ (pullback_cone_of_restrict Z hf hg).X :=
-- { base := pullback.lift s.fst.base s.snd.base
--   (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition),
--   c := whisker_left _ (s.π.app walking_cospan.one).c ≫
--     (whisker_right (nat_trans.op
--     { app := λ U, hom_of_le
--       (λ x (hx : x ∈ (opens.map (pullback.lift s.fst.base s.snd.base _)).obj U),
--         ⟨pullback.lift s.fst.base s.snd.base
--             (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition) x, hx,
--           show limit.π (cospan f g) walking_cospan.one
--             (pullback.lift s.fst.base s.snd.base _ x) = (s.π.app walking_cospan.one).base x,
--           by  { have := s.π.naturality walking_cospan.hom.inl,
--                 erw category.id_comp at this,
--                 simpa [this] } ⟩),
--       naturality' := λ _ _ _, refl _ }) s.X.presheaf
--       : (is_open_map.functor _ ⋙ opens.map _).op ⋙ s.X.presheaf ⟶ _ ⋙ s.X.presheaf)}

-- lemma pullback_cone_of_restrict_lift_comp_fst :
--   pullback_cone_of_restrict_lift Z hf hg s ≫
--     (pullback_cone_of_restrict Z hf hg).fst = s.fst :=
-- begin
--   delta pullback_cone_of_restrict_lift pullback_cone_of_restrict,
--   ext x,
--   { induction x using opposite.rec,
--     cases x,
--     have i : f ⁻¹' (⇑(limit.π (cospan f g) walking_cospan.one) ''
--       ((pullback.fst : pullback f g ⟶ _) ⁻¹' x_val)) ⊆ x_val,
--     { rw [←limit.w (cospan f g) walking_cospan.hom.inl, coe_comp, ←set.image_image],
--       erw set.preimage_image_eq _ hf.inj,
--       simp },
--     have := λ x, PresheafedSpace.congr_app
--       ((category.id_comp _).symm.trans (s.π.naturality walking_cospan.hom.inl : _)) x,
--     dsimp only [PresheafedSpace.comp_c_app, whisker_right_app,
--       nat_trans.comp_app],
--     erw this,
--     dsimp only [pullback_cone.mk_fst, PresheafedSpace.comp_c_app],
--     erw restrict_comp_hom_c_app',
--     simp only [category.assoc],
--     erw ←Z.presheaf.map_comp_assoc,
--     erw ←Z.presheaf.map_comp_assoc,
--     erw s.fst.c.naturality_assoc,
--     iterate 3 { erw [←s.X.presheaf.map_comp] },
--     convert category.comp_id _,
--     exact s.X.presheaf.map_id _,
--     { dsimp only [functor.op], refine (hom_of_le _).op, exact i } },
--   { change pullback.lift _ _ _ ≫ 𝟙 _ ≫ pullback.fst = _,
--     simp only [category.comp_id, category.id_comp, pullback.lift_fst] }
-- end

-- lemma pullback_cone_of_restrict_lift_comp_snd :
--   pullback_cone_of_restrict_lift Z hf hg s ≫
--     (pullback_cone_of_restrict Z hf hg).snd = s.snd :=
-- begin
--   delta pullback_cone_of_restrict_lift pullback_cone_of_restrict,
--   ext x,
--   { induction x using opposite.rec,
--     cases x,
--     have i : g ⁻¹' (⇑(limit.π (cospan f g) walking_cospan.one) ''
--       ((pullback.snd : pullback f g ⟶ _) ⁻¹' x_val)) ⊆ x_val,
--     { rw [←limit.w (cospan f g) walking_cospan.hom.inr, coe_comp, ←set.image_image],
--       erw set.preimage_image_eq _ hg.inj,
--       simp },
--     have := λ x, PresheafedSpace.congr_app
--       ((category.id_comp _).symm.trans (s.π.naturality walking_cospan.hom.inr : _)) x,
--     dsimp only [PresheafedSpace.comp_c_app, whisker_right_app,
--       nat_trans.comp_app],
--     erw this,
--     dsimp only [pullback_cone.mk_snd, PresheafedSpace.comp_c_app],
--     erw restrict_comp_hom_c_app',
--     simp only [category.assoc],
--     erw ←Z.presheaf.map_comp_assoc,
--     erw ←Z.presheaf.map_comp_assoc,
--     erw s.snd.c.naturality_assoc,
--     iterate 3 { erw [←s.X.presheaf.map_comp] },
--     convert category.comp_id _,
--     exact s.X.presheaf.map_id _,
--     { dsimp only [functor.op], refine (hom_of_le _).op, exact i } },
--   { change pullback.lift _ _ _ ≫ 𝟙 _ ≫ pullback.snd = _,
--     simp only [category.comp_id, category.id_comp, pullback.lift_snd] }
-- end

-- lemma pullback_cone_π_app_one_base :
--   ((pullback_cone_of_restrict Z hf hg).π.app walking_cospan.one).base =
--     limit.π (cospan f g) walking_cospan.one :=
-- begin
--   delta pullback_cone_of_restrict,
--   simp only [open_immersion.iso_restrict_inv_of_restrict, restrict_comp_hom_base, cospan_map_inl,
--     category.assoc, PresheafedSpace.comp_base, pullback_cone.mk_π_app_one,
--     PresheafedSpace.of_restrict_base, ← limit.w (cospan f g) walking_cospan.hom.inl],
--   erw category.id_comp
-- end

-- instance pullback_cone_fst_open_immersion :
--   open_immersion (pullback_cone_of_restrict Z hf hg).fst :=
-- begin
--   erw category_theory.limits.pullback_cone.mk_fst,
--   apply_instance
-- end

-- instance pullback_cone_snd_open_immersion :
--   open_immersion (pullback_cone_of_restrict Z hf hg).snd :=
-- begin
--   erw category_theory.limits.pullback_cone.mk_snd,
--   apply_instance
-- end

-- instance pullback_cone_one_open_immersion :
--   open_immersion ((pullback_cone_of_restrict Z hf hg).π.app walking_cospan.one) :=
-- begin
--   erw (category.id_comp _).symm.trans
--     ((pullback_cone_of_restrict Z hf hg).π.naturality walking_cospan.hom.inl : _),
--   dsimp only [cospan_map_inl, cospan_one],
--   apply_instance
-- end

-- /-- The constructed pullback cone is indeed the pullback. -/
-- def pullback_cone_of_restrict_is_limit :
--   is_limit (pullback_cone_of_restrict Z hf hg) :=
-- begin
--   apply pullback_cone.is_limit_aux',
--   intro s,
--   split,
--   swap,
--   exact pullback_cone_of_restrict_lift Z hf hg s,
--   split,
--   apply pullback_cone_of_restrict_lift_comp_fst,
--   split,
--   apply pullback_cone_of_restrict_lift_comp_snd,
--   intros m h₁ h₂,
--   have := congr_arg (λ i, i ≫ Z.of_restrict hf)
--     (h₁.trans (pullback_cone_of_restrict_lift_comp_fst Z hf hg s).symm),
--   simp only [category.assoc] at this,
--   erw ← (pullback_cone_of_restrict Z hf hg).π.naturality walking_cospan.hom.inl at this,
--   simp only [←category.assoc] at this,
--   rw cancel_mono at this,
--   erw cancel_mono (𝟙 _) at this,
--   exact this,
--   apply_instance
-- end

-- instance has_pullback_of_restrict :
--   has_pullback (Z.of_restrict hf) (Z.of_restrict hg) :=
-- ⟨⟨⟨_, pullback_cone_of_restrict_is_limit Z hf hg⟩⟩⟩

-- end restrict_pullback

-- variables {X Y Z : PresheafedSpace C}
-- variables (f : X ⟶ Z) [hf : open_immersion f] (g : Y ⟶ Z) [hg : open_immersion g]
-- include hf hg

-- /--
-- (Implementation). `cospan f g` is naturally isomporphic to
-- `cospan (Z.of_restrict hf) (Z.of_restrict hg)`.
-- -/
-- def open_immersion_cospan_iso :
--   cospan f g ≅ cospan (Z.of_restrict hf.base_open) (Z.of_restrict hg.base_open) :=
-- nat_iso.of_components
--   (λ j, by { rcases j with (_|_|_), exacts [iso.refl _, hf.iso_restrict, hg.iso_restrict] })
--   (by rintros _ _ (_|_|_); simp[hf.iso_restrict_hom_of_restrict, hg.iso_restrict_hom_of_restrict])

-- instance has_pullback_of_open_immersion :
--   has_pullback f g :=
-- has_limit_of_iso (open_immersion_cospan_iso f g).symm

-- instance open_immersion.pullback_fst_open_immersion :
--   open_immersion (pullback.fst : pullback f g ⟶ _) :=
-- begin
--   have := has_limit.iso_of_nat_iso_hom_π (open_immersion_cospan_iso f g) walking_cospan.left,
--   erw ← iso.comp_inv_eq at this,
--   delta pullback.fst,
--   rw ← this,
--   rw ← (limit.iso_limit_cone_hom_π
--     ⟨_, (pullback_cone_of_restrict_is_limit Z hf.base_open hg.base_open)⟩ walking_cospan.left),
--   apply_instance
-- end

-- instance open_immersion.pullback_snd_open_immersion :
--   open_immersion (pullback.snd : pullback f g ⟶ _) :=
-- begin
--   have := has_limit.iso_of_nat_iso_hom_π (open_immersion_cospan_iso f g) walking_cospan.right,
--   erw ← iso.comp_inv_eq at this,
--   delta pullback.snd,
--   rw ← this,
--   rw ← (limit.iso_limit_cone_hom_π
--     ⟨_, (pullback_cone_of_restrict_is_limit Z hf.base_open hg.base_open)⟩ walking_cospan.right),
--   apply_instance
-- end

-- instance open_immersion.pullback_one_open_immersion :
--   open_immersion (limit.π (cospan f g) walking_cospan.one) :=
-- begin
--   rw [←limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl],
--   apply_instance
-- end

end algebraic_geometry.PresheafedSpace
