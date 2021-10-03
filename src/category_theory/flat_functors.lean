import category_theory.structured_arrow
import category_theory.filtered
import category_theory.limits.presheaf
import category_theory.limits.kan_extension
import category_theory.limits.filtered_colimit_commutes_finite_limit

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory
open category_theory.limits
open opposite


-- set_option pp.universes true
-- set_option trace.class_instances true

-- #check @types.sort.category_theory.limits.has_limits

-- instance inst : has_limits (Cᵒᵖ ⥤ Type u₁) := infer_instance
namespace category_theory

section defs
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

class representably_flat (u : C ⥤ D) : Prop :=
(cofiltered : ∀ (X : D), is_cofiltered (costructured_arrow u X))

def functor.flat_cofiltered (u : C ⥤ D) [representably_flat u] (X : D) :
 is_cofiltered (costructured_arrow u X) := representably_flat.cofiltered X

variables (u : C ⥤ D) [representably_flat u] {X : D} (Y₁ Y₂ : costructured_arrow u X)

instance cofiltered_of_flat := u.flat_cofiltered X

end defs
section sec1
variables {C : Type u₁} [category.{v₁} C] {D : Type u₁} [category.{v₂} D]
variables {E : Type u₃} [category.{u₁} E] [has_limits E]

noncomputable
instance whiskering_left_preserves_small_limits (J : Type u₁) [H : small_category J]  (F) :
  preserves_limits_of_shape J ((whiskering_left C D E).obj F) := ⟨λ K, ⟨λ c hc,
begin
  apply evaluation_jointly_reflects_limits,
  intro Y,
  change is_limit (((evaluation D E).obj (F.obj Y)).map_cone c),
  exact preserves_limit.preserves hc,
end ⟩⟩
end sec1
section lems
variables {C D E: Type u₁} [category.{u₁} C] [category.{u₁} D] [category.{u₁} E]

-- include Y₁ Y₂

-- noncomputable theory

-- def functor.flat_min : costructured_arrow u X :=
-- (category_theory.is_cofiltered_or_empty.cocone_objs Y₁ Y₂).some

-- def functor.flat_min_left : u.flat_min Y₁ Y₂ ⟶ Y₁ :=
-- (category_theory.is_cofiltered_or_empty.cocone_objs Y₁ Y₂).some_spec.some

-- def functor.flat_min_right : u.flat_min Y₁ Y₂ ⟶ Y₂ :=
-- (category_theory.is_cofiltered_or_empty.cocone_objs Y₁ Y₂).some_spec.some_spec.some

-- def functor.flat_min_comm :=
-- (category_theory.is_cofiltered_or_empty.cocone_maps Y₁ Y₂)
-- lemma lem0 (F : C ⥤ D) (X : Dᵒᵖ) :
--   (((whiskering_left _ _ _).obj (costructured_arrow.proj F.op X)) ⋙ colim : (Cᵒᵖ ⥤ Type u₁) ⥤ _) =
--     Lan F.op ⋙ (evaluation Dᵒᵖ (Type u₁)).obj X :=
-- begin
--   apply functor.hext,
--   { intro Y, simp },
--   intros Y₁ Y₂ f,
--   simp only [functor.comp_map, evaluation_obj_map, whiskering_left_obj_map, Lan_map_app, heq_iff_eq],
--   apply (colimit.is_colimit (Lan.diagram F.op Y₁ X)).uniq { X := colimit _, ι := _ }
--     (colim.map (whisker_left (costructured_arrow.proj F.op X) f)),
--   intro Z,
--   simp only [colimit.ι_map, colimit.cocone_ι, whisker_left_app, category.comp_id, category.assoc],
--   transitivity f.app Z.left ≫ (colimit.ι (costructured_arrow.map Z.hom ⋙ Lan.diagram F.op Y₂ X :
--     costructured_arrow F.op _ ⥤ _) (costructured_arrow.mk (𝟙 (F.op.obj Z.left))) : _)
--     ≫ (colimit.pre (Lan.diagram F.op Y₂ X) (costructured_arrow.map Z.hom)),
--   { rw colimit.ι_pre,
--     congr,
--     simp only [category.id_comp, costructured_arrow.map_mk],
--     apply costructured_arrow.eq_mk },
--   { congr }
-- end

-- @[simps] noncomputable
-- def swap_cone (J : Type u₁) [small_category J] (F: C ⥤ D ⥤ E) (K : J ⥤ C) [has_limit K] (X : D) :
--   cone ((curry.obj (prod.swap D J ⋙ uncurry.obj (K ⋙ F))).obj X) := {
--   X := (F.obj (limit K)).obj X,
--   π := eq_to_hom (by {
--       apply functor.hext,
--       intro Y, simp,
--       intros Y₁ Y₂ f, simp, congr,
--   }) ≫ whisker_right (limit.cone K).π ((curry.obj (prod.swap _ _ ⋙ uncurry.obj F)).obj X)
-- }

-- -- lemma lemm (J : Type u₁) [small_category J] [fin_category J] {F: C ⥤ D ⥤ E} {K : J ⥤ C}
-- -- [has_limits_of_shape J E] [has_colimits_of_shape D E] [has_limit K] :
-- -- ((F ⋙ colim).map_cone (limit.cone K)).X =
-- --   colimit (curry.obj (prod.swap D J ⋙ uncurry.obj (K ⋙ F)) ⋙ lim)
-- -- := by {

-- -- }

-- noncomputable theory

-- -- lemma is_limit_swap_cone (J : Type u₁) [small_category J] (F: C ⥤ D ⥤ E) (K : J ⥤ C) [has_limit K]
-- --   (X : D) : is_limit (swap_cone J F K X) := {
-- --     lift := λ s, by {
-- --       unfold swap_cone,
-- --       simp,
-- --     }
--   -- }

-- local attribute[reducible] prod.swap
-- variables (J : Type u₁) [small_category J] (K : J ⥤ C) (F : C ⥤ D ⥤ E)
--   [has_limit K] [has_limits_of_shape J E]


-- def hom1 : F.obj (limit K) ⟶ curry.obj (prod.swap D J ⋙ uncurry.obj (K ⋙ F)) ⋙ lim := {
-- app := λ Y, limit.post K ((curry.obj (prod.swap D C ⋙ uncurry.obj F)).obj Y),
-- naturality' := λ Y₁ Y₂ f, by {
--   let F' := curry.obj (prod.swap D C ⋙ uncurry.obj F),
--   suffices : ((F'.map f).app (limit K)) ≫ limit.post K (F'.obj Y₂) =
--     limit.post K (F'.obj Y₁) ≫ lim_map (whisker_left K (F'.map f)),
--   { convert this using 2,
--     { simp, erw category.id_comp },
--     { simp only [functor.comp_map, lim_map_eq_lim_map], dsimp only [prod.swap],
--       congr, ext, simp, congr } },
--   ext,
--   simp only [nat_trans.naturality, limit.post_π, lim_map_π,
--     whisker_left_app, limit.post_π_assoc, category.assoc],
-- }
-- }

-- def hom3 : F.obj (limit K) ⟶ curry.obj (prod.swap D J ⋙ uncurry.obj (K ⋙ F)) ⋙ lim := by {
--   let Y : D, admit,
--   let G := ((curry.obj (prod.swap D C ⋙ uncurry.obj F)).obj Y),
--   have := (limit.is_limit (K ⋙ G)).lift_cone_morphism (G.map_cone (limit.cone K)),
-- -- app := λ Y, limit.post K ((curry.obj (prod.swap D C ⋙ uncurry.obj F)).obj Y),
-- -- naturality' := λ Y₁ Y₂ f, by {
-- --   let F' := curry.obj (prod.swap D C ⋙ uncurry.obj F),
-- --   suffices : ((F'.map f).app (limit K)) ≫ limit.post K (F'.obj Y₂) =
-- --     limit.post K (F'.obj Y₁) ≫ lim_map (whisker_left K (F'.map f)),
-- --   { convert this using 2,
-- --     { simp, erw category.id_comp },
-- --     { simp only [functor.comp_map, lim_map_eq_lim_map], dsimp only [prod.swap],
-- --       congr, ext, simp, congr } },
-- --   ext,
-- --   simp only [nat_trans.naturality, limit.post_π, lim_map_π,
-- --     whisker_left_app, limit.post_π_assoc, category.assoc],
-- -- }
-- }

-- variables [has_colimits_of_shape D E] [has_limit (K ⋙ F ⋙ colim)]

-- -- def hom2 : (F ⋙ colim).map_cone (limit.cone K) ⟶ limit.cone (K ⋙ F ⋙ colim) := {
-- --   hom := colim_map (hom1 _ _ _) ≫
-- --           (colimit_limit_to_limit_colimit (uncurry.obj (K ⋙ F) : _)) ≫
-- --           lim_map (whisker_right (currying.unit_iso.inv.app (K ⋙ F)) colim),
-- --   w' := λ Y, by {
-- --       ext, unfold colimit_limit_to_limit_colimit hom1, simp,
-- --       erw category.id_comp,
-- --       erw limits.limit.post_π_assoc,
-- --       congr,
-- --       simp,
-- --   }
-- -- }

-- -- set_option pp.universes true

-- def lem4 [fin_category J] [is_cofiltered D] [has_limits_of_shape J E]
--   {F : C ⥤ D ⥤ E} [has_limit (K ⋙ F ⋙ colim)] : is_limit ((F ⋙ colim).map_cone (limit.cone K)) :=
-- begin
--   have : ((F ⋙ colim).map_cone (limit.cone K)).X ≅ limit (K ⋙ F ⋙ colim),
--   simp,
--   apply is_limit.of_iso_limit (limit.is_limit _),
--   symmetry
--   -- haveI : is_iso this.hom,
--   -- {

--   -- }
-- end

-- def lemlem (J : Type u₁) [category J] (F : C ⥤ D ⥤ E) (K : J ⥤ C)
-- (H : ∀ (X : D), preserves_limit K (F ⋙ (evaluation _ _).obj X)) : preserves_limit K F := {
--   preserves := λ c hc, by {
--     apply evaluation_jointly_reflects_limits,
--     intro X,
--     have := @preserves_limit.preserves _ _ _ _ _ _ _ _ (H X) _ hc,
--     -- have := (H X).preserves (((evaluation _ _).obj X).map_cone c),
--   }
-- }



-- lemma
set_option pp.universes true

#check preserves_limits_of_shape_if_evaluation

def lem1 (F : C ⥤ D) [representably_flat F] (J : Type u₁) [H : small_category J] [fin_category J] :
  preserves_limits_of_shape J (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)) :=
begin
  have : category.{u₁} (Dᵒᵖ ⥤ Type u₁) := infer_instance,
  have := @preserves_limits_of_shape_if_evaluation (Dᵒᵖ ⥤ Type u₁) _ Cᵒᵖ,
  -- (Lan F.op : (Cᵒᵖ ⥤ Type u₁) ⥤ (Dᵒᵖ ⥤ Type u₁)) J,
  exact
{ preserves_limit := λ K, {
  preserves := λ c hc, by {
    apply evaluation_jointly_reflects_limits,
    intro X,
    change is_limit ((Lan F.op ⋙ (evaluation Dᵒᵖ (Type u₁)).obj X).map_cone c),
    rw ← lem0,
    apply is_limit.of_iso_limit _ (functor.map_iso _ ((limit.is_limit _).unique_up_to_iso hc)),
    haveI : preserves_limit K ((whiskering_left _ _ (Type u₁)).obj
      (costructured_arrow.proj F.op X)) := {
        preserves := λ c hc, by {
          apply evaluation_jointly_reflects_limits,
          intro Y,
          change is_limit (((evaluation _ (Type u₁)).obj
            ((costructured_arrow.proj F.op X).obj Y)).map_cone c),
          exact preserves_limit.preserves hc,
        }
      },
    generalize : (whiskering_left _ _ (Type u₁)).obj
      (costructured_arrow.proj F.op X) = G,
    haveI : preserves_limits G,
    apply_instance,
    -- let G :=
    --   K ⋙
    --     ((whiskering_left _ _ _).obj (costructured_arrow.proj F.op X)),
    let := (colimit_limit_to_limit_colimit (uncurry.obj (K ⋙ G) : _)),
    simp at this,
--     have : G ⋙ colim = K ⋙ (Lan F.op ⋙ (evaluation Dᵒᵖ (Type u₁)).obj X),
--     {
--       change K ⋙ (_ ⋙ colim) = K ⋙ _,
--       congr' 1,
--       unfold Lan, simp,
--       apply functor.hext,
--       intro Y, simp,
--       intros Y₁ Y₂ f,
--       simp only [category_theory.adjunction.left_adjoint_of_equiv_map,
--  category_theory.whiskering_left_obj_map,
--  category_theory.functor.comp_map,
--  heq_iff_eq,
--  category_theory.evaluation_obj_map],
--       ext,
--       simp?,
--       congr,
--     }
    -- dsimp[G] at this,
    -- simp at this,
    -- delta evaluation functor.map_cone cones.functoriality,
    -- have := ,
    -- have := (structured_arrow.proj _ F).op ⋙ F,
    -- have := colimit_limit_to_limit_colimit_is_iso,
    -- delta Lan,
    -- dsimp,
    -- apply is_limit.of_iso_limit _ (as_iso (colimit_limit_to_limit_colimit _)),
  }
} }
end

theorem thm (F : C ⥤ D) : representably_flat F ↔
  ∀ (J : Type u₁) [H : small_category J] [@fin_category J H],
    ∃ (H : @preserves_limits_of_shape _ _ _ _ J H (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁))), true := sorry

end category_theory
