/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.types
import category_theory.currying

/-!
# The morphism comparing a colimit of limits with the corresponding limit of colimits.

For `F : J × K ⥤ C` there is always a morphism $\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$.
While it is not usually an isomorphism, with additional hypotheses on `J` and `K` it may be,
in which case we say that "colimits commute with limits".

The prototypical example, proved in `category_theory.limits.filtered_colimit_commutes_finite_limit`,
is that when `C = Type`, filtered colimits commute with finite limits.

## References
* Borceux, Handbook of categorical algebra 1, Section 2.13
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/

universes w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

open category_theory

namespace category_theory.limits

variables {J : Type u₁} {K : Type u₂} [category.{v₁} J] [category.{v₂} K]
variables {C : Type u₃} [category.{v₃} C]

variables {F : J ⥤ K ⥤ C}

variables {cj : Π (j : J), cone (F.obj j)}
variables {ck : Π (k : K), cocone (F.flip.obj k)}
variables (tj : Π (j : J), is_limit (cj j))
variables (tk : Π (k : K), is_colimit (ck k))

@[simps]
def cones_to_functor : J ⥤ C :=
{ obj := λ j, (cj j).X,
  map := λ j₁ j₂ α, (tj j₂).map (cj j₁) (F.map α),
  map_id' := λ j, (tj j).hom_ext (by simp),
  map_comp' := λ j₁ j₂ j₃ α β, (tj j₃).hom_ext (by simp) }

@[simps]
def cocones_to_functor : K ⥤ C :=
{ obj := λ k, (ck k).X,
  map := λ k₁ k₂ α, (tk k₁).map (ck k₂) (F.flip.map α),
  map_id' := λ k, (tk k).hom_ext (by tidy),
  map_comp' := λ k₁ k₂ k₃ α β, (tk k₁).hom_ext (by simp) }

variables {c₁ : cocone (cones_to_functor tj)} (t₁ : is_colimit c₁)
variables {c₂ : cone (cocones_to_functor tk)} (t₂ : is_limit c₂)

-- { obj := λ k, (ck k).X,
--   map := λ k₁ k₂ α, is_colimit.map (ck k₁) (tk k₂) (F.map α),
--   map_id' := λ j, (tj j).hom_ext (by simp),
--   map_comp' := λ j₁ j₂ j₃ α β, (tj j₃).hom_ext (by simp) }

def colimit_to_limit : c₁.X ⟶ c₂.X :=
t₂.lift
{ X := _,
  π :=
  { app := λ k, t₁.desc
    { X := _,
      ι :=
      { app := λ j, (cj j).π.app k ≫ (ck k).ι.app j,
        naturality' := λ j₁ j₂ f, by { dsimp, simp [←(ck k).w f] } } },
    naturality' := λ k₁ k₂ f, t₁.hom_ext (by tidy) } }.

lemma ι_colimit_to_limit_π (j k) :
  c₁.ι.app j ≫ colimit_to_limit tj tk t₁ t₂ ≫ c₂.π.app k = (cj j).π.app k ≫ (ck k).ι.app j :=
by simp [colimit_to_limit]

-- /--
-- The universal morphism
-- $\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$.
-- -/
-- noncomputable
-- def colimit_limit_to_limit_colimit :
--   colimit ((curry.obj (swap K J ⋙ F)) ⋙ lim) ⟶ limit ((curry.obj F) ⋙ colim) :=
-- limit.lift ((curry.obj F) ⋙ colim)
-- { X := _,
--   π :=
--   { app := λ j, colimit.desc ((curry.obj (swap K J ⋙ F)) ⋙ lim)
--     { X := _,
--       ι :=
--       { app := λ k,
--           limit.π ((curry.obj (swap K J ⋙ F)).obj k) j ≫ colimit.ι ((curry.obj F).obj j) k,
--         naturality' :=
--         begin
--           dsimp,
--           intros k k' f,
--           simp only [functor.comp_map, curry.obj_map_app, limits.lim_map_π_assoc, swap_map,
--             category.comp_id, map_id_left_eq_curry_map, colimit.w],
--         end }, },
--     naturality' :=
--     begin
--       dsimp,
--       intros j j' f,
--       ext k,
--       simp only [limits.colimit.ι_map, curry.obj_map_app, limits.colimit.ι_desc_assoc,
--         limits.colimit.ι_desc, category.id_comp, category.assoc, map_id_right_eq_curry_swap_map,
--         limit.w_assoc],
--     end } }

-- /--
-- Since `colimit_limit_to_limit_colimit` is a morphism from a colimit to a limit,
-- this lemma characterises it.
-- -/
-- @[simp] lemma ι_colimit_limit_to_limit_colimit_π (j) (k) :
--   colimit.ι _ k ≫ colimit_limit_to_limit_colimit F ≫ limit.π _ j =
--     limit.π ((curry.obj (swap K J ⋙ F)).obj k) j ≫ colimit.ι ((curry.obj F).obj j) k :=
-- by { dsimp [colimit_limit_to_limit_colimit], simp, }

-- @[simp] lemma ι_colimit_limit_to_limit_colimit_π_apply (F : J × K ⥤ Type v) (j) (k) (f) :
--    limit.π ((curry.obj F) ⋙ colim) j
--      (colimit_limit_to_limit_colimit F (colimit.ι ((curry.obj (swap K J ⋙ F)) ⋙ lim) k f)) =
--      colimit.ι ((curry.obj F).obj j) k (limit.π ((curry.obj (swap K J ⋙ F)).obj k) j f) :=
-- by { dsimp [colimit_limit_to_limit_colimit], simp, }

end category_theory.limits
