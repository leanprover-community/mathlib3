/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.kan_extension
import category_theory.limits.filtered_colimit_commutes_finite_limit
import category_theory.limits.preserves.functor_category
import category_theory.limits.presheaf

/-!
# Representably flat functors

Define representably flat functors as functors such that the catetory of structured arrows over `X`
is cofltered for each `X`. This concept is also knows as flat functors as in [Elephant],
Remark C2.3.7, and is called representably flat as suggested by Mike Shulman at
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to differentiate it
from the other notions of flatness.

We

## TODO

* Dualise to pushouts
* Generalise to wide pullbacks

-/

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory
open category_theory.limits
open opposite

namespace category_theory

section defs
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

class representably_flat (u : C ⥤ D) : Prop :=
(cofiltered : ∀ (X : D), is_cofiltered (structured_arrow X u))

lemma functor.flat_cofiltered (u : C ⥤ D) [representably_flat u] (X : D) :
 is_cofiltered (structured_arrow X u) := representably_flat.cofiltered X

variables (u : C ⥤ D) [representably_flat u] {X : D} (Y₁ Y₂ : costructured_arrow u X)

instance cofiltered_of_flat := u.flat_cofiltered X
end defs

section small_category
variables {C D : Type u₁} [small_category C] [small_category D]

/--
(Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costrucuted arrows over `X`.
-/
lemma Lan_evaluation_eq_colim (E : Type u₂) [category.{u₁} E] (F : C ⥤ D) (X : D)
  [∀ (X : D), has_colimits_of_shape (costructured_arrow F X) E] :
  Lan F ⋙ (evaluation D E).obj X =
  ((whiskering_left _ _ E).obj (costructured_arrow.proj F X)) ⋙ colim :=
begin
  apply functor.hext,
  { intro Y, simp },
  intros Y₁ Y₂ f,
  simp only [functor.comp_map, evaluation_obj_map, whiskering_left_obj_map, Lan_map_app, heq_iff_eq],
  symmetry,
  apply (colimit.is_colimit (Lan.diagram F Y₁ X)).uniq { X := colimit _, ι := _ }
    (colim.map (whisker_left (costructured_arrow.proj F X) f)),
  intro Z,
  simp only [colimit.ι_map, colimit.cocone_ι, whisker_left_app, category.comp_id, category.assoc],
  transitivity f.app Z.left ≫ (colimit.ι (costructured_arrow.map Z.hom ⋙ Lan.diagram F Y₂ X :
    costructured_arrow F _ ⥤ _) (costructured_arrow.mk (𝟙 (F.obj Z.left))) : _)
    ≫ (colimit.pre (Lan.diagram F Y₂ X) (costructured_arrow.map Z.hom)),
  { rw colimit.ι_pre,
    congr,
    simp only [category.id_comp, costructured_arrow.map_mk],
    apply costructured_arrow.eq_mk },
  { congr }
end

/--
If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable
def Lan_presesrves_finite_limit_of_flat (F : C ⥤ D) [representably_flat F]
  (J : Type u₁) [small_category J] [fin_category J] :
  preserves_limits_of_shape J (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)) :=
begin
  apply preserves_limits_of_shape_if_evaluation (Lan F.op : (Cᵒᵖ ⥤ Type u₁) ⥤ (Dᵒᵖ ⥤ Type u₁)) J,
  intro K,
  rw Lan_evaluation_eq_colim,
  haveI : is_filtered (costructured_arrow F.op K) :=
    is_filtered.of_equivalence (structured_arrow_op_equivalence F (unop K)),
  apply_instance
end

def preserves_finite_limit_of_flat (F : C ⥤ D) [representably_flat F]
  (J : Type u₁) [small_category J] [fin_category J] :
  preserves_limits_of_shape J F := by {
  have := F ⋙ yoneda,
  have := yoneda ⋙ (Lan F.op : _),
  have := colimit_adj.extend_along_yoneda (F ⋙ yoneda) ≅ Lan F.op,
  let := whisker_left yoneda (Lan.adjunction (Type u₁) F.op).unit,
  -- simp at this,
  -- haveI : = Lan_presesrves_finite_limit_of_flat F,
}

end small_category

end category_theory
