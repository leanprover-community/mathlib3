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

lemma lem0 (F : C ⥤ D) (X : Dᵒᵖ) :
  (((whiskering_left _ _ _).obj (costructured_arrow.proj F.op X)) ⋙ colim : (Cᵒᵖ ⥤ Type u₁) ⥤ _) =
    Lan F.op ⋙ (evaluation Dᵒᵖ (Type u₁)).obj X :=
begin
  apply functor.hext,
  { intro Y, simp },
  intros Y₁ Y₂ f,
  simp only [functor.comp_map, evaluation_obj_map, whiskering_left_obj_map, Lan_map_app, heq_iff_eq],
  apply (colimit.is_colimit (Lan.diagram F.op Y₁ X)).uniq { X := colimit _, ι := _ }
    (colim.map (whisker_left (costructured_arrow.proj F.op X) f)),
  intro Z,
  simp only [colimit.ι_map, colimit.cocone_ι, whisker_left_app, category.comp_id, category.assoc],
  transitivity f.app Z.left ≫ (colimit.ι (costructured_arrow.map Z.hom ⋙ Lan.diagram F.op Y₂ X :
    costructured_arrow F.op _ ⥤ _) (costructured_arrow.mk (𝟙 (F.op.obj Z.left))) : _)
    ≫ (colimit.pre (Lan.diagram F.op Y₂ X) (costructured_arrow.map Z.hom)),
  { rw colimit.ι_pre,
    congr,
    simp only [category.id_comp, costructured_arrow.map_mk],
    apply costructured_arrow.eq_mk },
  { congr }
end

end lems
noncomputable theory
variables {C : Type u₁} [category.{u₁} C] {D : Type u₁} [category.{u₁} D]

def lem1 (F : C ⥤ D) [representably_flat F] (J : Type u₁) [H : small_category J] [fin_category J] :
  preserves_limits_of_shape J (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)) :=
begin
  -- have : category.{u₁} (Dᵒᵖ ⥤ Type u₁) := infer_instance,
  apply preserves_limits_of_shape_if_evaluation (Lan F.op : (Cᵒᵖ ⥤ Type u₁) ⥤ (Dᵒᵖ ⥤ Type u₁)) J,
  intro K,
  rw ← lem0,
  haveI : preserves_limits_of_shape J (colim : (costructured_arrow F.op K ⥤ Type u₁) ⥤ Type u₁),
  swap, apply_instance,
  haveI

end

theorem thm (F : C ⥤ D) : representably_flat F ↔
  ∀ (J : Type u₁) [H : small_category J] [@fin_category J H],
    ∃ (H : @preserves_limits_of_shape _ _ _ _ J H (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁))), true := sorry

end category_theory
