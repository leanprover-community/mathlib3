/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn
-/
import category_theory.limits.shapes.finite_products
import category_theory.discrete_category

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We also give special cases for (co)products,
but not yet for pullbacks / pushouts or for (co)equalizers.

-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory
open category_theory.functor
open opposite

namespace category_theory.limits

variables {C : Type u₁} [category.{v₁} C]
variables {J : Type u₂} [category.{v₂} J]

/-- Turn a colimit for `F : J ⥤ C` into a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps] def is_limit_cocone_op (F : J ⥤ C) {c : cocone F} (hc : is_colimit c) :
  is_limit c.op :=
{ lift := λ s, (hc.desc s.unop).op,
  fac' := λ s j, quiver.hom.unop_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_colimit.fac] using w (op j)
  end }

/-- Turn a limit for `F : J ⥤ C` into a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps] def is_colimit_cone_op (F : J ⥤ C) {c : cone F} (hc : is_limit c) :
  is_colimit c.op :=
{ desc := λ s, (hc.lift s.unop).op,
  fac' := λ s j, quiver.hom.unop_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_limit.fac] using w (op j)
  end }

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps] def is_limit_cone_left_op_of_cocone (F : J ⥤ Cᵒᵖ) {c : cocone F} (hc : is_colimit c) :
  is_limit (cone_left_op_of_cocone c) :=
{ lift := λ s, (hc.desc (cocone_of_cone_left_op s)).unop,
  fac' :=  λ s j, quiver.hom.op_inj $ by simpa only [cone_left_op_of_cocone_π_app, op_comp,
    quiver.hom.op_unop, is_colimit.fac, cocone_of_cone_left_op_ι_app],
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_colimit.fac, cocone_of_cone_left_op_ι_app] using w (op j)
  end }

/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps] def is_colimit_cocone_left_op_of_cone (F : J ⥤ Cᵒᵖ) {c : cone F} (hc : is_limit c) :
  is_colimit (cocone_left_op_of_cone c) :=
{ desc := λ s, (hc.lift (cone_of_cocone_left_op s)).unop,
  fac' := λ s j, quiver.hom.op_inj $ by simpa only [cocone_left_op_of_cone_ι_app, op_comp,
    quiver.hom.op_unop, is_limit.fac, cone_of_cocone_left_op_π_app],
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_limit.fac, cone_of_cocone_left_op_π_app] using w (op j)
  end }

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps] def is_limit_cone_right_op_of_cocone (F : Jᵒᵖ ⥤ C) {c : cocone F} (hc : is_colimit c) :
  is_limit (cone_right_op_of_cocone c) :=
{ lift := λ s, (hc.desc (cocone_of_cone_right_op s)).op,
  fac' := λ s j, quiver.hom.unop_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_colimit.fac] using w (unop j)
  end }

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps] def is_colimit_cocone_right_op_of_cone (F : Jᵒᵖ ⥤ C) {c : cone F} (hc : is_limit c) :
  is_colimit (cocone_right_op_of_cone c) :=
{ desc := λ s, (hc.lift (cone_of_cocone_right_op s)).op,
  fac' := λ s j, quiver.hom.unop_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_limit.fac] using w (unop j)
  end }

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps] def is_limit_cone_unop_of_cocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : cocone F} (hc : is_colimit c) :
  is_limit (cone_unop_of_cocone c) :=
{ lift := λ s, (hc.desc (cocone_of_cone_unop s)).unop,
  fac' := λ s j, quiver.hom.op_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_colimit.fac] using w (unop j)
  end }

/-- Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`. -/
@[simps] def is_colimit_cocone_unop_of_cone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : cone F} (hc : is_limit c) :
  is_colimit (cocone_unop_of_cone c) :=
{ desc := λ s, (hc.lift (cone_of_cocone_unop s)).unop,
  fac' := λ s j, quiver.hom.op_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_limit.fac] using w (unop j)
  end }

/-- Turn a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F : J ⥤ C`. -/
@[simps] def is_limit_cocone_unop (F : J ⥤ C) {c : cocone F.op} (hc : is_colimit c) :
  is_limit c.unop :=
{ lift := λ s, (hc.desc s.op).unop,
  fac' := λ s j, quiver.hom.op_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_colimit.fac] using w (unop j)
  end }

/-- Turn a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F : J ⥤ C`. -/
@[simps] def is_colimit_cone_unop (F : J ⥤ C) {c : cone F.op} (hc : is_limit c) :
  is_colimit c.unop :=
{ desc := λ s, (hc.lift s.op).unop,
  fac' := λ s j, quiver.hom.op_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_limit.fac] using w (unop j)
  end }

/-- Turn a colimit for `F.left_op : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps] def is_limit_cone_of_cocone_left_op (F : J ⥤ Cᵒᵖ) {c : cocone F.left_op}
  (hc : is_colimit c) : is_limit (cone_of_cocone_left_op c) :=
{ lift := λ s, (hc.desc (cocone_left_op_of_cone s)).op,
  fac' := λ s j, quiver.hom.unop_inj $ by simpa only [cone_of_cocone_left_op_π_app, unop_comp,
    quiver.hom.unop_op, is_colimit.fac, cocone_left_op_of_cone_ι_app],
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_colimit.fac, cone_of_cocone_left_op_π_app] using w (unop j)
  end }

/-- Turn a limit of `F.left_op : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/
@[simps] def is_colimit_cocone_of_cone_left_op (F : J ⥤ Cᵒᵖ) {c : cone (F.left_op)}
  (hc : is_limit c) : is_colimit (cocone_of_cone_left_op c) :=
{ desc := λ s, (hc.lift (cone_left_op_of_cocone s)).op,
  fac' := λ s j, quiver.hom.unop_inj $ by simpa only [cocone_of_cone_left_op_ι_app, unop_comp,
    quiver.hom.unop_op, is_limit.fac, cone_left_op_of_cocone_π_app],
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_limit.fac, cocone_of_cone_left_op_ι_app] using w (unop j)
  end }

/-- Turn a colimit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps] def is_limit_cone_of_cocone_right_op (F : Jᵒᵖ ⥤ C) {c : cocone F.right_op}
  (hc : is_colimit c) : is_limit (cone_of_cocone_right_op c) :=
{ lift := λ s, (hc.desc (cocone_right_op_of_cone s)).unop,
  fac' := λ s j, quiver.hom.op_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_colimit.fac] using w (op j)
  end }

/-- Turn a limit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps] def is_colimit_cocone_of_cone_right_op (F : Jᵒᵖ ⥤ C) {c : cone F.right_op}
  (hc : is_limit c) : is_colimit (cocone_of_cone_right_op c) :=
{ desc := λ s, (hc.lift (cone_right_op_of_cocone s)).unop,
  fac' := λ s j, quiver.hom.op_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.op_inj (hc.hom_ext (λ j, quiver.hom.unop_inj _)),
    simpa only [quiver.hom.op_unop, is_limit.fac] using w (op j)
  end }

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps] def is_limit_cone_of_cocone_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : cocone F.unop} (hc : is_colimit c) :
  is_limit (cone_of_cocone_unop c) :=
{ lift := λ s, (hc.desc (cocone_unop_of_cone s)).op,
  fac' := λ s j, quiver.hom.unop_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_colimit.fac] using w (op j)
  end }

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps] def is_colimit_cone_of_cocone_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : cone F.unop} (hc : is_limit c) :
  is_colimit (cocone_of_cone_unop c) :=
{ desc := λ s, (hc.lift (cone_unop_of_cocone s)).op,
  fac' := λ s j, quiver.hom.unop_inj (by simpa),
  uniq' := λ s m w,
  begin
    refine quiver.hom.unop_inj (hc.hom_ext (λ j, quiver.hom.op_inj _)),
    simpa only [quiver.hom.unop_op, is_limit.fac] using w (op j)
  end }

/--
If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
lemma has_limit_of_has_colimit_left_op (F : J ⥤ Cᵒᵖ) [has_colimit F.left_op] : has_limit F :=
has_limit.mk
{ cone := cone_of_cocone_left_op (colimit.cocone F.left_op),
  is_limit := is_limit_cone_of_cocone_left_op _ (colimit.is_colimit _) }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
lemma has_limits_of_shape_op_of_has_colimits_of_shape [has_colimits_of_shape Jᵒᵖ C] :
  has_limits_of_shape J Cᵒᵖ :=
{ has_limit := λ F, has_limit_of_has_colimit_left_op F }

local attribute [instance] has_limits_of_shape_op_of_has_colimits_of_shape

/--
If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
lemma has_limits_op_of_has_colimits [has_colimits C] : has_limits Cᵒᵖ := ⟨infer_instance⟩


/--
If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
lemma has_colimit_of_has_limit_left_op (F : J ⥤ Cᵒᵖ) [has_limit F.left_op] : has_colimit F :=
has_colimit.mk
{ cocone := cocone_of_cone_left_op (limit.cone F.left_op),
  is_colimit := is_colimit_cocone_of_cone_left_op _ (limit.is_limit _) }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
lemma has_colimits_of_shape_op_of_has_limits_of_shape [has_limits_of_shape Jᵒᵖ C] :
  has_colimits_of_shape J Cᵒᵖ :=
{ has_colimit := λ F, has_colimit_of_has_limit_left_op F }

local attribute [instance] has_colimits_of_shape_op_of_has_limits_of_shape

/--
If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
lemma has_colimits_op_of_has_limits [has_limits C] : has_colimits Cᵒᵖ := ⟨infer_instance⟩

variables (X : Type v₁)
/--
If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
lemma has_coproducts_opposite [has_products_of_shape X C] :
  has_coproducts_of_shape X Cᵒᵖ :=
begin
  haveI : has_limits_of_shape (discrete X)ᵒᵖ C :=
    has_limits_of_shape_of_equivalence (discrete.opposite X).symm,
  apply_instance
end

/--
If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
lemma has_products_opposite [has_coproducts_of_shape X C] :
  has_products_of_shape X Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape (discrete X)ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence (discrete.opposite X).symm,
  apply_instance
end

lemma has_finite_coproducts_opposite [has_finite_products C] :
  has_finite_coproducts Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, begin
    resetI,
    haveI : has_limits_of_shape (discrete J)ᵒᵖ C :=
      has_limits_of_shape_of_equivalence (discrete.opposite J).symm,
    apply_instance,
  end }

lemma has_finite_products_opposite [has_finite_coproducts C] :
  has_finite_products Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, begin
    resetI,
    haveI : has_colimits_of_shape (discrete J)ᵒᵖ C :=
      has_colimits_of_shape_of_equivalence (discrete.opposite J).symm,
    apply_instance,
  end }

lemma has_equalizers_opposite [has_coequalizers C] : has_equalizers Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape walking_parallel_pair.{v₁}ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_parallel_pair_op_equiv.{v₁},
  apply_instance
end

lemma has_coequalizers_opposite [has_equalizers C] : has_coequalizers Cᵒᵖ :=
begin
  haveI : has_limits_of_shape walking_parallel_pair.{v₁}ᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_parallel_pair_op_equiv.{v₁},
  apply_instance
end

lemma has_finite_colimits_opposite [has_finite_limits C] :
  has_finite_colimits Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, by { resetI, apply_instance, }, }

lemma has_finite_limits_opposite [has_finite_colimits C] :
  has_finite_limits Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, by { resetI, apply_instance, }, }

end category_theory.limits
