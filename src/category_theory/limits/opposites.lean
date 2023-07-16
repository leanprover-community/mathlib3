/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn
-/
import category_theory.limits.filtered
import category_theory.limits.shapes.finite_products
import category_theory.discrete_category
import tactic.equiv_rw

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We also give special cases for (co)products,
(co)equalizers, and pullbacks / pushouts.

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

lemma has_limit_of_has_colimit_op (F : J ⥤ C) [has_colimit F.op] : has_limit F :=
has_limit.mk
{ cone := (colimit.cocone F.op).unop,
  is_limit := is_limit_cocone_unop _ (colimit.is_colimit _) }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
lemma has_limits_of_shape_op_of_has_colimits_of_shape [has_colimits_of_shape Jᵒᵖ C] :
  has_limits_of_shape J Cᵒᵖ :=
{ has_limit := λ F, has_limit_of_has_colimit_left_op F }

lemma has_limits_of_shape_of_has_colimits_of_shape_op [has_colimits_of_shape Jᵒᵖ Cᵒᵖ] :
  has_limits_of_shape J C :=
{ has_limit := λ F, has_limit_of_has_colimit_op F }

local attribute [instance] has_limits_of_shape_op_of_has_colimits_of_shape

/--
If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
instance has_limits_op_of_has_colimits [has_colimits C] : has_limits Cᵒᵖ := ⟨infer_instance⟩

lemma has_limits_of_has_colimits_op [has_colimits Cᵒᵖ] : has_limits C :=
{ has_limits_of_shape := λ J hJ, by exactI has_limits_of_shape_of_has_colimits_of_shape_op }

instance has_cofiltered_limits_op_of_has_filtered_colimits
  [has_filtered_colimits_of_size.{v₂ u₂} C] : has_cofiltered_limits_of_size.{v₂ u₂} Cᵒᵖ :=
{ has_limits_of_shape := λ I hI₁ hI₂, by exactI has_limits_of_shape_op_of_has_colimits_of_shape }

lemma has_cofiltered_limits_of_has_filtered_colimits_op
  [has_filtered_colimits_of_size.{v₂ u₂} Cᵒᵖ] : has_cofiltered_limits_of_size.{v₂ u₂} C :=
{ has_limits_of_shape := λ I hI₂ hI₂, by exactI has_limits_of_shape_of_has_colimits_of_shape_op }

/--
If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
lemma has_colimit_of_has_limit_left_op (F : J ⥤ Cᵒᵖ) [has_limit F.left_op] : has_colimit F :=
has_colimit.mk
{ cocone := cocone_of_cone_left_op (limit.cone F.left_op),
  is_colimit := is_colimit_cocone_of_cone_left_op _ (limit.is_limit _) }

lemma has_colimit_of_has_limit_op (F : J ⥤ C) [has_limit F.op] : has_colimit F :=
has_colimit.mk
{ cocone := (limit.cone F.op).unop,
  is_colimit := is_colimit_cone_unop _ (limit.is_limit _) }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
instance has_colimits_of_shape_op_of_has_limits_of_shape [has_limits_of_shape Jᵒᵖ C] :
  has_colimits_of_shape J Cᵒᵖ :=
{ has_colimit := λ F, has_colimit_of_has_limit_left_op F }

lemma has_colimits_of_shape_of_has_limits_of_shape_op [has_limits_of_shape Jᵒᵖ Cᵒᵖ] :
  has_colimits_of_shape J C :=
{ has_colimit := λ F, has_colimit_of_has_limit_op F }

/--
If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
instance has_colimits_op_of_has_limits [has_limits C] : has_colimits Cᵒᵖ := ⟨infer_instance⟩

lemma has_colimits_of_has_limits_op [has_limits Cᵒᵖ] : has_colimits C :=
{ has_colimits_of_shape := λ J hJ, by exactI has_colimits_of_shape_of_has_limits_of_shape_op }

instance has_filtered_colimits_op_of_has_cofiltered_limits
  [has_cofiltered_limits_of_size.{v₂ u₂} C] : has_filtered_colimits_of_size.{v₂ u₂} Cᵒᵖ :=
{ has_colimits_of_shape := λ I hI₁ hI₂, by exactI infer_instance }

lemma has_filtered_colimits_of_has_cofiltered_limits_op
  [has_cofiltered_limits_of_size.{v₂ u₂} Cᵒᵖ] : has_filtered_colimits_of_size.{v₂ u₂} C :=
{ has_colimits_of_shape := λ I hI₁ hI₂, by exactI has_colimits_of_shape_of_has_limits_of_shape_op }

variables (X : Type v₂)
/--
If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
instance has_coproducts_of_shape_opposite [has_products_of_shape X C] :
  has_coproducts_of_shape X Cᵒᵖ :=
begin
  haveI : has_limits_of_shape (discrete X)ᵒᵖ C :=
    has_limits_of_shape_of_equivalence (discrete.opposite X).symm,
  apply_instance
end

lemma has_coproducts_of_shape_of_opposite [has_products_of_shape X Cᵒᵖ] :
  has_coproducts_of_shape X C :=
begin
  haveI : has_limits_of_shape (discrete X)ᵒᵖ Cᵒᵖ :=
    has_limits_of_shape_of_equivalence (discrete.opposite X).symm,
  exact has_colimits_of_shape_of_has_limits_of_shape_op
end

/--
If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
instance has_products_of_shape_opposite [has_coproducts_of_shape X C] :
  has_products_of_shape X Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape (discrete X)ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence (discrete.opposite X).symm,
  apply_instance
end

lemma has_products_of_shape_of_opposite [has_coproducts_of_shape X Cᵒᵖ] :
  has_products_of_shape X C :=
begin
  haveI : has_colimits_of_shape (discrete X)ᵒᵖ Cᵒᵖ :=
    has_colimits_of_shape_of_equivalence (discrete.opposite X).symm,
  exact has_limits_of_shape_of_has_colimits_of_shape_op
end

instance has_products_opposite [has_coproducts.{v₂} C] : has_products.{v₂} Cᵒᵖ :=
λ X, infer_instance

lemma has_products_of_opposite [has_coproducts.{v₂} Cᵒᵖ] : has_products.{v₂} C :=
λ X, has_products_of_shape_of_opposite X

instance has_coproducts_opposite [has_products.{v₂} C] : has_coproducts.{v₂} Cᵒᵖ :=
λ X, infer_instance

lemma has_coproducts_of_opposite [has_products.{v₂} Cᵒᵖ] : has_coproducts.{v₂} C :=
λ X, has_coproducts_of_shape_of_opposite X

instance has_finite_coproducts_opposite [has_finite_products C] : has_finite_coproducts Cᵒᵖ :=
{ out := λ n, limits.has_coproducts_of_shape_opposite _ }

lemma has_finite_coproducts_of_opposite [has_finite_products Cᵒᵖ] : has_finite_coproducts C :=
{ out := λ n, has_coproducts_of_shape_of_opposite _ }

instance has_finite_products_opposite [has_finite_coproducts C] : has_finite_products Cᵒᵖ :=
{ out := λ n, infer_instance }

lemma has_finite_products_of_opposite [has_finite_coproducts Cᵒᵖ] : has_finite_products C :=
{ out := λ n, has_products_of_shape_of_opposite _ }

instance has_equalizers_opposite [has_coequalizers C] : has_equalizers Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape walking_parallel_pairᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_parallel_pair_op_equiv,
  apply_instance
end

instance has_coequalizers_opposite [has_equalizers C] : has_coequalizers Cᵒᵖ :=
begin
  haveI : has_limits_of_shape walking_parallel_pairᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_parallel_pair_op_equiv,
  apply_instance
end

instance has_finite_colimits_opposite [has_finite_limits C] :
  has_finite_colimits Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, by { resetI, apply_instance, }, }

instance has_finite_limits_opposite [has_finite_colimits C] :
  has_finite_limits Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, by { resetI, apply_instance, }, }

instance has_pullbacks_opposite [has_pushouts C] : has_pullbacks Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape walking_cospanᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_cospan_op_equiv.symm,
  apply has_limits_of_shape_op_of_has_colimits_of_shape,
end

instance has_pushouts_opposite [has_pullbacks C] : has_pushouts Cᵒᵖ :=
begin
  haveI : has_limits_of_shape walking_spanᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_span_op_equiv.symm,
  apply_instance
end

/-- The canonical isomorphism relating `span f.op g.op` and `(cospan f g).op` -/
@[simps]
def span_op {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  span f.op g.op ≅ walking_cospan_op_equiv.inverse ⋙ (cospan f g).op :=
nat_iso.of_components (by { rintro (_|_|_); refl, })
  (by { rintros (_|_|_) (_|_|_) f; cases f; tidy, })

/-- The canonical isomorphism relating `(cospan f g).op` and `span f.op g.op` -/
@[simps]
def op_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).op ≅ walking_cospan_op_equiv.functor ⋙ span f.op g.op :=
calc (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op : by refl
... ≅ (walking_cospan_op_equiv.functor ⋙ walking_cospan_op_equiv.inverse) ⋙ (cospan f g).op :
  iso_whisker_right walking_cospan_op_equiv.unit_iso _
... ≅ walking_cospan_op_equiv.functor ⋙ (walking_cospan_op_equiv.inverse ⋙ (cospan f g).op) :
  functor.associator _ _ _
... ≅ walking_cospan_op_equiv.functor ⋙ span f.op g.op : iso_whisker_left _ (span_op f g).symm

/-- The canonical isomorphism relating `cospan f.op g.op` and `(span f g).op` -/
@[simps]
def cospan_op {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  cospan f.op g.op ≅ walking_span_op_equiv.inverse ⋙ (span f g).op :=
nat_iso.of_components (by { rintro (_|_|_); refl, })
  (by { rintros (_|_|_) (_|_|_) f; cases f; tidy, })

/-- The canonical isomorphism relating `(span f g).op` and `cospan f.op g.op` -/
@[simps]
def op_span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).op ≅ walking_span_op_equiv.functor ⋙ cospan f.op g.op :=
calc (span f g).op ≅ 𝟭 _ ⋙ (span f g).op : by refl
... ≅ (walking_span_op_equiv.functor ⋙ walking_span_op_equiv.inverse) ⋙ (span f g).op :
  iso_whisker_right walking_span_op_equiv.unit_iso _
... ≅ walking_span_op_equiv.functor ⋙ (walking_span_op_equiv.inverse ⋙ (span f g).op) :
  functor.associator _ _ _
... ≅ walking_span_op_equiv.functor ⋙ cospan f.op g.op :
  iso_whisker_left _ (cospan_op f g).symm

namespace pushout_cocone

/-- The obvious map `pushout_cocone f g → pullback_cone f.unop g.unop` -/
@[simps (lemmas_only)]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  pullback_cone f.unop g.unop :=
cocone.unop ((cocones.precompose (op_cospan f.unop g.unop).hom).obj
  (cocone.whisker walking_cospan_op_equiv.functor c))

@[simp]
lemma unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  c.unop.fst = c.inl.unop :=
by { change (_ : limits.cone _).π.app _ = _,
  simp only [pushout_cocone.ι_app_left, pushout_cocone.unop_π_app], tidy }

@[simp]
lemma unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  c.unop.snd = c.inr.unop :=
by { change (_ : limits.cone _).π.app _ = _,
  simp only [pushout_cocone.unop_π_app, pushout_cocone.ι_app_right], tidy, }

/-- The obvious map `pushout_cocone f.op g.op → pullback_cone f g` -/
@[simps (lemmas_only)]
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  pullback_cone f.op g.op :=
(cones.postcompose ((cospan_op f g).symm).hom).obj
  (cone.whisker walking_span_op_equiv.inverse (cocone.op c))

@[simp]
lemma op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  c.op.fst = c.inl.op :=
by { change (_ : limits.cone _).π.app _ = _, apply category.comp_id, }

@[simp]
lemma op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  c.op.snd = c.inr.op :=
by { change (_ : limits.cone _).π.app _ = _, apply category.comp_id, }

end pushout_cocone

namespace pullback_cone

/-- The obvious map `pullback_cone f g → pushout_cocone f.unop g.unop` -/
@[simps (lemmas_only)]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  pushout_cocone f.unop g.unop :=
cone.unop ((cones.postcompose (op_span f.unop g.unop).symm.hom).obj
  (cone.whisker walking_span_op_equiv.functor c))

@[simp]
lemma unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  c.unop.inl = c.fst.unop :=
begin
  change ((_ : limits.cocone _).ι.app _) = _,
  dsimp only [unop, op_span],
  simp, dsimp, simp, dsimp, simp
end

@[simp]
lemma unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  c.unop.inr = c.snd.unop :=
begin
  change ((_ : limits.cocone _).ι.app _) = _,
  apply quiver.hom.op_inj,
  simp [unop_ι_app], dsimp, simp,
  apply category.comp_id,
end

/-- The obvious map `pullback_cone f g → pushout_cocone f.op g.op` -/
@[simps (lemmas_only)]
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  pushout_cocone f.op g.op :=
(cocones.precompose (span_op f g).hom).obj
  (cocone.whisker walking_cospan_op_equiv.inverse (cone.op c))

@[simp] lemma op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  c.op.inl = c.fst.op :=
by { change (_ : limits.cocone _).ι.app _ = _, apply category.id_comp, }

@[simp] lemma op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  c.op.inr = c.snd.op :=
by { change (_ : limits.cocone _).ι.app _ = _, apply category.id_comp, }

/-- If `c` is a pullback cone, then `c.op.unop` is isomorphic to `c`. -/
def op_unop {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) : c.op.unop ≅ c :=
pullback_cone.ext (iso.refl _) (by simp) (by simp)

/-- If `c` is a pullback cone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unop_op {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) : c.unop.op ≅ c :=
pullback_cone.ext (iso.refl _) (by simp) (by simp)

end pullback_cone

namespace pushout_cocone

/-- If `c` is a pushout cocone, then `c.op.unop` is isomorphic to `c`. -/
def op_unop {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) : c.op.unop ≅ c :=
pushout_cocone.ext (iso.refl _) (by simp) (by simp)

/-- If `c` is a pushout cocone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unop_op {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) : c.unop.op ≅ c :=
pushout_cocone.ext (iso.refl _) (by simp) (by simp)

/-- A pushout cone is a colimit cocone if and only if the corresponding pullback cone
in the opposite category is a limit cone. -/
def is_colimit_equiv_is_limit_op  {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  is_colimit c ≃ is_limit c.op :=
begin
  apply equiv_of_subsingleton_of_subsingleton,
  { intro h,
    equiv_rw is_limit.postcompose_hom_equiv _ _,
    equiv_rw (is_limit.whisker_equivalence_equiv walking_span_op_equiv.symm).symm,
    exact is_limit_cocone_op _ h, },
  { intro h,
    equiv_rw is_colimit.equiv_iso_colimit c.op_unop.symm,
    apply is_colimit_cone_unop,
    equiv_rw is_limit.postcompose_hom_equiv _ _,
    equiv_rw (is_limit.whisker_equivalence_equiv _).symm,
    exact h, }
end

/-- A pushout cone is a colimit cocone in `Cᵒᵖ` if and only if the corresponding pullback cone
in `C` is a limit cone. -/
def is_colimit_equiv_is_limit_unop  {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z}
  (c : pushout_cocone f g) : is_colimit c ≃ is_limit c.unop :=
begin
  apply equiv_of_subsingleton_of_subsingleton,
  { intro h,
    apply is_limit_cocone_unop,
    equiv_rw is_colimit.precompose_hom_equiv _ _,
    equiv_rw (is_colimit.whisker_equivalence_equiv _).symm,
    exact h, },
  { intro h,
    equiv_rw is_colimit.equiv_iso_colimit c.unop_op.symm,
    equiv_rw is_colimit.precompose_hom_equiv _ _,
    equiv_rw (is_colimit.whisker_equivalence_equiv walking_cospan_op_equiv.symm).symm,
    exact is_colimit_cone_op _ h, },
end

end pushout_cocone

namespace pullback_cone

/-- A pullback cone is a limit cone if and only if the corresponding pushout cocone
in the opposite category is a colimit cocone. -/
def is_limit_equiv_is_colimit_op  {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  (c : pullback_cone f g) : is_limit c ≃ is_colimit c.op :=
(is_limit.equiv_iso_limit c.op_unop).symm.trans c.op.is_colimit_equiv_is_limit_unop.symm

/-- A pullback cone is a limit cone in `Cᵒᵖ` if and only if the corresponding pushout cocone
in `C` is a colimit cocone. -/
def is_limit_equiv_is_colimit_unop  {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z}
  (c : pullback_cone f g) : is_limit c ≃ is_colimit c.unop :=
(is_limit.equiv_iso_limit c.unop_op).symm.trans c.unop.is_colimit_equiv_is_limit_op.symm

end pullback_cone

section pullback

open opposite

/-- The pullback of `f` and `g` in `C` is isomorphic to the pushout of
`f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable
def pullback_iso_unop_pushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_pushout f.op g.op] : pullback f g ≅ unop (pushout f.op g.op) :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit _)
  ((pushout_cocone.is_colimit_equiv_is_limit_unop _) (colimit.is_colimit (span f.op g.op)))

@[simp, reassoc]
lemma pullback_iso_unop_pushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_pushout f.op g.op] :
  (pullback_iso_unop_pushout f g).inv ≫ pullback.fst =
    (pushout.inl : _ ⟶ pushout f.op g.op).unop :=
(is_limit.cone_point_unique_up_to_iso_inv_comp _ _ _).trans (by simp)

@[simp, reassoc]
lemma pullback_iso_unop_pushout_inv_snd {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) [has_pullback f g] [has_pushout f.op g.op] :
  (pullback_iso_unop_pushout f g).inv ≫ pullback.snd =
    (pushout.inr : _ ⟶ pushout f.op g.op).unop :=
(is_limit.cone_point_unique_up_to_iso_inv_comp _ _ _).trans (by simp)

@[simp, reassoc]
lemma pullback_iso_unop_pushout_hom_inl {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) [has_pullback f g] [has_pushout f.op g.op] :
  pushout.inl ≫ (pullback_iso_unop_pushout f g).hom.op = pullback.fst.op :=
begin
  apply quiver.hom.unop_inj,
  dsimp,
  rw [← pullback_iso_unop_pushout_inv_fst, iso.hom_inv_id_assoc],
end

@[simp, reassoc]
lemma pullback_iso_unop_pushout_hom_inr {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) [has_pullback f g] [has_pushout f.op g.op] :
  pushout.inr ≫ (pullback_iso_unop_pushout f g).hom.op = pullback.snd.op :=
begin
  apply quiver.hom.unop_inj,
  dsimp,
  rw [← pullback_iso_unop_pushout_inv_snd, iso.hom_inv_id_assoc],
end

end pullback

section pushout

/-- The pushout of `f` and `g` in `C` is isomorphic to the pullback of
 `f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable
def pushout_iso_unop_pullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] : pushout f g ≅ unop (pullback f.op g.op) :=
is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
  ((pullback_cone.is_limit_equiv_is_colimit_unop _) (limit.is_limit (cospan f.op g.op)))
.
@[simp, reassoc]
lemma pushout_iso_unop_pullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  pushout.inl ≫ (pushout_iso_unop_pullback f g).hom =
    (pullback.fst : pullback f.op g.op ⟶ _).unop :=
(is_colimit.comp_cocone_point_unique_up_to_iso_hom _ _ _).trans (by simp)

@[simp, reassoc]
lemma pushout_iso_unop_pullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  pushout.inr ≫ (pushout_iso_unop_pullback f g).hom =
    (pullback.snd : pullback f.op g.op ⟶ _).unop :=
(is_colimit.comp_cocone_point_unique_up_to_iso_hom _ _ _).trans (by simp)

@[simp]
lemma pushout_iso_unop_pullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  (pushout_iso_unop_pullback f g).inv.op ≫ pullback.fst = pushout.inl.op :=
begin
  apply quiver.hom.unop_inj,
  dsimp,
  rw [← pushout_iso_unop_pullback_inl_hom, category.assoc, iso.hom_inv_id, category.comp_id],
end

@[simp]
lemma pushout_iso_unop_pullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  (pushout_iso_unop_pullback f g).inv.op ≫ pullback.snd = pushout.inr.op :=
begin
  apply quiver.hom.unop_inj,
  dsimp,
  rw [← pushout_iso_unop_pullback_inr_hom, category.assoc, iso.hom_inv_id, category.comp_id],
end

end pushout

end category_theory.limits
