/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.limits.preserves.shapes.pullbacks
import category_theory.limits.preserves.shapes.binary_products

/-!
# Constructing equalizers from pullbacks and binary products.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If a category has pullbacks and binary products, then it has equalizers.

TODO: generalize universe
-/

noncomputable theory

universes v v' u u'

open category_theory category_theory.category

namespace category_theory.limits

variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v'} D] (G : C ⥤ D)

-- We hide the "implementation details" inside a namespace
namespace has_equalizers_of_has_pullbacks_and_binary_products

variables [has_binary_products C] [has_pullbacks C]

/-- Define the equalizing object -/
@[reducible]
def construct_equalizer (F : walking_parallel_pair ⥤ C) : C :=
pullback (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.left))
         (prod.lift (𝟙 _) (F.map walking_parallel_pair_hom.right))

/-- Define the equalizing morphism -/
abbreviation pullback_fst (F : walking_parallel_pair ⥤ C) :
  construct_equalizer F ⟶ F.obj walking_parallel_pair.zero :=
pullback.fst

lemma pullback_fst_eq_pullback_snd (F : walking_parallel_pair ⥤ C) :
  pullback_fst F = pullback.snd :=
by convert pullback.condition =≫ limits.prod.fst; simp

/-- Define the equalizing cone -/
@[reducible]
def equalizer_cone (F : walking_parallel_pair ⥤ C) : cone F :=
cone.of_fork
  (fork.of_ι (pullback_fst F)
    (begin
      conv_rhs { rw pullback_fst_eq_pullback_snd, },
      convert pullback.condition =≫ limits.prod.snd using 1; simp
     end))

/-- Show the equalizing cone is a limit -/
def equalizer_cone_is_limit (F : walking_parallel_pair ⥤ C) : is_limit (equalizer_cone F) :=
{ lift :=
  begin
    intro c, apply pullback.lift (c.π.app _) (c.π.app _),
    apply limit.hom_ext,
    rintro (_ | _); simp
  end,
  fac' := by rintros c (_ | _); simp,
  uniq' :=
  begin
    intros c _ J,
    have J0 := J walking_parallel_pair.zero, simp at J0,
    apply pullback.hom_ext,
    { rwa limit.lift_π },
    { erw [limit.lift_π, ← J0, pullback_fst_eq_pullback_snd] }
  end }

end has_equalizers_of_has_pullbacks_and_binary_products

open has_equalizers_of_has_pullbacks_and_binary_products
/-- Any category with pullbacks and binary products, has equalizers. -/
-- This is not an instance, as it is not always how one wants to construct equalizers!
lemma has_equalizers_of_has_pullbacks_and_binary_products
  [has_binary_products C] [has_pullbacks C] :
  has_equalizers C :=
{ has_limit := λ F, has_limit.mk
  { cone := equalizer_cone F,
    is_limit := equalizer_cone_is_limit F } }

local attribute[instance] has_pullback_of_preserves_pullback

/-- A functor that preserves pullbacks and binary products also presrves equalizers. -/
def preserves_equalizers_of_preserves_pullbacks_and_binary_products
    [has_binary_products C] [has_pullbacks C]
    [preserves_limits_of_shape (discrete walking_pair) G]
    [preserves_limits_of_shape walking_cospan G] :
  preserves_limits_of_shape walking_parallel_pair G :=
⟨λ K, preserves_limit_of_preserves_limit_cone (equalizer_cone_is_limit K) $
{ lift := λ c, begin
    refine pullback.lift _ _ _ ≫ (@@preserves_pullback.iso _ _ _ _ _ _ _ _).inv,
    { exact c.π.app walking_parallel_pair.zero },
    { exact c.π.app walking_parallel_pair.zero },
    apply (map_is_limit_of_preserves_of_is_limit G _ _ (prod_is_prod _ _)).hom_ext,
    swap, apply_instance,
    rintro (_|_),
    { simp only [category.assoc, ← G.map_comp, prod.lift_fst,
        binary_fan.π_app_left, binary_fan.mk_fst], },
    { simp only [binary_fan.π_app_right, binary_fan.mk_snd,
        category.assoc, ← G.map_comp, prod.lift_snd],
      exact (c.π.naturality (walking_parallel_pair_hom.left)).symm.trans
        (c.π.naturality (walking_parallel_pair_hom.right)) },
  end,
  fac' := λ c j, begin
    rcases j with (_|_);
      simp only [category.comp_id, preserves_pullback.iso_inv_fst, cone.of_fork_π, G.map_comp,
        preserves_pullback.iso_inv_fst_assoc, functor.map_cone_π_app, eq_to_hom_refl,
        category.assoc, fork.of_ι_π_app, pullback.lift_fst, pullback.lift_fst_assoc],
      exact (c.π.naturality (walking_parallel_pair_hom.left)).symm.trans (category.id_comp _)
  end,
  uniq' := λ s m h, begin
    rw iso.eq_comp_inv,
    have := h walking_parallel_pair.zero,
    dsimp [equalizer_cone] at this,
    ext; simp only [preserves_pullback.iso_hom_snd,
      category.assoc, preserves_pullback.iso_hom_fst, pullback.lift_fst, pullback.lift_snd,
      category.comp_id, ← pullback_fst_eq_pullback_snd, ← this],
  end }⟩


-- We hide the "implementation details" inside a namespace
namespace has_coequalizers_of_has_pushouts_and_binary_coproducts

variables [has_binary_coproducts C] [has_pushouts C]

/-- Define the equalizing object -/
@[reducible]
def construct_coequalizer (F : walking_parallel_pair ⥤ C) : C :=
pushout (coprod.desc (𝟙 _) (F.map walking_parallel_pair_hom.left))
        (coprod.desc (𝟙 _) (F.map walking_parallel_pair_hom.right))

/-- Define the equalizing morphism -/
abbreviation pushout_inl (F : walking_parallel_pair ⥤ C) :
  F.obj walking_parallel_pair.one ⟶ construct_coequalizer F :=
pushout.inl

lemma pushout_inl_eq_pushout_inr (F : walking_parallel_pair ⥤ C) :
  pushout_inl F = pushout.inr :=
by convert limits.coprod.inl ≫= pushout.condition; simp

/-- Define the equalizing cocone -/
@[reducible]
def coequalizer_cocone (F : walking_parallel_pair ⥤ C) : cocone F :=
cocone.of_cofork
  (cofork.of_π (pushout_inl F)
    (begin
      conv_rhs { rw pushout_inl_eq_pushout_inr, },
      convert limits.coprod.inr ≫= pushout.condition using 1; simp
     end))

/-- Show the equalizing cocone is a colimit -/
def coequalizer_cocone_is_colimit (F : walking_parallel_pair ⥤ C) :
  is_colimit (coequalizer_cocone F) :=
{ desc :=
  begin
    intro c, apply pushout.desc (c.ι.app _) (c.ι.app _),
    apply colimit.hom_ext,
    rintro (_ | _); simp
  end,
  fac' := by rintros c (_ | _); simp,
  uniq' :=
  begin
    intros c _ J,
    have J1 : pushout_inl F ≫ m = c.ι.app walking_parallel_pair.one :=
      by simpa using J walking_parallel_pair.one,
    apply pushout.hom_ext,
    { rw colimit.ι_desc, exact J1 },
    { rw [colimit.ι_desc, ← pushout_inl_eq_pushout_inr], exact J1 }
  end }

end has_coequalizers_of_has_pushouts_and_binary_coproducts

open has_coequalizers_of_has_pushouts_and_binary_coproducts
/-- Any category with pullbacks and binary products, has equalizers. -/
-- This is not an instance, as it is not always how one wants to construct equalizers!
lemma has_coequalizers_of_has_pushouts_and_binary_coproducts
  [has_binary_coproducts C] [has_pushouts C] : has_coequalizers C :=
{ has_colimit := λ F, has_colimit.mk
  { cocone := coequalizer_cocone F,
    is_colimit := coequalizer_cocone_is_colimit F } }

local attribute[instance] has_pushout_of_preserves_pushout

/-- A functor that preserves pushouts and binary coproducts also presrves coequalizers. -/
def preserves_coequalizers_of_preserves_pushouts_and_binary_coproducts
    [has_binary_coproducts C] [has_pushouts C]
    [preserves_colimits_of_shape (discrete walking_pair) G]
    [preserves_colimits_of_shape walking_span G] :
  preserves_colimits_of_shape walking_parallel_pair G :=
⟨λ K, preserves_colimit_of_preserves_colimit_cocone (coequalizer_cocone_is_colimit K) $
{ desc := λ c, begin
    refine (@@preserves_pushout.iso _ _ _ _ _ _ _ _).inv ≫ pushout.desc _ _ _,
    { exact c.ι.app walking_parallel_pair.one },
    { exact c.ι.app walking_parallel_pair.one },
    apply (map_is_colimit_of_preserves_of_is_colimit G _ _ (coprod_is_coprod _ _)).hom_ext,
    swap, apply_instance,
    rintro (_|_),
    { simp only [binary_cofan.ι_app_left, binary_cofan.mk_inl, category.assoc, ← G.map_comp_assoc,
        coprod.inl_desc] },
    { simp only [binary_cofan.ι_app_right, binary_cofan.mk_inr, category.assoc, ← G.map_comp_assoc,
        coprod.inr_desc],
      exact (c.ι.naturality walking_parallel_pair_hom.left).trans
        (c.ι.naturality walking_parallel_pair_hom.right).symm, },
  end,
  fac' := λ c j, begin
    rcases j with (_|_); simp only [functor.map_cocone_ι_app, cocone.of_cofork_ι, category.id_comp,
      eq_to_hom_refl, category.assoc, functor.map_comp, cofork.of_π_ι_app, pushout.inl_desc,
      preserves_pushout.inl_iso_inv_assoc],
      exact (c.ι.naturality (walking_parallel_pair_hom.left)).trans (category.comp_id _)
  end,
  uniq' := λ s m h, begin
    rw iso.eq_inv_comp,
    have := h walking_parallel_pair.one,
    dsimp [coequalizer_cocone] at this,
    ext; simp only [preserves_pushout.inl_iso_hom_assoc, category.id_comp, pushout.inl_desc,
      pushout.inr_desc, preserves_pushout.inr_iso_hom_assoc,
      ← pushout_inl_eq_pushout_inr, ← this],
  end }⟩


end category_theory.limits
