/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import topology.sheaves.sheaf_condition.sites
import category_theory.limits.preserves.basic
import category_theory.category.pairwise
import category_theory.limits.constructions.binary_products

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`
-/

noncomputable theory

universes v u

open topological_space
open Top
open opposite
open category_theory
open category_theory.limits

namespace Top.presheaf

variables {X : Top.{v}}

variables {C : Type u} [category.{v} C]

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_pairwise_intersections`).

A presheaf is a sheaf if `F` sends the cone `(pairwise.cocone U).op` to a limit cone.
(Recall `pairwise.cocone U` has cone point `supr U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
def is_sheaf_pairwise_intersections (F : presheaf C X) : Prop :=
∀ ⦃ι : Type v⦄ (U : ι → opens X), nonempty (is_limit (F.map_cone (pairwise.cocone U).op))

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections`).

A presheaf is a sheaf if `F` preserves the limit of `pairwise.diagram U`.
(Recall `pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `supr U`.)
-/
def is_sheaf_preserves_limit_pairwise_intersections (F : presheaf C X) : Prop :=
∀ ⦃ι : Type v⦄ (U : ι → opens X), nonempty (preserves_limit (pairwise.diagram U).op F)

/-!
The remainder of this file shows that these conditions are equivalent
to the usual sheaf condition.
-/

variables [has_products C]

namespace sheaf_condition_pairwise_intersections

open category_theory.pairwise category_theory.pairwise.hom
open sheaf_condition_equalizer_products

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_functor_obj (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) (c : limits.cone ((diagram U).op ⋙ F)) :
  limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
{ X := c.X,
  π :=
  { app := λ Z,
      walking_parallel_pair.cases_on Z
        (pi.lift (λ (i : ι), c.π.app (op (single i))))
        (pi.lift (λ (b : ι × ι), c.π.app (op (pair b.1 b.2)))),
    naturality' := λ Y Z f,
    begin
      cases Y; cases Z; cases f,
      { ext i, dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app, category_theory.functor.map_id,
          category.assoc],
        dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app], },
      { ext ⟨i, j⟩, dsimp [sheaf_condition_equalizer_products.left_res],
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
          category.assoc],
        have h := c.π.naturality (quiver.hom.op (hom.left i j)),
        dsimp at h,
        simpa using h, },
      { ext ⟨i, j⟩, dsimp [sheaf_condition_equalizer_products.right_res],
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
          category.assoc],
        have h := c.π.naturality (quiver.hom.op (hom.right i j)),
        dsimp at h,
        simpa using h, },
      { ext i, dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app, category_theory.functor.map_id,
          category.assoc],
        dsimp,
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app], },
    end, }, }

section
local attribute [tidy] tactic.case_bash

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_functor (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) :
  limits.cone ((diagram U).op ⋙ F) ⥤
    limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
{ obj := λ c, cone_equiv_functor_obj F U c,
  map := λ c c' f,
  { hom := f.hom,
    w' := λ j, begin
      cases j;
      { ext, simp only [limits.fan.mk_π_app, limits.cone_morphism.w,
        limits.limit.lift_π, category.assoc, cone_equiv_functor_obj_π_app], },
    end }, }.

end

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_inverse_obj (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X)
  (c : limits.cone (sheaf_condition_equalizer_products.diagram F U)) :
  limits.cone ((diagram U).op ⋙ F) :=
{ X := c.X,
  π :=
  { app :=
    begin
      intro x,
      induction x using opposite.rec,
      rcases x with (⟨i⟩|⟨i,j⟩),
      { exact c.π.app (walking_parallel_pair.zero) ≫ pi.π _ i, },
      { exact c.π.app (walking_parallel_pair.one) ≫ pi.π _ (i, j), }
    end,
    naturality' :=
    begin
      intros x y f,
      induction x using opposite.rec,
      induction y using opposite.rec,
      have ef : f = f.unop.op := rfl,
      revert ef,
      generalize : f.unop = f',
      rintro rfl,
      rcases x with ⟨i⟩|⟨⟩; rcases y with ⟨⟩|⟨j,j⟩; rcases f' with ⟨⟩,
      { dsimp, erw [F.map_id], simp, },
      { dsimp, simp only [category.id_comp, category.assoc],
        have h := c.π.naturality (walking_parallel_pair_hom.left),
        dsimp [sheaf_condition_equalizer_products.left_res] at h,
        simp only [category.id_comp] at h,
        have h' := h =≫ pi.π _ (i, j),
        rw h',
        simp,
        refl, },
      { dsimp, simp only [category.id_comp, category.assoc],
        have h := c.π.naturality (walking_parallel_pair_hom.right),
        dsimp [sheaf_condition_equalizer_products.right_res] at h,
        simp only [category.id_comp] at h,
        have h' := h =≫ pi.π _ (j, i),
        rw h',
        simp,
        refl, },
      { dsimp, erw [F.map_id], simp, },
    end, }, }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_inverse (F : presheaf C X)
  ⦃ι : Type v⦄ (U : ι → opens ↥X) :
  limits.cone (sheaf_condition_equalizer_products.diagram F U) ⥤
    limits.cone ((diagram U).op ⋙ F) :=
{ obj := λ c, cone_equiv_inverse_obj F U c,
  map := λ c c' f,
  { hom := f.hom,
    w' :=
    begin
      intro x,
      induction x using opposite.rec,
      rcases x with (⟨i⟩|⟨i,j⟩),
      { dsimp,
        rw [←(f.w walking_parallel_pair.zero), category.assoc], },
      { dsimp,
        rw [←(f.w walking_parallel_pair.one), category.assoc], },
    end }, }.

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_unit_iso_app (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens ↥X)
  (c : cone ((diagram U).op ⋙ F)) :
  (𝟭 (cone ((diagram U).op ⋙ F))).obj c ≅
    (cone_equiv_functor F U ⋙ cone_equiv_inverse F U).obj c :=
{ hom :=
  { hom := 𝟙 _,
    w' := λ j, begin
      induction j using opposite.rec, rcases j;
      { dsimp, simp only [limits.fan.mk_π_app, category.id_comp, limits.limit.lift_π], }
    end, },
  inv :=
  { hom := 𝟙 _,
    w' := λ j, begin
      induction j using opposite.rec, rcases j;
      { dsimp, simp only [limits.fan.mk_π_app, category.id_comp, limits.limit.lift_π], }
    end },
  hom_inv_id' := begin
    ext,
    simp only [category.comp_id, limits.cone.category_comp_hom, limits.cone.category_id_hom],
  end,
  inv_hom_id' := begin
    ext,
    simp only [category.comp_id, limits.cone.category_comp_hom, limits.cone.category_id_hom],
  end, }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_unit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  𝟭 (limits.cone ((diagram U).op ⋙ F)) ≅
    cone_equiv_functor F U ⋙ cone_equiv_inverse F U :=
nat_iso.of_components (cone_equiv_unit_iso_app F U) (by tidy)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_counit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  cone_equiv_inverse F U ⋙ cone_equiv_functor F U ≅
    𝟭 (limits.cone (sheaf_condition_equalizer_products.diagram F U)) :=
nat_iso.of_components (λ c,
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
      { ext ⟨i,j⟩, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
      { ext ⟨i,j⟩, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
    end, },
  hom_inv_id' := by { ext, dsimp, simp only [category.comp_id], },
  inv_hom_id' := by { ext, dsimp, simp only [category.comp_id], }, })
(λ c d f, by { ext, dsimp, simp only [category.comp_id, category.id_comp], })

/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def cone_equiv (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  limits.cone ((diagram U).op ⋙ F) ≌ limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
{ functor := cone_equiv_functor F U,
  inverse := cone_equiv_inverse F U,
  unit_iso := cone_equiv_unit_iso F U,
  counit_iso := cone_equiv_counit_iso F U, }

local attribute [reducible]
  sheaf_condition_equalizer_products.res
  sheaf_condition_equalizer_products.left_res

/--
If `sheaf_condition_equalizer_products.fork` is an equalizer,
then `F.map_cone (cone U)` is a limit cone.
-/
def is_limit_map_cone_of_is_limit_sheaf_condition_fork
  (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (P : is_limit (sheaf_condition_equalizer_products.fork F U)) :
  is_limit (F.map_cone (cocone U).op) :=
is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U).symm).symm P)
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      intro x,
      induction x using opposite.rec,
      rcases x with ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
          category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      intro x,
      induction x using opposite.rec,
      rcases x with ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
          category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  hom_inv_id' := by { ext, dsimp, simp only [category.comp_id], },
  inv_hom_id' := by { ext, dsimp, simp only [category.comp_id], }, }

/--
If `F.map_cone (cone U)` is a limit cone,
then `sheaf_condition_equalizer_products.fork` is an equalizer.
-/
def is_limit_sheaf_condition_fork_of_is_limit_map_cone
  (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (Q : is_limit (F.map_cone (cocone U).op)) :
  is_limit (sheaf_condition_equalizer_products.fork F U) :=
is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U)).symm Q)
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp, ext ⟨i, j⟩,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
          category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨⟩,
      { dsimp, simp, refl, },
      { dsimp, ext ⟨i, j⟩,
        simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
          category.assoc],
        rw ←F.map_comp,
        refl, }
    end },
  hom_inv_id' := by { ext, dsimp, simp only [category.comp_id], },
  inv_hom_id' := by { ext, dsimp, simp only [category.comp_id], }, }


end sheaf_condition_pairwise_intersections

open sheaf_condition_pairwise_intersections

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
lemma is_sheaf_iff_is_sheaf_pairwise_intersections (F : presheaf C X) :
  F.is_sheaf ↔ F.is_sheaf_pairwise_intersections :=
iff.intro (λ h ι U, ⟨is_limit_map_cone_of_is_limit_sheaf_condition_fork F U (h U).some⟩)
  (λ h ι U, ⟨is_limit_sheaf_condition_fork_of_is_limit_map_cone F U (h U).some⟩)

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
lemma is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections (F : presheaf C X) :
  F.is_sheaf ↔ F.is_sheaf_preserves_limit_pairwise_intersections :=
begin
  rw is_sheaf_iff_is_sheaf_pairwise_intersections,
  split,
  { intros h ι U,
    exact ⟨preserves_limit_of_preserves_limit_cone (pairwise.cocone_is_colimit U).op (h U).some⟩ },
  { intros h ι U,
    haveI := (h U).some,
    exact ⟨preserves_limit.preserves (pairwise.cocone_is_colimit U).op⟩ }
end

end Top.presheaf

namespace Top.sheaf

variables {X : Top.{v}} {C : Type u} [category.{v} C] [has_products C]
variables (F : X.sheaf C) (U V : opens X)
open category_theory.limits

/-- For a sheaf `F`, `F(U ∪ V)` is the pullback of `F(U) ⟶ F(U ∩ V)` and `F(V) ⟶ F(U ∩ V)`.
This is the pullback cone. -/
def inter_union_pullback_cone : pullback_cone
  (F.1.map (hom_of_le inf_le_left : U ∩ V ⟶ _).op) (F.1.map (hom_of_le inf_le_right).op) :=
pullback_cone.mk (F.1.map (hom_of_le le_sup_left).op) (F.1.map (hom_of_le le_sup_right).op)
  (by { rw [← F.1.map_comp, ← F.1.map_comp], congr })

@[simp] lemma inter_union_pullback_cone_X :
  (inter_union_pullback_cone F U V).X = F.1.obj (op $ U ∪ V) := rfl
@[simp] lemma inter_union_pullback_cone_fst :
  (inter_union_pullback_cone F U V).fst = F.1.map (hom_of_le le_sup_left).op := rfl
@[simp] lemma inter_union_pullback_cone_snd :
  (inter_union_pullback_cone F U V).snd = F.1.map (hom_of_le le_sup_right).op := rfl

variable (s : pullback_cone
  (F.1.map (hom_of_le inf_le_left : U ∩ V ⟶ _).op) (F.1.map (hom_of_le inf_le_right).op))

/-- (Implementation).
Every cone over `F(U) ⟶ F(U ∩ V)` and `F(V) ⟶ F(U ∩ V)` factors through `F(U ∪ V)`. -/
def inter_union_pullback_cone_lift : s.X ⟶ F.1.obj (op (U ∪ V)) :=
begin
  let ι : walking_pair → opens X := λ j, walking_pair.cases_on j U V,
  have hι : U ∪ V = supr ι,
  { ext, split,
    { rintros (h|h),
    exacts [⟨_,⟨_,⟨walking_pair.left,rfl⟩,rfl⟩,h⟩, ⟨_,⟨_,⟨walking_pair.right,rfl⟩,rfl⟩,h⟩] },
    { rintros ⟨_,⟨_,⟨⟨⟩,⟨⟩⟩,⟨⟩⟩,z⟩, exacts [or.inl z, or.inr z] } },
  refine (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.lift
    ⟨s.X, { app := _, naturality' := _ }⟩ ≫ F.1.map (eq_to_hom hι).op,
  { apply opposite.rec,
    rintro ((_|_)|(_|_)),
    exacts [s.fst, s.snd, s.fst ≫ F.1.map (hom_of_le inf_le_left).op,
      s.snd ≫ F.1.map (hom_of_le inf_le_left).op] },
  rintros i j f,
  induction i using opposite.rec,
  induction j using opposite.rec,
  let g : j ⟶ i := f.unop, have : f = g.op := rfl, clear_value g, subst this,
  rcases i with ((_|_)|(_|_)); rcases j with ((_|_)|(_|_)); rcases g; dsimp;
    simp only [category.id_comp, s.condition, category_theory.functor.map_id, category.comp_id],
  { rw [← cancel_mono (F.1.map (eq_to_hom $ inf_comm : U ∩ V ⟶ _).op), category.assoc,
      category.assoc],
    erw [← F.1.map_comp, ← F.1.map_comp],
    convert s.condition.symm },
  { convert s.condition }
end

lemma inter_union_pullback_cone_lift_left :
  inter_union_pullback_cone_lift F U V s ≫ F.1.map (hom_of_le le_sup_left).op = s.fst :=
begin
  erw [category.assoc, ←F.1.map_comp],
  exact (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
    (op $ pairwise.single walking_pair.left)
end

lemma inter_union_pullback_cone_lift_right :
  inter_union_pullback_cone_lift F U V s ≫ F.1.map (hom_of_le le_sup_right).op = s.snd :=
begin
  erw [category.assoc, ←F.1.map_comp],
  exact (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
    (op $ pairwise.single walking_pair.right)
end

/-- For a sheaf `F`, `F(U ∪ V)` is the pullback of `F(U) ⟶ F(U ∩ V)` and `F(V) ⟶ F(U ∩ V)`. -/
def is_limit_pullback_cone : is_limit (inter_union_pullback_cone F U V) :=
begin
  let ι : walking_pair → opens X := λ j, walking_pair.cases_on j U V,
  have hι : U ∪ V = supr ι,
  { ext, split,
    { rintros (h|h),
    exacts [⟨_,⟨_,⟨walking_pair.left,rfl⟩,rfl⟩,h⟩, ⟨_,⟨_,⟨walking_pair.right,rfl⟩,rfl⟩,h⟩] },
    { rintros ⟨_,⟨_,⟨⟨⟩,⟨⟩⟩,⟨⟩⟩,z⟩, exacts [or.inl z, or.inr z] } },
  apply pullback_cone.is_limit_aux',
  intro s,
  use inter_union_pullback_cone_lift F U V s,
  refine ⟨_,_,_⟩,
  { apply inter_union_pullback_cone_lift_left },
  { apply inter_union_pullback_cone_lift_right },
  { intros m h₁ h₂,
    rw ← cancel_mono (F.1.map (eq_to_hom hι.symm).op),
    apply (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.hom_ext,
    apply opposite.rec,
    rintro ((_|_)|(_|_)); rw [category.assoc, category.assoc],
    { erw ← F.1.map_comp,
      convert h₁,
      apply inter_union_pullback_cone_lift_left },
    { erw ← F.1.map_comp,
      convert h₂,
      apply inter_union_pullback_cone_lift_right },
    all_goals
    { dsimp only [functor.op, pairwise.cocone_ι_app, functor.map_cone_π_app,
        cocone.op, pairwise.cocone_ι_app_2, unop_op, op_comp, nat_trans.op],
      simp_rw [F.1.map_comp, ← category.assoc],
      congr' 1,
      simp_rw [category.assoc, ← F.1.map_comp] },
    { convert h₁,
      apply inter_union_pullback_cone_lift_left },
    { convert h₂,
      apply inter_union_pullback_cone_lift_right } }
end

/-- If `U, V` are disjoint, then `F(U ∪ V) = F(U) × F(V)`. -/
def is_product_of_disjoint (h : U ∩ V = ⊥) : is_limit
    (binary_fan.mk (F.1.map (hom_of_le le_sup_left : _ ⟶ U ⊔ V).op)
      (F.1.map (hom_of_le le_sup_right : _ ⟶ U ⊔ V).op)) :=
is_product_of_is_terminal_is_pullback _ _ _ _
  (F.is_terminal_of_eq_empty h) (is_limit_pullback_cone F U V)

end Top.sheaf
