/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.products
import topology.sheaves.sheaf_condition.pairwise_intersections

/-!
# The sheaf condition in terms of an equalizer of products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ F.obj (U i)` and `∏ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the `pairwise_intersections` sheaf condition when
the presheaf is valued in a category with products, and thereby equivalent to the default sheaf
condition.
-/

universes v' v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_products.{v'} C]
variables {X : Top.{v'}} (F : presheaf C X) {ι : Type v'} (U : ι → opens X)

namespace presheaf

namespace sheaf_condition_equalizer_products

/-- The product of the sections of a presheaf over a family of open sets. -/
def pi_opens : C := ∏ (λ i : ι, F.obj (op (U i)))
/--
The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def pi_inters : C := ∏ (λ p : ι × ι, F.obj (op (U p.1 ⊓ U p.2)))

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def left_res : pi_opens F U ⟶ pi_inters.{v'} F U :=
pi.lift (λ p : ι × ι, pi.π _ p.1 ≫ F.map (inf_le_left (U p.1) (U p.2)).op)

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def right_res : pi_opens F U ⟶ pi_inters.{v'} F U :=
pi.lift (λ p : ι × ι, pi.π _ p.2 ≫ F.map (inf_le_right (U p.1) (U p.2)).op)

/--
The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (supr U)) ⟶ pi_opens.{v'} F U :=
pi.lift (λ i : ι, F.map (topological_space.opens.le_supr U i).op)

@[simp, elementwise]
lemma res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (opens.le_supr U i).op :=
by rw [res, limit.lift_π, fan.mk_π_app]

@[elementwise]
lemma w : res F U ≫ left_res F U = res F U ≫ right_res F U :=
begin
  dsimp [res, left_res, right_res],
  ext,
  simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
  rw [←F.map_comp],
  rw [←F.map_comp],
  congr,
end

/--
The equalizer diagram for the sheaf condition.
-/
@[reducible]
def diagram : walking_parallel_pair ⥤ C :=
parallel_pair (left_res.{v'} F U) (right_res F U)

/--
The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : fork.{v} (left_res F U) (right_res F U) := fork.of_ι _ (w F U)

@[simp]
lemma fork_X : (fork F U).X = F.obj (op (supr U)) := rfl

@[simp]
lemma fork_ι : (fork F U).ι = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_zero :
  (fork F U).π.app walking_parallel_pair.zero = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_one :
  (fork F U).π.app walking_parallel_pair.one = res F U ≫ left_res F U := rfl

variables {F} {G : presheaf C X}

/-- Isomorphic presheaves have isomorphic `pi_opens` for any cover `U`. -/
@[simp]
def pi_opens.iso_of_iso (α : F ≅ G) : pi_opens F U ≅ pi_opens.{v'} G U :=
pi.map_iso (λ X, α.app _)

/-- Isomorphic presheaves have isomorphic `pi_inters` for any cover `U`. -/
@[simp]
def pi_inters.iso_of_iso (α : F ≅ G) : pi_inters F U ≅ pi_inters.{v'} G U :=
pi.map_iso (λ X, α.app _)

/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
def diagram.iso_of_iso (α : F ≅ G) : diagram F U ≅ diagram.{v'} G U :=
nat_iso.of_components
  begin rintro ⟨⟩, exact pi_opens.iso_of_iso U α, exact pi_inters.iso_of_iso U α end
  begin
    rintro ⟨⟩ ⟨⟩ ⟨⟩,
    { simp, },
    { ext, simp [left_res], },
    { ext, simp [right_res], },
    { simp, },
  end.

/--
If `F G : presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
def fork.iso_of_iso (α : F ≅ G) :
  fork F U ≅ (cones.postcompose (diagram.iso_of_iso U α).inv).obj (fork G U) :=
begin
  fapply fork.ext,
  { apply α.app, },
  { ext,
    dunfold fork.ι, -- Ugh, `simp` can't unfold abbreviations.
    simp [res, diagram.iso_of_iso], }
end

end sheaf_condition_equalizer_products

/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def is_sheaf_equalizer_products (F : presheaf.{v' v u} C X) : Prop :=
∀ ⦃ι : Type v'⦄ (U : ι → opens X), nonempty (is_limit (sheaf_condition_equalizer_products.fork F U))

/-!
The remainder of this file shows that the equalizer_products sheaf condition is equivalent
to the pariwise_intersections sheaf condition.
-/

namespace sheaf_condition_pairwise_intersections

open category_theory.pairwise category_theory.pairwise.hom

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_functor_obj (c : cone ((diagram U).op ⋙ F)) :
  cone (sheaf_condition_equalizer_products.diagram F U) :=
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
def cone_equiv_functor :
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
def cone_equiv_inverse_obj
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
        simp only [category.assoc, limit.lift_π, fan.mk_π_app],
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
def cone_equiv_inverse :
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
        dunfold fork.ι,
        rw [←(f.w walking_parallel_pair.zero), category.assoc], },
      { dsimp,
        rw [←(f.w walking_parallel_pair.one), category.assoc], },
    end }, }.

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_unit_iso_app
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
def cone_equiv_unit_iso :
  𝟭 (limits.cone ((diagram U).op ⋙ F)) ≅
    cone_equiv_functor F U ⋙ cone_equiv_inverse F U :=
nat_iso.of_components (cone_equiv_unit_iso_app F U) (by tidy)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_counit_iso :
  cone_equiv_inverse F U ⋙ cone_equiv_functor F U ≅
    𝟭 (limits.cone (sheaf_condition_equalizer_products.diagram F U)) :=
nat_iso.of_components (λ c,
{ hom :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext ⟨j⟩, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
      { ext ⟨i,j⟩, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
    end },
  inv :=
  { hom := 𝟙 _,
    w' :=
    begin
      rintro ⟨_|_⟩,
      { ext ⟨j⟩, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
      { ext ⟨i,j⟩, dsimp, simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π], },
    end, },
  hom_inv_id' := by { ext, dsimp, simp only [category.comp_id], },
  inv_hom_id' := by { ext, dsimp, simp only [category.comp_id], }, })
(λ c d f, by { ext, dsimp, simp only [category.comp_id, category.id_comp], })

/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def cone_equiv :
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
to the default sheaf condition.
-/
lemma is_sheaf_iff_is_sheaf_equalizer_products (F : presheaf C X) :
  F.is_sheaf ↔ F.is_sheaf_equalizer_products :=
(is_sheaf_iff_is_sheaf_pairwise_intersections F).trans $
iff.intro (λ h ι U, ⟨is_limit_sheaf_condition_fork_of_is_limit_map_cone F U (h U).some⟩)
  (λ h ι U, ⟨is_limit_map_cone_of_is_limit_sheaf_condition_fork F U (h U).some⟩)

end presheaf

end Top
